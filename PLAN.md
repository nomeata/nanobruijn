# nanobruijn

Forked from [nanoda_lib](https://github.com/ammkrn/nanoda_lib) (Rust Lean 4 type checker).

**Goal**: Replace locally-nameless binding with pure de Bruijn indices + shift-homomorphic
caching. Avoid the expensive substitution on binder entry while retaining cross-depth
cache hits via shift-invariant keys.

**Principle**: Performance comparisons should reflect the design differences, not
low-level tuning. Optimizations that could equally be applied to nanoda (e.g. parsing
tricks, SIMD, micro-benchmarking tweaks) are out of scope. Only optimizations that arise
from or interact with the de Bruijn + shift-homomorphic design are interesting.

## Design (changes from vanilla nanoda)

### Pure de Bruijn (no locally nameless)

Vanilla nanoda substitutes `bvar(0)` with a fresh fvar on binder entry (full traversal).
We use a local context array with `push_local`/`pop_local` (zero allocation).

- `inst` split into `inst` (no shift-down) and `inst_beta` (shift-down for beta/let/Pi)
- `inst_aux` shifts substitution values under binders via `mk_shift(val, offset)`
- `lookup_var` retrieves types from `local_ctx[depth - 1 - idx]` and shifts to current depth
- `inductive.rs`/`quot.rs` still use old Local approach (works correctly)

### ExprPtr: Shift-in-pointer (replacing Shift DAG nodes)

No `Shift` variant in the Expr enum. Instead, `ExprPtr = (CorePtr, u16)` carries the
shift inline. The DAG only stores core expressions (indexed by `CorePtr`).
`ExprPtr(p, k)` represents `shift(dag[p], k, 0)`.

- `ExprPtr::CLOSED_SHIFT = u16::MAX`: Sentinel for closed expressions (nlbv=0). Acts as
  +infinity in min calculations. Strict invariant: shift=0 means OPEN at depth 0,
  CLOSED_SHIFT means closed. Enforced by `osnf_adj` (panics on violation).
- `ExprPtr::closed(core)`, `ExprPtr::unshifted(core)`, `ExprPtr::new(core, k)`,
  `ExprPtr::from_nlbv(core, nlbv)`: constructors for different cases. `from_nlbv`
  checks nlbv to pick closed vs open. `unshifted` is only for verified-open expressions.
- `e.shift_up(amount)`: O(1) shift composition. No-op for closed (is_closed() check).
- `e.adjust_depth(from, to)`: depth-aware shift adjustment for UF and cache operations.
  Handles closed expressions transparently.
- `view_expr(e)`: if shift=0 or closed, returns `read_expr` directly. Otherwise adjusts
  children by composing shifts. Non-binder children: O(1). Binder bodies: full traversal
  via `shift_expr_aux` (cached). EXPENSIVE for Pi/Lambda/Let with shift > 0.
- `osnf_adj(nlbv, amount)`: OSNF child adjustment. Normalizes closed children (nlbv=0) to
  CLOSED_SHIFT. Panics if invariant violated. Used in all mk_* constructors.
- `mk_shift(inner, amount)`: returns ExprPtr::closed for closed cores, ExprPtr::new otherwise.
- `unfold_apps`: checks is_closed()/shift==0 per-iteration to avoid unnecessary shift_up.
- **OSNF for cores**: min(open_child.shift) == 0. CLOSED_SHIFT children act as infinity in min.

**Shift composition in inst_aux**: `inst_aux` carries pending shift `(sh_amt, sh_cut)`.
Children's shifts compose with the pending shift: if `child.shift >= sh_cut`, clean
composition. Otherwise, `view_expr` fallback.

### Cheap head checks (view_expr discipline)

`view_expr` is expensive for Pi/Lambda/Let with `shift > 0` — it performs a full
body-traversal to compose shifts under cutoff=1. To avoid this when only the head
constructor or a subset of children is needed:

- **`is_app/is_pi/is_lambda/is_let/is_sort/is_const/is_proj/is_var/is_local/is_nat_lit/is_string_lit`**:
  O(1) tag checks via `read_expr` — no shift work (tag is shift-invariant).
- **`view_app`**: returns `Option<(fun, arg)>`. App children only need `shift_up` (O(1)).
- **`view_proj`, `view_const`, `view_var`**: partial views for non-binder forms.
- **`view_pi_head`, `view_lambda_head`**: return `(name, style, binder_type)` without
  composing body shifts. Skips the expensive binder-body traversal.
- **`read_expr`**: when the DAG tag suffices (e.g., `is_sort_zero`) or when we know
  `e.shift == 0 || e.is_closed()` (e.g., after the peel path in `infer_inner`), use
  `read_expr(e.core)` directly — shift work is unnecessary.

Discipline: prefer `is_*` for tag checks, `view_*_head`/`view_*` for partial views, and
`read_expr` in post-peel code; reserve `view_expr` for places that genuinely need the
full shift-composed view (e.g., binder body traversal in `infer_pi`/`infer_lambda`,
Lambda beta reduction in `whnf_no_unfolding`).

### Canonical OSNF under binders (`canon.rs`, 2026-09-11)

`Theory.lean`'s `IsOSNF.lam` requires `fvar_lb_val (lam body) = 0` with the bound
variable *unbound* — a shift common to the body's free variables is extracted through the
binder, which needs a cutoff adjustment of the body (`adjust_child body lb 1`). Until
2026-09-11 the binder constructors only extracted the body pointer's own uniform shift, and
only when the body did not mention its bound variable, so the same term could be
`Lam(ty, body)+1` or `Lam(ty, body')+0` with the +1 baked into `body'`; the uniqueness
theorem covered the model's normal form, not the code's. Pointer equality — the only
O(1) equality test — then missed alpha-equivalent terms, which is what made con-leche's
`_datF` lemmas exponential (see "Open bug", below).

Now `mk_lambda`/`mk_pi`/`mk_let` (and the parser's `p_binder`/`p_let`, which build the
export DAG and must produce identical cores) extract `lb = (smallest free index >= 1) - 1`
through the binder and apply `unshift(body, lb, 1)` — the theory's `adjust_child`,
implemented once over the `OsnfBuilder` trait for both builders. `unshift` only descends
into children whose pointer shift is below the cutoff (the part that mentions a bound
variable), rebuilds through the canonicalizing constructors, and is memoized per
`(core, amount, cutoff)`.

The extractable shift is read off a per-core **loose-bvar bitset** (`canon::BvSet`), a
side-table like `expr_nlbv` computed at allocation from the children: a `u64` head for
indices `0..64` (`expr_bvmask`) plus, for the cores that have indices `>= 64`, an
arbitrary-length tail stored out of line in a flat arena (`expr_bvtail` offset into
`BvTails`; most cores have `NO_TAIL`, 4 bytes). Shift, unbind (leave a binder: drop
index 0, decrement the rest) and union are exact on it, so `body_lb = min_ge(body, 1) - 1`
is decided exactly for every binder and the implemented normal form is `Theory.lean`'s
throughout — one normal form, no window, no policy switch. The children's sets are OR-ed
shifted straight into the new node's accumulator (`or_shl`/`or_unbind`), so a node whose
indices stay below 64 never allocates. `canon::tests::bvset_matches_naive_sets` checks the
word arithmetic against naive sets across word boundaries, and
`tests::util::osnf_canonical_beyond_the_head_word` pins `λx. x #61` (built directly or as
`(λx. x #51)+10`) and `λx. x #130` to `(λx. x #1) + 60` / `+ 129`.

History, kept for the lessons: the first version was a 48-bit mask with a 16-bit `lo`
("the record may be incomplete from `lo`"), which decided binders only within its window
and by default extracted *nothing* beyond it — not canonical there, and a second, exact
mode using lazily built per-core sorted index sets cost +54% on con-leche.
- A single sticky "`>= 63` occurs" bit is **not** sound: after `k` binders it means
  `>= 63-k`, overlapping the precise range. Sets must be exact under unbind.
- "Undecidable" must mean "open, extract nothing" (`Some(0)`), not "closed" — conflating
  them marked binders with far-out free variables as closed and overflowed
  `nlbv + CLOSED_SHIFT`.
- A per-`(core, cutoff)` memoized traversal for "smallest free index `>= cutoff`" is
  O(n·depth) — every enclosing binder asks with a different cutoff — and visited 648 M
  nodes on one declaration. The bitset answers any cutoff from one per-core record.
- Per-child `Vec` clones in the allocation path (`from_parts(..).shl(..)` and OR) cost
  +25 B instructions on con-leche's parse alone (6.8 M cores with tails, 14.8 M tail
  words); OR-ing into one accumulator and the flat tail arena removed that.

**Memory.** Canonicalization has a memory cost at parse time: a body core is interned
when its export line is read, and when its binder later extracts a shift through it the
rebuilt body is a new core — the old one stays, unreferenced by anything but its export
entry, and it *must* stay until the end because any later line may still reference the
entry (a census on con-leche found every core reachable from some entry until the end;
no lookahead, no freeing). A reference-counted lazy-interning parser was tried and
parked (branch `wip/lazy-parser`): it frees originals early but then re-creates them,
since 9% of rebuilt-through entries are referenced again, 92% of those as ordinary
children — 3x the parse instructions. What is done instead:

- **End-of-parse compaction** (`LeanDag::compact_exprs`): mark from the declarations,
  compact in place, renumber. Init keeps 4.15 M of 5.92 M cores, con-leche 5.26 M of
  19.1 M (and 276 k instead of 6.8 M tailed cores), Mathlib 60.9 M of 87.4 M (master interns
  68.4 M). The steady state during checking is then *below* master (Init 301 MB vs 378 MB). The compaction costs the checker a little:
  dead export cores used to serve as hits for spines the checker rebuilds itself.
- **`ExprTable`**, a `Vec` of cores plus a `hashbrown::HashTable<u32>` over it, replaces
  the `IndexSet` for expressions: compaction in place with no transient copy, `u32`
  indices (half the index memory), hashes recomputed rather than stored.
- The parse-only structures are shrunk: the rebuild memo is a per-core slot `Vec` (one
  rebuild per core is the rule: 2.17 M memo entries over 1.92 M cores on Init) with a
  hash map only for the rest; `expr_remap` is `(u32, u16)`; tails need no offset table
  since a tail exists iff `nlbv > 64` and its length is `ceil(nlbv/64) - 1`.

Peak RSS (single thread; the peak is the parse in every case): Init 432 MB vs master
378 MB (+14%; the first bitset build was 570 MB), std 739 MB vs 644 MB, con-leche
parse 1.54 GB vs 627 MB, con-leche whole export 2.86 GB (first bitset build 4.10 GB). What
remains above master on Init is the dead cores between their line and the end of the
parse (1.77 M × ~60 B) plus the memo; on con-leche the rebuilds are the whole story.

Cost and effect, single-threaded `perf stat` against `origin/master` (`79048ed`):

| | master | **this** | |
|---|---|---|---|
| Init (54k decls) | 226.3 B, 378 MB | **217.8 B, 432 MB** | −3.8% |
| std (93k decls) | 384.2 B, 644 MB | **356.3 B, 739 MB** | −7.3% |
| `perf/fueled-chain` N=6/9/12 | 36 ms / 5.4 s / 263 s (4 600 B) | **1 / 3 / 5 ms** (0.33 B) | exponential → linear (nanoda: 2 / 19 / 34 ms) |
| `ConLeche.checkIotaThm_datF` | 1 513 s | **25 ms** | (nanoda: 40 ms) |
| con-leche whole export | killed at 1 h | **562.7 B, 99 s, 2.86 GB** | |
| `ConLeche.Model.declNative` | — | **15.5 s, 2.49 GB** | 1.1 M → 4.7 M binder builds, 4.2 M → 19.8 M rebuilt nodes |
| con-leche, arena (4 threads) | killed at 1 h | **42 s, 561 B, 3.4 GB** | (nanoda: 1.1 m) |
| Mathlib (671k decls, 4 threads) | 9.95 T, 5.80 GB, 338 s wall / 1 172 s user | **7.88 T, 6.44 GB, 299 s / 976 s** | −20.8% instructions, +11% RSS |

Canonicity does not cost, it pays: pointer equality now catches everything it was missing.
`tests::util::osnf_canonical_under_binder` pins the two shortest cases. What the exact
form does cost on con-leche is *maintaining* it on thousands-deep let chains: the parser
extracts through 233 k binders there, and the checker rebuilds after every `inst_beta`
(`declNative`: 1.1 M → 4.7 M binder builds, 4.2 M → 19.8 M rebuilt nodes). That is the
price of the theorem holding for the code, and it is paid once per distinct core. The
only way to have the theory's form on deep terms *without* rebuilds would be to carry a
cutoff on the pointer — `(core, shift, cutoff)` — so that a shift pulled through a binder
stays lazy; that is a representation change and OSNF would need redoing for cutoff
shifts. Not attempted. Arena suite: 33 correct, 1 `either`, no regressions (Init 213 B / 0.46 GB, std 349 B / 0.79 GB at 4 threads).

### Pointer equality (replacing sem_eq)

All equality checks use pointer equality (`==`). Since expressions are hash-consed into
IndexSets (export-file DAG and per-declaration TC DAG), structurally equal expressions
have the same pointer. `alloc_expr` always probes the export-file DAG first, ensuring
expressions from different sources get the same pointer.

Previously used `sem_eq` (structural walk through Shift wrappers) — removed because
with pointer-based caching, pointer identity is the correct check.

### Lazy zeta in whnf Let case

`whnf_no_unfolding_aux` handles `Let { val, body, .. }` lazily: pushes the let-binding
onto `local_ctx`, reduces the body in the extended context, pops, then `inst_beta(result, [val])`
on the much smaller whnf result. This avoids unbounded inst_beta growth on deeply nested lets.

When whnf encounters `Var(k)` pointing to a let-binding (`lookup_var_value`), it performs
zeta reduction: unfolds to the shifted let value and continues reducing.

`infer_let` uses eager `inst_beta(body, [val])` — always-let-in-context in infer diverges
on 8/54086 Init declarations because `inst_beta(result, [val])` after pop creates
structurally different expressions (not shift-variants), unlike nanoda where fvar-based
zeta returns the original `val` pointer.

### Pointer-based caching (nanoda style)

All caches are keyed by `CorePtr` (DAG pointer identity via hash-consing). No semantic
equality verification needed — pointer equality is exact.

Caches use depth-indexed frames: for an open `ExprPtr(core, shift)` at current depth
`d`, `bucket_idx = d - shift`. Bucket 0 holds closed expressions (shift=CLOSED_SHIFT,
never evicted); higher buckets are pushed/popped with local context. Shifting a cached
result to a query depth is O(1) via `shift_up`.

**WHNF cache**: `FxHashMap<CorePtr, ExprPtr>` per depth bucket. On lookup with shifted
input, we peel the shift, look up the core, and shift the result back. A single cache
entry serves all shifted variants.

**Infer cache**: Separate check/no-check maps per depth bucket. Check entries serve
both Check and InferOnly queries.

**DefEq cache**: Per-depth positive/negative maps (`defeq_pos`/`defeq_neg`), keyed on
normalized ExprPtr pairs and stored in the frame the pair is anchored to, so entries are
discarded when that binder is left. Deliberately *not* an equivalence closure: it records
only pairs that were themselves decided, never pairs connected through a third term. See
"Why the union-find had to go".

### OSNF (Outermost-Shift Normal Form) — everywhere

Every DAG node is a "core" expression. Compound cores (App, Pi, Lambda, Let, Proj)
satisfy the OSNF invariant: the minimum shift among their open children is 0.
Closed children use shift=CLOSED_SHIFT which acts as +infinity in min calculations.
Var(0) is the only Var in the DAG; Var(k) = ExprPtr(var0_ptr, k).

Pointer equality on `ExprPtr` is reliable: two expressions that differ only by a
uniform shift share the same core, and have the same `ExprPtr` if and only if they
have the same shift too. Hash-consing keys (`Expr`) include the shift of each
child, so cores with differently-shifted children are distinct.

**Enforcement**: Both at parse time and during TC. The `mk_app`/`mk_pi`/`mk_lambda`/
`mk_let`/`mk_proj` constructors compute `min_shift` across open children, adjust
each open child via `osnf_adj(nlbv, min_shift)`, and return the core paired with
`min_shift` in the outer `ExprPtr`. `osnf_adj` enforces the CLOSED_SHIFT invariant
(closed children keep CLOSED_SHIFT) and panics on violation.

**view_expr discipline**: see the "Cheap head checks" section above. `view_expr`
performs body-traversal for Pi/Lambda/Let with shift>0, so prefer `is_*`/`view_*_head`
for tag checks and partial views, and `read_expr` when post-peel guarantees shift=0.

### Speculative app congruence in def_eq

Before expensive whnf/delta work in `def_eq_inner`, speculatively try structural App
congruence using only O(1) `cheap_eq` checks on each arg and the head.

`cheap_eq(x, y)`: combines pointer equality (`==`), `eq_cache_contains`, UF check, and `defeq_open_lookup`.
Never recurses — O(1). This is "almost-cached equality": the whole expression may not be
cached, but all sub-components are.

Applied twice: once before whnf (spec_app), once after whnf_cheap_proj (spec_app2, guarded
by `x_n != x || y_n != y`). Also skip redundant second `quick_check` when whnf_cheap_proj
was a no-op.

6.3% hit rate, but each hit avoids expensive whnf + delta unfolding. **-16.7% on full Mathlib.**

### Shift-down-only optimization in inst_aux

When `inst_aux` detects all free bvars are past the substitution range
(via `nlbv` checks), delegates to persistently-cached
`push_shift_down_cutoff(e, n_substs, offset)` instead of traversing. Guard:
`n_substs >= 4` (lower thresholds regress due to HashMap overhead outweighing savings).

### OSNF dead-substitution in inst_aux_quick and inst/inst_beta

The ExprPtr's shift directly tells us the minimum free variable index (for open
expressions). When `e.shift >= n_substs`, ALL substituted variables are dead — no
variable gets substituted, which is O(1).

Three levels of the check:
1. **inst_beta/inst top level**: if `e.shift >= n_substs`, short-circuit before entering
   inst_aux entirely. For inst_beta: return `ExprPtr::new(e.core, e.shift - n_substs)`.
   For inst: return `e`.
2. **inst_aux_quick sh_amt==0**: on per-depth cache miss, check `nlbv <= offset`.
3. **inst_aux_quick sh_amt>0**: when the shifted nlbv falls below offset.

The `expr_nlbv: Vec<u16>` parallel array provides O(1) nlbv access without reading
the full Expr. `inst_cache` is a 64K-entry direct-mapped cache.

### Pre-peel cache for infer/whnf/wnu

Before peeling `ExprPtr(core, n)` at depth d (expensive `split_off`/`extend`), check
if the core's result is already cached at the inner depth d-n. If so, shift the cached
result via `shift_up(n)` and return without peeling. Eliminates >99% of infer/whnf
peels and 67% of wnu peels.

### inst_aux_quick fast path

Inlined `#[inline(always)]` wrapper that checks nlbv early-exits before calling the
full inst_aux (which involves `stacker::maybe_grow` + cache lookup). Avoids ~24M+
function calls for trivial cases (closed expressions, nlbv below offset, dead
substitutions).

### Infrastructure

- `stacker` crate for dynamic stack growth (deep recursion on mathlib)
- 256 MB worker thread stack in `main.rs`
- Iterative `whnf_no_unfolding_aux` (was recursive, caused stack overflow)
- mk_var Vec cache (O(1) lookup by index) and 2-way set-associative mk_app cache (64K entries/1MB,
  lazily allocated after 10K misses). On hit in way-1, promote to way-0 (MRU). On miss,
  evict way-1, move way-0→way-1, insert in way-0. Eliminated billions of hash table lookups
  on pathological declarations. Originally 1M entries (16MB) but reduced to 64K — the 16MB
  cache exceeded L3, causing every access to miss. **14% improvement on Init from right-sizing.**
- `expr_nlbv: Vec<u16>` parallel array alongside `IndexSet<Expr>` in both export-file and
  per-declaration dags. `num_loose_bvars(ptr)` reads from this 2-byte Vec instead of the
  full 48-byte Expr. Most impactful for inst_aux's 48.7M early exits (nlbv=0 check) and
  mk_shift's closed-expression elision. **~2% improvement on Init, ~1.2% on Mathlib 100K.**
- Pre-sized per-declaration dag: `LeanDag::with_capacity(16384)` eliminates hashbrown rehash
  overhead (was 2.3% of runtime from repeated doublings during declaration checking).
- `ReusableDag`: Reuses the per-declaration dag's allocated IndexSet memory across declarations
  via `clear_for_reuse()` (clears entries but preserves capacity). Uses `ManuallyDrop` +
  pointer cast to rebind `LeanDag<'static>` to the local TcCtx lifetime (sound because all
  types use PhantomData for lifetimes with identical layout). Eliminates per-declaration
  allocation/deallocation of ~2MB IndexSets. **~20% improvement on Init.**

## Results

### Correctness
- Passes all arena tests: app-lam, dag-app-binder, init (accept);
  constlevels, level-imax-leq, level-imax-normalization (correctly rejected)
- Full Mathlib (630K declarations): 0 errors, 0 timeouts

### Performance

Fair in-binary comparison (same binary, both TC paths with ReusableDag, 4 threads):

| Benchmark | nanoda TC | nanobruijn TC | Ratio |
|-----------|-----------|---------------|-------|
| Init (54k decls, 310MB) | 6.3s | 7.2s | **1.14x** |
| app-lam N=4000 | 8.3s | 10ms | 0.001x |
| Mathlib (630k decls, 5.0GB) | 320s | 345s | **1.08x** |

Standalone nanobruijn (parsing + TC, 4 threads) with OSNF parse-time normalization:

| Benchmark | without OSNF | with OSNF | Change |
|-----------|-------------|-----------|--------|
| Init | 6.5s | 7.6s | +17% |
| Mathlib (user) | 1175s avg | 1095s | **-7%** user time |
| Mathlib (RSS) | 7.9GB | 9.3GB | +18% RSS |

A/B/A test (baseline, OSNF, baseline): wall times 359s/315s/297s, user times
1297s/1095s/1053s. Baseline run 2 faster than run 1 due to OS page cache warming.
User time (CPU-bound) is the fairer metric: baseline avg 1175s, OSNF 1095s = **-7%**.

Previous table had Init at 24.2s/20.1s — those were standalone binaries with different
IndexSet implementations. The in-binary comparison is fair: same parsing, same dag, same
thread pool, only the TC algorithm differs.

### Gap analysis

On Init nanobruijn is 14% slower (in-binary TC comparison). On full Mathlib standalone
with OSNF, nanobruijn is ~7% faster in user time than without OSNF (1175s → 1095s).
The in-binary comparison (320s nanoda vs 345s nanobruijn = 1.08x) predates OSNF.

Key optimization: `infer_app` preserves lazy Shift wrappers (using `unfold_apps` instead
of `unfold_apps_stack`), allowing infer's shift-peel to strip shifts and infer inner
expressions at their natural depth. This reuses cached inferences from lower binder depths,
avoiding redundant work on shifted expression variants. **-21% on Mathlib** (439s → 345s).

Trace analysis (Init, per-declaration aggregates):
- nanobruijn creates only 2% more expressions than nanoda (80M vs 78M alloc_expr)
- But does 50% more infer calls (24M vs 16M) and 56% more def_eq calls (12M vs 7M)
- The extra calls come from shifted expression variants causing cache misses
- mk_app allocations are nearly identical (59.5M vs 59.1M) — shift overhead is in
  the number of operations, not the number of expressions

Profile hotspots (Mathlib last 210K, pre-optimization): mk_app 14.7%, inst_aux 10.3%,
insert_full 7.6%, subst_aux 4.4%, whnf_no_unfolding 4.2%, unfold_apps 3.2%,
view_expr 3.2%, canonical_hash 2.7%, shift_eq_aux 2.4%, infer_inner 2.4%,
alloc_expr 2.3%, get_index_of 2.3%, HashMap::insert 2.1%, mk_shift_cutoff 1.8%.

## Paths not taken

These approaches were tried and found counterproductive, unsound, or out of scope:

- **alloc_expr_tc** (skip ExportFile probe for TC-generated expressions): When any child
  has DagMarker::TcCtx, skip the export_file IndexSet lookup. Was a 19.4% improvement on
  Init. Removed because it breaks pointer identity: structurally equal expressions can get
  different pointers (one ExportFile, one TcCtx), making pointer-based caching unsound.
  The 17% Init regression from removing it is the cost of correct pointer identity.
- **Shift-equivalence caching** (struct_hash + fvar_bloom + canonical_hash + sem_eq):
  Per-expression struct_hash (shift-invariant hash) and fvar_bloom (32-bit bloom filter of
  free bvar indices) combined into canonical_hash for cache keys, with sem_eq verification
  on hit. Replaced by pointer-based caching — simpler, matches nanoda, and enables future
  OSNF-everywhere where pointer identity is exact. ~660 lines removed.
- **Custom Deserialize for ExportJsonObject** (replacing `#[serde(flatten)]`): **~7.5%
  improvement on Mathlib 100K** (128s → 115s). Reverted because this is a design-neutral
  optimization that could equally be applied to nanoda — out of scope for the design comparison.

- **OSNF enforcement in push_shift_up** (route App/Proj through mk_app/mk_proj when
  fvar_lb > 0): push_shift_up_inner bypasses mk_app/mk_proj for App and Proj, producing
  non-OSNF expressions with fvar_lb > 0. These have different pointers than the equivalent
  OSNF forms, causing cache misses. Fixing this (either via mk_app or inlined adjust_child_tc)
  gives dramatic improvement on AlgebraicGeometry declarations (inst_aux 280M → 89M, -10.4%
  instructions on #272519) but causes 85 panics on full Mathlib (vs 5 baseline) — the
  adjust_child_tc + alloc_expr + mk_shift overhead for fvar_lb > 0 cases is too expensive
  on declarations where the non-OSNF forms didn't cause significant cache misses. The fix
  is correct and beneficial for targeted declarations but needs a cheaper implementation
  to be globally beneficial. **Key insight**: pointer identity loss from non-OSNF push_shift_up
  is a real issue — future work should find a way to fix it with lower overhead.
- **Eager shift resolution** (push_shift in lookup_var, in inst_aux vals): Creates different
  expression identities that cascade poorly through caches. Up to 9x slower.
- **Lazy beta reduction** (push args as let-locals, whnf at higher depth): Changing evaluation
  depth causes catastrophic whnf/wnu cache miss rates (4.2x regression).
- **Negative shifts for below-depth whnf cache hits**: Wrapping stored results in
  `Shift(result, -delta)` or `push_shift(result, -delta, 0)` to lazily defer the shift.
  Crashes: negative Shift wrappers on sub-expressions leak their inner (high-index) Var
  nodes through caches, unfold_apps, and pattern matching. Even `push_shift` (one level)
  fails because it creates `mk_shift_cutoff(child, -delta, 0)` wrappers on children which
  then propagate. Only `push_shift_down` (full eager traversal) works correctly — all Var
  indices are concretely resolved to valid indices at the target depth. The eager approach
  has zero measurable overhead on Init (17K hits, cost offset by avoided recomputation).
  Now implemented: `push_shift_down(stored_result, abs_delta)` with guard
  `result_fvar_lb >= abs_delta`. Lazy negative Shift wrappers are fundamentally incompatible
  with a system where expressions flow through multiple code paths that may read sub-expressions
  directly (via read_expr, unfold_apps, cache lookup) without first resolving Shift wrappers.
- **Negative def_eq caching**: Unsound — def_eq results can change due to side effects from
  intervening comparisons (which may prove sub-expressions equal).
- **Persistent inst_cache across inst_beta calls** (fingerprint-based key): Soundness issues
  from hash collisions (panics with 64-bit fingerprint). Verified cache impractical for
  stack-allocated subst slices.
- **Persistent shift-down for n_substs < 4**: HashMap overhead and eager node creation
  outweigh savings for small substitutions.
- **Canonicalization** (eagerly resolving all Shift nodes): Far too expensive per inst_beta
  result. Also causes infinite recursion when used as a shift cache key (the operation
  preserves structural identity, so lookups find the same entry forever).
- **Depth-sensitive canonical hash** (mixing shift amount into hash): Eliminates cross-depth
  verify-fails but loses 11% of valuable cross-depth cache hits. Net regression.
- **inst_cache DM cache (64K, generation-counted)**: Replacing per-call HashMap with a
  direct-mapped cache at 64K entries (1.3MB). 1.8% slower — the DM cache is in L2/L3
  territory while the per-call HashMap is small and stays in L1. At 4K entries (96KB),
  however, the DM cache with generation counter gives ~3.6% improvement on Init and ~2.7%
  on Mathlib 100K — the O(1) clear (generation bump vs HashMap::clear) and direct slot
  access outweigh the occasional collisions. Now adopted as the inst_cache implementation.
- **Lowering shift-down-only threshold to n_substs >= 1**: 0.4% slower due to HashMap overhead.
- **Various micro-optimizations**: Identity checks in subst_aux/push_shift (branch overhead),
  struct_hash early rejection in shift_eq (most calls are positive matches), mk_app DM cache
  doubling (L2/L3 cache pressure).
- **Speculative Pi/Lambda congruence**: push_local overhead is negligible (0.007% of runtime);
  sem_eq on bodies already tried in quick_check.
- **ExprCache reuse across declarations**: Reusing FxHashMaps across declarations. 2x regression
  because large-declaration HashMap capacity creates L1/L2 cache pressure for small declarations.
- **jemalloc**: 45% regression on Init (35.4s vs 24.5s). glibc's allocator works better for
  this workload's allocation pattern (many small allocations in tight loops).
- **Custom PartialEq for Expr** (only comparing payload fields, not hash/struct_hash/fvar_list):
  17% regression. The compiler optimizes the derived PartialEq into efficient memcmp; the
  match-based custom version has more branching overhead.
- **Wider mk_app DM cache entries** (storing fun+arg+result to avoid read_expr verification):
  No improvement at 64K entries (2MB, L2 pressure offset savings). Neutral at 32K (1MB).
- **whnf_no_unfolding `cur` return shortcut**: Returning `cur` instead of `foldl_apps(e_fun, args)`
  in no-reduction paths. 35% regression — `unfold_apps` normalizes Shift wrappers on args,
  so `cur` still has unnormalized Shift wrappers while `foldl_apps` creates properly normalized
  expressions.
- **shift_eq GenCache reduction** (64K entries): 2x regression on Mathlib. 256K was marginal,
  1M is required for heavy declarations.
- **PGO (Profile-Guided Optimization)**: <1% improvement on Init. Not worth the build complexity.
- **ExprCache reuse across declarations** (with shrink_to cap): 8% regression on Mathlib 100K.
  Same root cause as ExprCache reuse without cap — HashMap capacity from previous declarations
  creates L1/L2 cache pressure even after shrinking. The allocation cost of fresh ExprCache
  per declaration is cheaper than the cache pressure from reused capacity.
- **Precomputed canonical_hash in parallel Vec<u64>**: Store canonical_hash alongside DAG
  expressions for O(1) lookup. No measurable improvement — the saved read_expr calls are
  already cache-hot, and the Vec overhead (compute + push + memory) cancels the savings.
- **fvar_lb parallel Vec<u16>**: Store fvar_lb alongside DAG expressions for O(1) lookup,
  avoiding read_expr + read_fvar_node for cache bucketing. 2% regression — same root cause
  as canonical_hash Vec: the push overhead exceeds the read savings.
- **subst_cache DM cache** (4K entries, generation-counted): 10% regression. Unlike inst_cache,
  the subst_cache is traversal-based (walks entire subexpression DAG within one call). DM cache
  collisions evict entries needed later in the same traversal, causing subtree re-traversal.
  The per-call HashMap stays in L1 and has zero evictions.
- **alloc_fvar_node DM cache** (1K entries): 20% regression. FVarList nodes have high reuse
  within a declaration; DM cache collisions cause expensive re-traversals in fvar_merge.
- **fvar_list TcCtx check in mk_app/mk_lambda/mk_pi/mk_let**: Skipping export_file probe when
  fvar_list has TcCtx dag_marker. No improvement — when all child pointers are ExportFile,
  fvar_union almost always produces ExportFile results, so the check is rarely true.
- **Replacing fvar_list with fvar_lb parallel Vec (no bloom)**: Removed delta-encoded FVarList
  linked list from Expr, replaced with O(1) fvar_lb computation from children. Eliminated
  fvar_union (6.33% on Init). But canonical_hash degraded to struct_hash alone (no
  fvar_normalize_hash), causing 15% regression on Mathlib 100K from cache collision increase.
  **Superseded**: the fvar_bloom approach (32-bit bloom filter) provides sufficient discrimination
  for canonical_hash without the linked list overhead. Now adopted as `fvar_bloom: u32` +
  `fvar_lb: u16` in every Expr variant, replacing FVarList entirely.
  **~2.3% improvement on Mathlib 100K** (fvar_union went from 6.33%+14% children = 20% to 0%).

- **def_eq shift-peel** (strip matching Shift wrappers from both sides, split_off context,
  recurse at lower depth): 10% regression on Init. The split_off/extend Vec operations
  (allocation + copy per call) outweigh the cache reuse benefit. The approach is correct
  (def_eq is preserved by uniform shifting) but impractical due to per-call overhead.
- **eq_cache shift-stripping fallback** (after sem_eq verify failure, strip matching outer
  shifts and retry): Converts only 1.1% of verify failures to hits. Most verify failures
  are genuine hash collisions, not shifted variants. Negligible impact on both Init and
  Mathlib.
- **unfold_apps `shifted` flag** (skip foldl_apps rebuild on no-reduction paths when no
  shifts encountered): Correct but negligible performance impact — the foldl_apps rebuild
  was already cheap relative to the shift overhead.

- **OSNF expression rewriting** (Outermost-Shift Normal Form): For expression `e` with
  `fvar_lb = k > 0`, pre-compute `core = shift_down(e, k, 0)` (fvar_lb = 0). In
  mk_shift_cutoff, rewrite `Shift(e, amount, 0)` → `Shift(core, fvar_lb+amount, 0)`.
  Statistics show 1.99x core sharing on Mathlib 100K (47M → 23.6M unique cores). But
  the rewriting breaks pointer equality during TC: expressions that were identical pointers
  now differ (one has Shift(core, ...) wrapper). When these Shift(core, amt, c=0) nodes
  are compared inside Lambda bodies (tracking cutoff > 0), the cutoff mismatch (0 vs N)
  triggers expensive shift_eq_pending comparisons. **60% regression on Mathlib 100K**
  (2m10s → 3m28s). Also found a pre-existing bug: the `fvar_lb` optimization for
  mismatched Shift cutoffs was using the Shift node's fvar_lb (= inner.fvar_lb + amount)
  instead of inner's fvar_lb, causing false negatives in def_eq. Bug fixed.
  Infrastructure kept (osnf.rs, osnf_core field) for potential cache-key-based approach.
- **OSNF at parse time via mk_shift_cutoff rewriting**: Same approach as above but applied
  during TC rather than at parse time. Same 60% regression — moved to parse-time approach
  below (see Design section: OSNF parse-time normalization).
- **Cached constant ExprPtrs** (Bool.true/false, Nat.zero/succ, Nat, String): Cache the
  ExprPtrs for common constants used in nat/bool/string reduction to avoid repeated
  `alloc_levels_slice(&[]) + mk_const` hash table lookups. No measurable improvement —
  these constants are the first entries in their hash tables, so lookups are already O(1).
  The 2.48% `bool_to_expr` profile cost is dominated by inlined surrounding code, not lookups.
- **Lower mk_app DM threshold** (100 misses instead of 1000): Allocating the 1MB DM cache
  earlier to benefit more declarations. Slightly worse — the 1MB allocation for lightweight
  declarations creates L2/L3 cache pressure without enough mk_app calls to amortize it.
- **view_expr #[inline]**: 10% regression on Init from instruction cache pressure.
  The compiler's default inlining decisions are already optimal.
- **view_expr result cache** (direct-mapped 4K entries, keyed on (core, shift)):
  60% cache hit rate on Init. But the cache overhead (hash computation + indirect
  memory access + Expr copy + cache insert) outweighs the saved work, yielding
  ~1% slower on Init (245B vs 242B). The underlying `shift_expr_aux` cache already
  captures the expensive part; the rest of `view_expr` is too cheap to benefit
  from caching. Key insight: `unfold_pi_step`/`unfold_lambda_step` calls are 99.8%
  on unshifted inputs (shift=0 or closed), so those paths don't need caching
  either.
- **Remove `mk_app_dm_cache`** (after the 2026-04-19 field removal made mk_app lean):
  Init 225.7B → 229.4B (+1.6%); Mathlib 8t: 3m28s → 3m44s wall (+8%), 20m33s → 21m19s
  user (+3.7%). The cache still pays off. **Why:** instrumented per-call-site counters
  show 97% of mk_app calls originate from `inst_aux` and its inline `inst_aux_quick`
  (~34k+7k of ~43k calls per slow Init declaration). The 96% cache hit rate is not
  "identity" (unchanged children): the children genuinely change in most calls. It's
  different substitution paths converging on the same `(fun, arg)` pair downstream —
  `inst_cache` bumps `inst_substs_id` on every top-level `inst`/`inst_beta` call, so
  nothing hits across calls. `mk_app_dm_cache` is the meet point where those paths
  merge and is the right level for this redundancy. Kept.
- **mk_app identity short-circuit** (return original when `new_fun == fun && new_arg == arg
  && sh_amt == 0` in `inst_aux_body` / `inst_aux_quick` App arms): counter shows the path
  fires 14–1521 times per declaration out of ~43k mk_app calls (0.03–3.5%). Init regressed
  225.7B → 233.6B (+3.5%) — the extra compare on every App traversal exceeds the saved
  work. Reverted. The redundancy caught by mk_app_dm_cache is NOT unchanged-identity;
  see above.

- **Memoized `has_bvar(core, idx)` predicate** wired into `inst_aux_quick_core`'s
  sh_amt==0 path: if the specific bvar at `offset` isn't in the subtree, take the cheaper
  `push_shift_down_cutoff` path (cached) instead of the full `inst_aux` recursion. Results:
  - perf/shift-cascade N=1000: 1.10B → 887M (−19%). Still O(N²).
  - perf/shift-cascade "full" variant: unchanged (has_bvar returns true everywhere).
  - Init: 226.3B → 224.7B (noise-level).
  - **Mathlib 8 threads: 9.87T → 9.81T instructions (−0.7%, measured by perf).**
  Reverted. The cascade win doesn't generalize — real-world code (Init, Mathlib) rarely
  hits the "let-var absent in subtree" pattern that the has_bvar skip catches. The added
  HashMap cache + predicate call in a hot path isn't worth 0.7% on Mathlib.
  **Lesson:** wall-clock time on Mathlib is wobbly (showed phantom 4–5% delta);
  instruction counts are the honest metric. Always re-measure both with and without the
  change using `perf stat -e instructions` before committing.

- **Cached `bvars: CorePtr → Bitvector` (precise free-bvar set).** Follow-up to the
  has_bvar experiment: store the *entire* set of free bvar indices (`SmallVec<[u64; 1]>`)
  for each core, so one call answers all `has_bvar` queries — including multi-element
  substitution ranges. Wired into `inst_aux_quick_core`'s sh_amt==0 path via
  `bvars_intersects_range(offset, offset+n_substs)`, replacing the dead `fvar_lb >= …`
  check. Tried both eager (parallel `Vec<BVarSet>` in `LeanDag`, populated at
  `alloc_expr`) and lazy (memoized `expr_cache.bvars_cache`). Results:
  - Eager: cascade N=1000 1.10B → **2.05B (+87%)**, Init 225.7B → 241.4B (+7%).
  - Lazy: cascade N=1000 1.10B → **2.74B (+149%)**.
  Both regress. The precise range check doesn't fire meaningfully on cascade (bvar 0 is
  always present in the let body, so `intersects_range(0,1)` returns true; no skip) and
  adds a range scan on every `inst_aux_quick_core` hit. Storage materialization is the
  killer: deep cascade exprs need up to 16 u64 words → heap spill on each `shift_up`/
  `union_into`. has_bvar's per-`(e, idx)` bool cache is much cheaper per query than a
  full bitvector, even though it recomputes the same subtree multiple times. Reverted
  without committing.
  **Lesson:** "bulk compute once" only helps if each computation is cheap, which fails
  when the structure materialized is O(depth) and the query space is narrow (usually
  just one index). Narrow, lazy, per-query caches beat wide, eager, per-expr tables for
  bvar presence.

- **Lazy `infer_let`** (push let onto local_ctx, infer body, pop, inst_beta on result):
  fixes `perf/shift-cascade` (1000 nested lets) dramatically — **1.12B → 41M instructions,
  27× faster, ahead of nanoda's 53M** on that test. But blows up Init: one declaration
  at ~#19500 hits the 10s per-decl timeout, DAG bloats to 4.5M+ entries in that window.

  **Context:** `perf/shift-cascade` is pathological for pure de Bruijn specifically
  because each let-var `f_k` appears *only* in `f_{k+1}`'s value, nowhere else in the
  body. Scaling measurements at N ∈ {250, 500, 1000, 2000}:
  - Original cascade: nanobruijn O(N²) (ratios 3.38, 3.80, 3.92), nanoda O(N) (ratios
    1.41, 1.60, 1.76). Linear fit for nanoda: `0.039·N + 13.2`.
  - "Full" variant with body `f_1 (f_2 (… (f_N 0)))` (every let-var referenced
    everywhere): both quadratic. nanobruijn ratios 3.62, 3.85; nanoda ratios 3.35,
    3.73. Gap closes from 21× to ~1.6×.

  Nanoda's O(N) win comes from locally-nameless fvar-ification of the outer `fun a`
  in `infer_lambda`. After that single traversal, every `v_k` has `nlbv = 1` (only
  references `f_{k-1}`). At each subsequent `infer_let` level, `inst(body, [val])`'s
  `nlbv ≤ offset` fast-path skips every val at depth ≥ 1 — per-level cost becomes
  O(1). Without fvar-ification, `nlbv` stays high (bvar-indexed outer refs), the
  skip never fires, and we pay O(N-k) per level = O(N²) total. A more general
  dependent-let workload defeats both designs.
  **Not a frame-invalidation issue**: lazy frame invalidation preserves entries on pop.
  **Not a cache-bucketing-slack issue either**: OSNF guarantees that any freshly-allocated
  core at shift=0 inside the let references the let var (at least one child has shift=0
  by min-shift-of-open-children==0). So bucketing those at `d+1` is correct, not wasteful.
  **Actual root cause — zeta produces many unique variants.** In eager mode the single
  up-front `inst_beta(body, [val])` creates one body' where every let-var occurrence has
  been replaced by `val` directly. whnf on body' traverses these and the DAG's hash-consing
  consolidates equivalent sub-expressions into shared cores. Cache hit rate stays ~70%.
  In lazy mode, every `Var(k) → let-var` encounter during whnf triggers a fresh
  `lookup_var_value` that returns `val.shift_up(idx+1)` — a distinct ExprPtr per shift
  amount. Beta reductions downstream then produce distinct shifted variants. The whnf
  cache stores each as a separate key; few repeats. Measured whnf hit rate on the
  diverging Init decl: **174 / 364024 = 0.05%** (eager baseline: ~70%). DAG grows to
  4.5M entries for a single declaration.
  **Why cascade still wins anyway:** in the cascade test, the body's inferred type is
  `Nat` (closed) at every level, so the outer `inst_beta(body_ty, [val])` after pop is
  O(1). The expensive cache-miss churn that plagues the Init diverger doesn't fire,
  because the cascade's body doesn't depend on the let vars in a way that triggers
  zeta-during-whnf — it just declares helpers that happen not to be used further up.
  **Possible fix direction:** unify zeta variants. If `lookup_var_value` returned a
  canonical shape (e.g., by always pre-shifting `val` once at let-push time and
  composing shifts lazily on the ExprPtr), the zeta results would pointer-share across
  occurrences at the same depth. Needs careful design — we already compose shifts via
  `shift_up`, but beta reductions bake the shift into the result via inst_beta, losing
  the shift-composable form. Out of scope for now.
  **Trade-off for now:** we lose on `perf/shift-cascade` vs the official kernel and
  nanoda. Eager-only `infer_let` keeps Init fast but pays O(N²) on deeply nested let
  chains with cross-let value references.
- **target-cpu=native**: Regression. Generic x86-64 code performs better, likely because
  the wider AVX-512 instructions cause frequency throttling on this CPU.
- **Trace counter removal**: Commenting out all 116 `self.trace.xxx += 1` increments.
  15% regression — the compiler uses trace field accesses for register allocation and
  code layout decisions; removing them changes the instruction sequence for the worse.
- **canonical_hash fast-path for closed expressions**: Skip `fvar_normalize_hash` when
  `fvar_list.is_none()`. No measurable improvement — the compiler already optimizes
  `fvar_normalize_hash(None)` to return 0 quickly.

## Upstream nanoda porting

Reviewed all nanoda_lib commits from fork point `68d5ca9` through `3a24072` (2026-09-22).

Applied:
- **`4219437` — Encode DagMarker in bit 31 of Ptr** (by Mark Ruvald Pedersen):
  Ptr goes from 5-byte repr(packed) to 4-byte naturally-aligned u32.
  Upstream reported +12% improvement from better cache density and aligned loads.
- **`9557f24` / `2097cc6` — Remove truncating casts** (by Luca Bruno / ammkrn):
  `pos as u16` → `u16::try_from(pos).unwrap()` in abstr_aux,
  `ind_type_idx as usize` → `usize::try_from(ind_type_idx).unwrap()` in inductive.rs.
- **PR #22 (`ddfac2b`) — more struct and inductive checks** (by ammkrn):
  (1) `Env::get_structure(n, rec_ok)` gates projection/eta/unit-like paths on actual
  structure shape (single ctor, no indices, recursion only allowed where safe);
  `can_be_struct` is now a thin wrapper over it. (2) `aux_data_ck` methods on
  `InductiveData`/`ConstructorData`/`RecursorData` assert that auxiliary data computed
  while checking inductives matches the export file's assertions, and
  `check_inductive_declar` recomputes `is_recursive` and asserts it matches `isRec`.
- **PR #23 (`404660c`) — upstream safety checks** (by ammkrn): the private `_nested`
  name prefix is rejected in the types of a checked inductive, its mutual block, and its
  constructors (`TcCtx::get_pfx`, `has_nested_pfx`, generic `find_e` traversal);
  `def_eq_proj` requires equal structure names, not just equal indices.
- **PR #24 (`78ded44`) — conservative always/never zero** (by ammkrn): `is_proposition`
  splits into `is_prop` (type whnfs to `Sort l` with `l <= 0`, via the partial order) and
  `may_be_prop` (`l` not *syntactically* guaranteed nonzero, via the new structural
  `is_never_zero`, which unlike `is_nonzero` never reasons from assumptions about params).
  `infer_proj` and `iota_try_eta_struct` guard on `may_be_prop`, so their restrictions
  apply whenever the type *might* be a proposition.
- **PR #26 (`f04456a`) — underived recursor checks** (by ammkrn): the parser records
  `ind_name_to_recursor_names`; `ck_recursor_names_simple` requires set equality between
  derived and exported recursor names, so extra recursors cannot be smuggled in. For
  nested inductives the derived set is `mk_base_rec_names` unioned with the unspecialized
  nested recursor names.
- **PR #27 (`05024bd`, part) — is_sort guards** (by ammkrn): `is_prop`/`may_be_prop`
  panic when the argument's type does not whnf to a `Sort`, instead of reporting
  "not a prop" for a malformed input. See below for the part not taken.
- **PR #28 (`8a327a1`) — prohibit orphan recursors** (by ammkrn): every recursor must
  name an inductive that exists, is an inductive, and was exported before it — otherwise
  it is never checked against a derivation. Factored into `ck_recursor_has_inductive`
  since nanobruijn dispatches declarations separately for its two checkers.

Cost of the PR #22–#28 checks together: Init 226.64B → 227.51B instructions
(**+0.38%**, single-threaded, `perf stat`). Most of it is the per-inductive work these
added — recomputing `is_recursive`, scanning types for a `_nested` prefix, and building
and comparing recursor name sets.

- **PR #31 (`0928383`) — perf improvements from the FLT project** (by ammkrn), 2026-09-28:
  (1) scratch maps (`abstr_cache`, `abstr_cache_levels`, `subst_cache`) are replaced
  rather than cleared once they have grown past 1024 entries, since clearing costs the
  capacity, not the length (`reset_scratch_map`; nanobruijn's `inst_cache` is a
  direct-mapped `Vec`, so nothing to do there); (2) a per-declaration memo of `def_eq`
  calls that returned false, keyed by the pair and the eager-mode flag — nanobruijn's
  depth-bucketed `defeq_neg` cache, so far only fed by congruence failures in the lazy
  delta step, now also takes every deep `def_eq` failure and carries the eager flag in
  its key; (3) `try_eq_const_app` compares arguments right to left, the last ones being
  the most likely to differ. The general memo must stay apart from the congruence
  failures (the key carries a flag): "arguments differ under the same head" does not
  make the sides unequal once the head unfolds, and merging the two made Mathlib fail.
  Effect: Init/std/con-leche within ±0.7% single-threaded, **Mathlib 7.89 T → 4.72 T
  instructions (−40%)**, 278 s → 231 s wall at 4 threads, RSS unchanged — Mathlib's
  instance-heavy terms repeat the same failing comparisons over and over.
- **PR #34 (`c8e5083`) — pretty-printer grouping** (by Scott Hughes): `partition_slice`
  used `partition_point`, which assumed "same type/style as the first binder" partitions
  the telescope; it scans to the first nonmatch now, with the four regression tests in
  `tests/pretty_printer.rs`. Printing only.
- **PR #36 (`b36e6f3`) — sub-quadratic decimal nat literals** (by lordwilson):
  `parse_decimal_fast` splits a digit string by `10^(2048·2^j)` and recombines with big
  multiplications instead of `BigUint::from_str`, which is quadratic in the digit count
  (a 25 M-digit literal took longer than five minutes to parse). The accompanying
  dependency bumps (num-bigint 0.5, rand 0.10, num-integer/num-traits) are taken too;
  only the tests' rand API use changed.
- **PR #27 (`05024bd`, part) — replace the union-find def-eq cache.** Upstream swaps
  `UnionFind` for an `FxHashSet<SortedPair>` so the cache cannot conclude `x = z` from
  cached `x = y` and `y = z`, and drops `union_find.rs` entirely. Done here too; see
  below for why and for the nanobruijn-specific shape of the replacement.

### Why the union-find had to go

The problem is not that transitivity concludes *wrong* equalities. Definitional equality
really is transitive, so a transitive cache is sound exactly when `def_eq` is sound, and
an audit over all of Init found the union-find never asserting an equality the algorithm
could not re-derive (1,356,917 hits, 0 unconfirmed).

The problem is that the union-find makes `def_eq` **non-monotonic in time**: a pair can
be judged unequal, and then, after unrelated pairs are cached and the equivalence classes
grow, judged equal. `def_eq` is an incomplete procedure, so a "no" that later becomes
"yes" is not by itself unsound. It becomes unsound when a decision that has to stay
*consistent across a check* is derived from it — whether a type is impredicative, whether
a projection applies. Those must not change answer halfway through. That instability, not
a fabricated equality, is what made the analogous cache unsound in Lean's own kernel.
Nobody has engineered that attack against nanoda, but the principle carries over, so the
cache should not be an equivalence closure regardless of whether an exploit exists today.

### The replacement

Upstream's flat `SortedPair` set works for nanoda because locally-nameless terms with
unique fvar ids denote the same thing everywhere. A nanobruijn `ExprPtr` is
`(core, shift)` and denotes different things at different depths, so the positive cache is
**depth-bucketed like every other nanobruijn cache**: `DepthFrame::defeq_pos` plus a
`defeq_pos_base` for closed pairs, entered through the existing `defeq_normalize_pair` /
`defeq_canon_key_open` helpers. It is an exact mirror of the negative (`defeq_neg`) cache,
which already had precisely this shape — normalize the pair's shifts to a bucket, key on
the hash-ordered pair, store in the frame the pair is anchored to so the entry dies when
that binder is left. `defeq_canon_key_open` *is* upstream's `SortedPair::new`.

`nanoda_tc.rs` is locally-nameless like upstream, so it takes upstream's change literally:
a flat `FxHashSet<SortedPair<CorePtr>>`, with `SortedPair` in `util.rs`.

Cost, single-threaded `perf stat`, median of 3 (Init) / 2 (std):

| | union-find | pair cache | |
|---|---|---|---|
| Init (54k decls) | 227.64B | **226.56B** | −0.45% |
| std (10M-line export) | 384.22B | **382.87B** | −0.35% |

So the equivalence closure was not paying for itself: it produced only 0.7% more hits on
Init (1,356,917 vs 1,348,015) while `uf_find`'s chain-walking cost more than the extra
hits saved. The `cheap_eq` speculative app congruence (**-16.7% on full Mathlib**) does
not depend on transitivity — `cheap_eq` is now `x == y || defeq_pos_lookup(x, y)` and
keeps answering from the pair cache.

An earlier measurement of the union-find's "transitive" hit share (21% on Init) was an
overestimate: it classified a hit as transitive whenever neither side was the other's
representative, which path compression and re-parenting make common for directly-unioned
pairs too. The 0.7% hit-count difference is the honest figure.

### Auditing the def_eq cache (`verify_defeq_cache`)

The `verify_defeq_cache` config option re-decides every positive-cache hit with the
def_eq caches suppressed (`TypeChecker::defeq_cache_suppressed`, which covers the negative
cache too) and reports any hit the algorithm cannot independently confirm. Since the cache
cleanup left this as the *only* positive def_eq cache, suppressing it makes the
re-decision purely algorithmic. `NANOBRUIJN_AUDIT_CONTROL=1` is the self-test: it feeds
the audit pairs the checker has just judged *un*equal, and every one must come back
unconfirmed, otherwise a clean audit would mean nothing (init-prelude: 10 of 10 with the
control, 0 without).

With the pair cache, Init audits 1,348,015 hits with 0 unconfirmed. Under the union-find
the same audit found 11 unconfirmed hits across the arena suite, all in `proj-of-stuck-prop`
and `rec-missing-ih` — adversarial exports that are correctly rejected either way, and all
of them direct unions rather than transitive. They are gone now, but they were never
evidence about transitivity; they say a def_eq result on malformed input is not always
reproducible on a second independent attempt, which is a separate open question.

### Arena results

Checked against the [lean-kernel-arena](https://github.com/leanprover/lean-kernel-arena)
suite (29 tests built locally; `cedar`, `cslib` and `mathlib` skipped as they pull large
repos). At `8cd5f61`, before these ports, three soundness tests failed — `extra-rec`,
`orphan-rec` and `proj-of-subst-prop` were each *accepted*, i.e. a proof of `False` got
through. PRs #26, #28 and #24 close them respectively. Current status: **28 correct,
0 incorrect**, 1 `either` (`nested-nonuniform-param`, which the arena accepts either way).

Not applicable:
- `3e705b3` — nix flake (dev tooling)
- `7981ff6` / `224b7c1` — README update for JSON export format
- `514a1a5` / `14bbb5c` — semver bumps
- `b109108` — README paragraph documenting `unsafe_permit_all_axioms`. nanobruijn's
  README defers config options to `--help` rather than enumerating them, and the
  mutual-exclusivity enforcement the paragraph describes is already in `util.rs`.
- **PR #21 (`698c869`) — exit code 2 for discontiguous backrefs.** Upstream *declines*
  export files whose `in`/`il`/`ie` indices are not contiguous. nanobruijn deliberately
  went the other way in `5a42fcc`: the parser resolves references through
  `name_remap`/`level_remap`/`expr_remap` and *supports* sparse and out-of-order indices,
  with the arena's `LevelIndexOutOfOrder` and `SparseNameIndex` cases as regression tests.
  Porting this would remove a tested capability.

## Resolved: con-leche timed out (`checkIotaThm_datF`) — pointer equality missed alpha-equivalent terms

The arena's `con-leche` test (checks con-leche's own consistency proof and
parser-equivalence theorem) is the one test nanobruijn fails: 73/73 soundness and
119/120 completeness. **It is a timeout, not a rejection**: the arena's run command
masks the exit code (`|| exit 1`), the run is killed at exactly the 1 h `timeout` after
164.9 T instructions, and stderr holds only the `ExprPtr parse:` line, no panic. The
export is ~1.7x Init and everyone else is fast (nanoda 1.1 m, official 1.8 m, lean4lean
2.8 m).

**Localised to the `_datF` lemma family.** Serial checking reaches 11 000 of 27 349
declarations in 7.6 s, then stalls. Same binary, same parsed export, `use_nanoda_tc`
toggled:

| # | declaration | nanoda | nanobruijn |
|---|---|---|---|
| 11833 | `ConLeche.checkIotaThmN_datF` | 100 ms | > 5 min |
| 11834 | `ConLeche.checkIotaThm_datF` | 40 ms | **1 513 255 ms (25.2 min), 37 800x** |
| 11837 | `ConLeche.checkIotaRule_datF` | 19 ms | 91 ms |
| 11843 | `ConLeche.checkProjTy_datF` | 3 ms | 10 ms |

#11834's counters against nanoda's: def_eq 484 M vs 9 278 (52 000x), whnf 1.14 G vs
12 273, alloc_expr 7.6 G vs 177 774 — while touching only 1.24 M distinct DAG nodes and
with the caches hitting (whnf 83%, mk_app 32.8 G hits). It is an exponentially branching
search, not cache loss. Not caused by dropping the union-find: `63fd6b4` and `79048ed`
hang identically. Reproducer on the arena's built export:
`{"use_nanoda_tc": false, "num_threads": 1, "skip_declarations": 11833, "max_declarations": 11834}`.

**What the lemmas are.** `f_datF : (f (m := FueledM) args).val F = f (m := CheckM) args`,
proved by `unfold f; simp only [FueledM.atF_bind, atF_pure, atF_throw, atF_ite, …]`.
`FueledM α = {p : Nat → CheckM α // ∀ f f' v, f ≤ f' → p f = .ok v → p f' = .ok v}`, and
`FueledM.bind x k = ⟨fun F => x.val F >>= fun a => (k a).val F, proof⟩`. What the kernel
has to decide is `f FueledM args ≡ <the unfolded body>` (from `unfold`) and then the two
monadic programs against each other, under one binder per `bind`.

### Root cause: pointer equality misses alpha-equivalent terms

Tracing every top-level def_eq in both checkers on `checkProjTy_datF`
(ad-hoc env-gated tracing in `def_eq`, not kept) and diffing the trees:

- nanoda's heaviest root costs 140 nested calls; nanobruijn's costs 1 891 and is the bare
  comparison `checkProjTy FueledM … $0…$6` vs its unfolding, the `let pty := …; let
  __do_jp := …` join-point chain.
- Lazy delta unfolds `checkProjTy` once. In nanoda the result is pointer-identical to the
  RHS (hash-consing on locally-nameless terms with the same fvars) and the loop stops.
  In nanobruijn the result is **alpha-equivalent modulo shift placement but not
  pointer-equal** (`LD d=1 it=2 eq=false sem=true`), so the comparison proceeds
  structurally into the two FueledM programs. 19 of the 24 lazy-delta steps at depth <= 4
  in that root are `eq=false sem=true`; across the declaration **75% of all deep def_eq
  calls (1 913 of 2 559) compare sides that are alpha-equal modulo shifts** (65% on
  `checkIotaRule_datF`). Each of those should have been an O(1) hit.
- The exponent: a structural descent through `Bind.bind FueledM …` vs `Bind.bind FueledM …`
  reaches `try_eq_const_app`, which returns `None` without any argument failing (the heads
  differ by then), so both sides are unfolded — one to the stuck projection
  `(Monad.toBind FueledM inst).0 …`, the other (via the whnf cache) all the way to
  `Subtype.mk (Nat → CheckM Expr) (fun p => monotone…) (fun F => …)`. Lazy delta is then
  exhausted (proj-headed vs constructor), `rew` unfolds the first side to match, and
  `⟨p₁, h₁⟩ ≡ ⟨p₂, h₂⟩` compares the monotonicity **proofs**: proof irrelevance compares
  their types, `∀ f f' v, f ≤ f' → p f = .ok v → p f' = .ok v`, which mention `p f` and
  `p f'` — so the sub-program is compared again, under three more binders, twice.
  ~3–4x per bind. nanoda only ever reaches the CheckM binds through `Subtype.val`, which
  projects the proof away, so it sees `Except.bind` there and stays linear.
- Confirmed by a distilled reproducer, now an arena perf test
  (`_tmp/lean-kernel-arena/tests/perf/fueled-chain.lean`, branch `perf-fueled-chain`): a
  fuel-indexed `Subtype` monad whose property mentions `p` twice under binders (trivially
  true — the monotonicity proof is not what matters), a `lift`, and `chainN`: N binds each
  followed by an `unless … throw` guard, with the `_datF` lemma proved exactly as con-leche
  does. nanoda 2 / 18 / 32 ms and nanobruijn **19 ms / 4.1 s / 256 s** at N = 6 / 9 / 12,
  i.e. ~4x per guard. Bisecting the ingredients: binds without guards are < 1 ms for both
  at N = 12; guards as tail `if`s instead of `do` join points give ~x25 at N = 9; and a
  property whose two mentions of `p` are the *same* subterm (`p f = .ok v → p f = .ok v`)
  halves the exponent base to ~2, because the second mention hits pointer equality — the
  base is the number of *distinct* re-comparisons of the rest of the program per level.

Why the representations differ — **the implementation does not compute the theory's normal
form under binders.** `Theory.lean` proves `osnf_unique` / `equiv_iff_osnf_eq` for a form
whose `lam` rule is `fvar_lb_val (lam body) = 0` with `fvars (lam body) = unbind body.fvars`:
the bound variable is dropped and the rest decremented, so a shift common to the body's
*free* variables is pulled out through the binder, and `mk_osnf_compound` realizes that
with `adjust_child body lb 1` — a shift with a **cutoff**, which recurses into the body.
The implementation's `mk_lambda`/`mk_pi` (`body_outer_shift`) instead extract only the
body pointer's own uniform shift, and only when the body does not mention the bound
variable at all (`nlbv(body) <= 1 → None`); if the body uses `#0` next to free variables,
nothing is extracted, because `osnf_adj` is a uniform subtraction and would underflow on
the `V0+0` child. The shortest pair, built by the real constructors
(`tests::util::osnf_not_canonical_under_binder`):

    lazy  = Lam(Sort 0, App(V0+0, V0+1)+0) +1      -- (λx. x #1) shifted by 1
    baked = Lam(Sort 0, App(V0+0, V0+2)+0) +0      -- λx. x #2 built directly

`materialize_expr lazy` prints identically to `baked`; the pointers differ. The theory's
`to_osnf` of this term is the lazy form (`fvar_lb_val (lam (app (bvar 0) (bvar 2))) = 1`,
so it becomes `shift 1 (lam (app (bvar 0) (bvar 1)))`); the implementation accepts both as
normal. So the uniqueness proof covers the model's normal form, not the invariant the
code maintains; the code's invariant is canonical for `app` and for binders whose body
does not use the bound variable, and non-canonical otherwise. In con-leche the observed
pair (dumped by a one-off diagnostic) is exactly this at scale: `App(P+0, A+0)+1` vs `App(P+1, A'+0)+0` with
`A'` the join-point lambda whose body had the +1 pushed past its `V0+0` children.

This is a gap in the checker's premise, not just a performance bug: pointer equality on
`(core, shift)` is complete for alpha-equivalent terms only if the representation is
canonical, and it is not. The theory shows what canonical would cost: extracting a shift
through a binder needs a cutoff adjustment of the body, i.e. a traversal — the work the
lazy-shift design set out to avoid. The options are (a) implement `IsOSNF.lam` in the
binder constructors and pay that traversal at construction (possibly cheap in practice
if bodies rarely mix `#0` with a common free shift, to be measured), or (b) keep the
weaker invariant and make `def_eq_quick_check` complete by other means (a
representation-insensitive equality gated by a shift-invariant hash).

Refuted along the way (each changed no counter): frame-invalidation of the depth-bucketed
caches; the union-find removal; eager zeta in whnf's `Let` case; cheap-projection whnf
consuming cached non-cheap results; a dead negative cache (it is narrowly scoped in nanoda
too).

**Resolution (2026-09-11).** Option (a), implemented in `canon.rs`; see "Canonical OSNF under binders" in the Design section for the mechanism, the two pitfalls, and the measurements. con-leche now checks in 24.1 s on the arena (33/33 correct), Init is 4.0% and std 7.2% cheaper.

## TODO

- **OSNF everywhere (including TC-generated expressions)**: DONE. Parse-time and
  TC-generated expressions both go through `osnf_adj` in the mk_* constructors.
  Pointer equality via `CorePtr` is reliable.

- **ExprPtr instead of Shift constructor**: DONE. `Shift` variant removed from the
  `Expr` enum; shifts carried in the outer `ExprPtr = (CorePtr, u16)` pair. No DAG
  entries for Shifts.

- **Optimize view_expr usage**: DONE. Added cheap `is_*` head checks and `view_*`
  partial views (view_app, view_proj, view_const, view_var, view_pi_head,
  view_lambda_head). Hot paths in `def_eq_binder_multi`, `spec_app_congruence`,
  `ensure_pi`, `ensure_sort`, `try_eta_expansion`, `infer_inner`,
  `whnf_no_unfolding_aux`, `is_sort_zero`, Quot iota, inductive restore paths
  converted to use these instead of `view_expr`.

- **fvar_lb removal**: DONE. `fvar_lb` field removed from Expr. Shift info is
  in the outer `ExprPtr`; Expr's `num_loose_bvars` (a parallel array) serves
  for quick nlbv lookup.

- **Depth-stacked UF for def_eq**: DONE. Cross-shift weighted UF with per-depth buckets
  in DepthFrame. Unions for closed expressions go to bucket 0; open expressions to
  `depth - shift`. The `uf_find` method follows chains across buckets via `sptr_shift`.

- **Lazy frame invalidation**: DONE. On `pop_local`, frames are hidden (depth counter
  decremented) rather than destroyed. On `push_local`, if a hidden frame exists with
  matching binder type, it is reused with all its caches intact. This catches the
  pop-all/push-all-same pattern (e.g., checking a declaration's type then its value
  traverses the same binders). Limitation vs nanoda's flat DbjLevel cache: we only
  get reuse when (a) the contexts match exactly and (b) the pop+push are consecutive
  (no intervening push of a different type at the same depth). Nanoda's flat cache
  gets hits even when contexts differ in the middle or when other work happens between
  the two identical contexts. Closing this gap would require a fundamentally different
  cache architecture (e.g., context-indexed flat cache).

- **CLOSED_SHIFT (u16::MAX) for closed expressions**: DONE. `SPtr::CLOSED_SHIFT = u16::MAX`
  indicates a closed expression (nlbv=0). O(1) closedness check via `is_closed()` instead
  of DAG lookup. Acts as +infinity in min calculations. Eliminates DAG lookups in
  sptr_nlbv, sptr_shift, cache_bucket, unfold_apps peel guards.
  Strict invariant: shift=0 means OPEN at current depth, CLOSED_SHIFT means closed.
  Enforced by `osnf_adj` (panics on violation). Invariant violation root-caused and fixed
  (nested inductive types with no params to abstract).

- **Lean Expr struct (2026-04-19)**: `hash`, `num_loose_bvars`, and `has_fvars` fields all
  removed from every Expr variant.
  - `hash`: now computed on demand in `Expr::get_hash()`.
  - `num_loose_bvars`: only stored in the parallel `expr_nlbv: Vec<u16>` (populated at
    `alloc_expr` from children's ExprPtr shifts via `TcCtx::compute_nlbv`).
  - `has_fvars`: lazy memoized on `CorePtr` via `expr_cache.has_fvars_cache` (FxHashMap).
    Only queried on non-hot paths (inductive.rs assertions, nanoda_tc, abstr early-exit).
  - **`osnf_adj` simplified**: takes only `amount` (no nlbv). Pure O(1) branching
    arithmetic — `if self.is_closed() { self } else { Self::new(self.core, self.shift - amount) }`.
  - **`mk_app` simplified**: pure ExprPtr arithmetic — two `is_closed()` checks, shift min,
    `osnf_adj` on each child, `alloc_expr`. No nlbv/has_fvars lookups.
  - **Impact**: Init 241.6B → 225.7B (-6.6%).

- **Cache cleanup (2026-04-19)**: removed caches that were subsumed or unhelpful:
  - `defeq_pos`: 0 hits / 988k UF hits on Init — strictly subsumed by UF. Removed.
  - `mk_pi_cache` / `mk_lambda_cache`: 54-59% hit rate but HashMap overhead ≈ `alloc_expr`
    probe cost; `alloc_expr` already hash-conses. Removed.
  - `strong_cache` + `eq_cache`: subsumed by UF. `cheap_eq` is now just
    `x == y || uf_check_eq(x, y)`. Removed.
  - Kept: `mk_app_dm_cache`. See below.
  - **Superseded 2026-08-26**: the UF is gone (see "Why the union-find had to go") and
    `defeq_pos` is back, now as the sole positive def_eq cache. `cheap_eq` is
    `x == y || defeq_pos_lookup(x, y)`. The "0 hits" above was an artifact of the UF
    being consulted first; standalone it takes 1.35M hits on Init.

## Current performance

Local measurements (release build):

| | Init (instructions, single-thread) | Mathlib (8 threads, wall / user) |
|---|---|---|
| nanobruijn (2026-09-28, + upstream PR #31 def_eq failure memo) | 218.5B (std 356.9B) | 4 threads: 4.72T, 231s / 706s, 6.4 GB |
| nanobruijn (2026-09-11, canonical binders + compaction) | 217.8B (std 356.3B) | 4 threads: 7.88T, 299s / 976s, 6.4 GB (master 9.95T, 338s / 1172s, 5.8 GB) |
| nanobruijn (2026-04-19, post-field-removal) | 225.7B | 3m28s / 20m33s |
| nanobruijn (2026-04-18) | 242B | — |
| nanobruijn (pre-CLOSED_SHIFT, 2026-04-15) | 238B | ~11.5T |
| Nanoda Init baseline | 227B | — |

Note: earlier comparisons claiming a large speedup over nanoda on Mathlib were
incorrect (mis-remembered nanoda number). For up-to-date cross-checker comparisons,
see [arena results](https://arena.lean-lang.org/).

**`max_declarations` caveat**: honored only in serial mode (`tc.rs:177`); parallel
mode pulls from an atomic counter until exhausted. Don't extrapolate from `_10k.json`
timings assuming they scale to full Mathlib — the first 10k are Init + early imports
and are denser than the tail.

### TODOs

- **Theory.lean**: cleaned up — the shift-invariant-caching / `cacheKey` material
  (abandoned along with the `canonical_hash` approach, see "Paths not taken") has been
  removed, along with demos, the unused `fvars_shift_zero` sorry, and two simp
  linter warnings. Main results kept and proven: `to_osnf_isOSNF`, `to_osnf_erase`,
  `osnf_unique`, `to_osnf_idempotent`, `equiv_iff_osnf_eq`, plus `adjust_child_erase`.
  Seven axioms remain, all linking the delta-encoded `SExpr.fvars` to the free-var
  structure of `SExpr.erase` — informally obvious, formally require a `decode`-based
  characterization of `fvars`. Attempting this in session stalled on Lean's `union.induct`
  naming under universal quantification plus fiddly `rintro rfl` substitutions;
  mechanically tractable but outside the session's budget.
- **Remove remaining dead code**: thread_local profiling counters, dead locally-nameless
  code (Local variant, FVarId, abstr, etc.), stale TcTrace fields (verify_fail counters)

## References

- [Lean Kernel Arena](https://arena.lean-lang.org/) — benchmarks and test cases
- [Arena results](https://leanprover.github.io/lean-kernel-arena/)
- [Kernel implementation analysis](https://gist.github.com/nomeata/b0d8da6857cd2fd4c4a22c03ca404164)
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/title_page.html)
- [Lean Type Theory](https://github.com/digama0/lean-type-theory)

