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

**DefEq cache**: Per-depth positive/negative maps (keyed on normalized ExprPtr pairs).
`UnionFind<ExprPtr>` provides transitive equality with depth-stratified unions — unions
proven at higher depths live in higher buckets and are discarded on pop.

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
- **target-cpu=native**: Regression. Generic x86-64 code performs better, likely because
  the wider AVX-512 instructions cause frequency throttling on this CPU.
- **Trace counter removal**: Commenting out all 116 `self.trace.xxx += 1` increments.
  15% regression — the compiler uses trace field accesses for register allocation and
  code layout decisions; removing them changes the instruction sequence for the worse.
- **canonical_hash fast-path for closed expressions**: Skip `fvar_normalize_hash` when
  `fvar_list.is_none()`. No measurable improvement — the compiler already optimizes
  `fvar_normalize_hash(None)` to return 0 quickly.

## Upstream nanoda porting

Reviewed all nanoda_lib commits from fork point `68d5ca9` through `6d2f037` (2026-04-07).

Applied:
- **`4219437` — Encode DagMarker in bit 31 of Ptr** (by Mark Ruvald Pedersen):
  Ptr goes from 5-byte repr(packed) to 4-byte naturally-aligned u32.
  Upstream reported +12% improvement from better cache density and aligned loads.
- **`9557f24` / `2097cc6` — Remove truncating casts** (by Luca Bruno / ammkrn):
  `pos as u16` → `u16::try_from(pos).unwrap()` in abstr_aux,
  `ind_type_idx as usize` → `usize::try_from(ind_type_idx).unwrap()` in inductive.rs.

Not applicable:
- `3e705b3` — nix flake (dev tooling)
- `7981ff6` / `224b7c1` — README update for JSON export format
- `514a1a5` / `14bbb5c` — semver bumps

## Current status (2026-04-12)

Ptr-based caching transition complete: all caches use ExprPtr keys, sem_eq/struct_hash/
fvar_bloom/canonical_hash/ChainMap/alloc_expr_tc removed. ~660 lines deleted. Pointer
equality (`==`) is the sole equality check, matching nanoda's design.

### Performance

Init standalone (profiling build, 4 threads):
- nanobruijn: 8.4s (17% regression from ExportFile probe — previously alloc_expr_tc skipped it)
- nanoda: 5.1s release / 17.7s profiling

Profile hotspots (Init, profiling build):
- nanobruijn: mk_app 19.5%, alloc_expr 7.5%, inst_aux 9.0%+3.8%, stacker 2.0%,
  view_expr 1.6%, mk_shift_cutoff 1.2%
- nanoda: mk_app 11.1%, HashMap::insert 12.9%, inst_aux 7.0%

Mathlib standalone (1 thread, `ulimit -v 10G`, sequential A/B):

| | nanobruijn | nanoda |
|---|---|---|
| Wall time | 19:25 (1165s) | 27:50 (1670s) |
| Max RSS | 9.42 GB | 8.91 GB |

nanobruijn is **30% faster** on Mathlib single-threaded. Memory difference is only 500MB.

With 4 threads, nanobruijn OOMs at 16GB. Root cause: pathological declarations create
massive TC DAGs (up to 46M entries ≈ 2.9GB). With 4 threads, 2-3 heavy declarations
overlapping exhausts memory (9.4GB export DAG + 3×2.9GB = 18GB).

**Pathological declaration analysis** — `Algebra.Generators.H1Cotangent.exact_δ_map`:
- nanoda: 185ms, 664K alloc_expr
- nanobruijn: 27,536ms (149x), 70.9M alloc_expr (107x), 46M TC DAG entries

Similar 100x blowup on other algebraic geometry declarations (CotangentSpace,
KaehlerDifferential, etc.). Root cause: TC-generated expressions aren't in OSNF, so
shifted variants of the same structural expression get different pointers, causing
cascading cache misses → repeated whnf/infer → more expression creation → more misses.

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

## Current performance

Local measurements (single-thread, release build):

| | Init | Mathlib |
|---|---|---|
| nanobruijn (2026-04-18) | 242B | 11.0T |
| nanobruijn (pre-CLOSED_SHIFT, 2026-04-15) | 238B | ~11.5T |
| Nanoda Init baseline | 227B | — |

Note: earlier comparisons claiming a large speedup over nanoda on Mathlib were
incorrect (mis-remembered nanoda number). For up-to-date cross-checker comparisons,
see [arena results](https://arena.lean-lang.org/).

### TODOs

- **Fill in Theory.lean sorry's**: OSNF uniqueness, erase preservation
- **Remove remaining dead code**: thread_local profiling counters, dead locally-nameless
  code (Local variant, FVarId, abstr, etc.), stale TcTrace fields (verify_fail counters)

## References

- [Lean Kernel Arena](https://arena.lean-lang.org/) — benchmarks and test cases
- [Arena results](https://leanprover.github.io/lean-kernel-arena/)
- [Kernel implementation analysis](https://gist.github.com/nomeata/b0d8da6857cd2fd4c4a22c03ca404164)
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/title_page.html)
- [Lean Type Theory](https://github.com/digama0/lean-type-theory)

## SPtr Refactor Status (2026-04-15)

**Branch**: `joachim/sptr-refactor`

**Completed**:
- SPtr type: `(CorePtr, u16)` — shift-in-pointer, no Shift DAG nodes
- Expr enum: Shift variant removed, fvar_lb removed, children changed to SPtr
- Only Var(0) in DAG; de Bruijn index carried in SPtr.shift
- mk_app/mk_pi/mk_lambda/mk_let/mk_proj extract min_shift for OSNF
- view_sptr replaces view_expr (full traversal for binder bodies)
- unfold_apps returns (SPtr, SmallVec<[SPtr; 8]>)
- All caches store SPtr values; defeq caches use SPtr keys
- Local context stores SPtr types
- Parser builds SPtr children, only Var(0) in DAG
- inst/inst_beta SPtr fast paths for dead substitutions

**Test status**:
- Tutorial: 126/126
- Init: 0 errors, 238B instructions (+0.8% vs 236B baseline)
- Mathlib: 0 panics (pending perf verification)

**Key bug found (2026-04-15)**: The def_eq union-find was unsound for open
expressions with SPtr. The UF was not depth-stacked, so unions proven at one
depth (where specific context entries were equal) would persist at other depths
where those context entries differ. With Shift DAG nodes this was hidden because
each (Shift, ExprPtr) combination was a unique DAG node. With SPtr, different
cores can represent the same expression at different shifts, and the UF union
would incorrectly equate cores that are only def_eq at specific depths.
Fix: restrict UF to closed expressions only (nlbv == 0).
- **Recursor types** (3 tests): sortElimProp2, accRec, reduceCtorParam

### SPtr Refactor Update (2026-04-15)

**Test status**:
- Tutorial: 126/126 (100%)
- Init: 54086/54086, 0 errors, 243B instructions (baseline 236B, +3%)
- Mathlib: 14 panics out of ~630K declarations (0.002% failure rate)
  - Down from 67 after sptr_shift fix in peel paths
  - Performance regression on some declarations (heartbeat threshold hits)

**Key fix**: Using `sptr_shift` (nlbv-aware) instead of `shift_up` in peel paths
prevents meaningless shift accumulation on closed expressions. 53 of the 67
Mathlib failures were caused by this.

**Remaining 14 failures**: peel mechanism corrupts context when processing
open expressions from view_sptr with OSNF structural shifts. Fix TBD.

**Remaining performance issue**: Some declarations hit heartbeat thresholds
that didn't before, suggesting cache efficiency regression.
