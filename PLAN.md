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

### Shift nodes (delayed shifting)

`Shift { inner, amount: u16 }` expression variant wraps expressions for O(1) shifting.
OSNF invariant: `inner.fvar_lb == 0`, `amount > 0`. No cutoff field, no negative amounts.
Nested shifts are impossible (inner can't be Shift since inner.fvar_lb == 0).

- `mk_shift(inner, amount: u16)`: creates wrappers, collapses nested Shifts, elides on
  closed expressions, eagerly forces `Var(k)` → `Var(k+amount)`. Enforces OSNF: if inner
  has fvar_lb > 0, normalizes to core first.
- `push_shift_up(e, amount)`: pushes Shift one level into constructor (cutoff=0).
  Non-binder children: `mk_shift(child, amount)` (O(1)).
  Binder bodies: `shift_expr(body, amount, 1)` (traversal, cached).
  App: recurses into `fun`, Shift-wraps `arg`. Allocates directly (bypasses mk_app OSNF).
  Pi/Lambda: delegates to `mk_pi`/`mk_lambda` which enforce OSNF — result may be Shift-wrapped.
- `view_expr(e)`: transparently sees through Shift nodes via `view_expr_shifted`.
  Never returns `Shift` variant; children may be Shift-wrapped. Used throughout TC, inductive
  checking, and def_eq for all pattern matches on compound constructors.
- `shift_expr(e, amount, cutoff)`: full traversal for cutoff > 0. Cached via shift_cache.
  Rebuilds via mk_* constructors, producing OSNF results.
- **fvar_lb optimization**: In `shift_expr_aux` and `push_shift_down_cutoff`, when
  `fvar_lb >= cutoff`, all free bvars are above the cutoff, so the cutoff is irrelevant.
  Converts to O(1) cutoff=0 path (mk_shift or Shift adjustment) instead of full traversal.
  Critical for avoiding O(depth) recursion on deeply nested binder chains.

**Shift composition in inst_aux**: When `inst_aux` carries pending shift `(sh_amt, sh_cut)`
and encounters `Shift(inner, amount, cutoff)`, it composes the shifts directly when
`cutoff < sh_cut && amount >= (sh_cut - cutoff)`, avoiding intermediate Shift creation.
This captures ~100% of first-level binder mismatches and repeats at every binder depth.

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

All caches are keyed by `ExprPtr` (pointer identity via hash-consing). No semantic
equality verification needed — pointer equality is exact.

Each expression stores `fvar_lb: u16` (lower bound on free bvar indices). Caches use
depth-indexed frames: `bucket_idx = depth - fvar_lb`. Bucket 0 holds closed expressions
(never evicted); higher buckets are pushed/popped with local context.

**WHNF cache**: `FxHashMap<ExprPtr, ExprPtr>` per depth bucket. Shift-peels top-level
Shifts before lookup (shift-equivariance).

**Infer cache**: Separate check/no-check maps per depth bucket. Check entries serve
both Check and InferOnly queries.

**DefEq cache (closed)**: `FxHashSet<(ExprPtr, ExprPtr)>` for positive results.
`UnionFind<ExprPtr>` provides transitive equality in O(α(n)).

**DefEq cache (open)**: Per-depth positive/negative stacks (LazyMap per frame).

### OSNF (Outermost-Shift Normal Form) — everywhere

Every expression in the DAG is in exactly one of these forms:
1. **Var(n)**: variable reference
2. **Core compound** (App, Pi, Lambda, Let, Proj, Sort, Const, Lit): always `fvar_lb = 0`
3. **Shift(n, core)**: `n > 0`, `core.fvar_lb = 0`

No negative shifts. No cutoff field on Shift. No compound expressions with `fvar_lb > 0`.
Pointer equality is reliable: same structural expression → same pointer.

**Enforcement**: Both at parse time and during TC. The `mk_app`/`mk_pi`/`mk_lambda`/
`mk_let`/`mk_proj` constructors all check `fvar_lb` after computing it from children.
If > 0, they extract a core (adjusting children down via `adjust_child_tc`) and wrap in
`Shift(fvar_lb, core)`. `adjust_child_tc` is O(1) per child under OSNF since children
with `nlbv > cutoff` must be `Shift(k, core)` or `Var(j)` with `k, j >= amount`.

**view_expr migration**: All code that pattern-matches expression constructors (Pi, Lambda,
App, Proj) must use `view_expr` instead of `read_expr`, since OSNF wraps open expressions
in Shift nodes that `read_expr` doesn't see through. This applies to:
- `inductive.rs`: get_local_params, check_ctor, sep_nonrec_rec_ctor_args, etc.
- `nanoda_tc.rs`: infer_lambda, infer_pi, infer_app, def_eq_binder_aux, etc.
- `tc.rs`: ensure_pi, whnf_no_unfolding_aux, def_eq_binder_multi, def_eq_proj, etc.
- `expr.rs`: abstr_aux_body, abstr_aux_levels_body, pi_telescope_size

**Fixpoint issue**: `push_shift_up(core_Pi, k)` can produce `Shift(k, core_Pi)` — the
same expression — when OSNF normalization in mk_pi re-wraps the result. Code that forces
Shifts via push_shift_up and then matches via read_expr must instead use `view_expr` to
avoid infinite loops.

**Parse-time core extraction**: During parsing, `adjust_child(child, fvar_lb, cutoff)`
extracts cores. Uses `expr_remap: Vec<usize>` for sequential-to-DAG index mapping.

**Results** (parse-time + TC enforcement, Init benchmark, single-thread):
- 2.9M of 5.7M parser expressions normalized, 10% core dedup → 7.8M DAG entries
- **Init: 26.7s vs nanoda 34.0s (22% faster), 587MB vs 471MB (+24% memory)**
- Parse-time only (full Mathlib): 47M of 88M normalized, -7% time, +18% RSS

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

When inst_aux detects all free bvars are past the substitution range
(`fvar_lb >= offset + n_substs`), delegates to persistently-cached
`push_shift_down_cutoff(e, n_substs, offset)` instead of traversing. Guard:
`n_substs >= 4` (lower thresholds regress due to HashMap overhead outweighing savings).
Fixed worst outliers: #298261 from 11.5s to 830ms, #357120 from 2.3s to 85ms.

### OSNF dead-substitution in inst_aux_quick and inst/inst_beta

Under OSNF, `fvar_lb` directly tells us the minimum free variable index. When
`fvar_lb >= offset + n_substs`, ALL substituted variables are dead — no variable gets
substituted. This is O(1) for Shift and Var nodes (push_shift_down or identity).

Three levels of the check:
1. **inst_beta/inst top level**: if `fvar_lb(e) >= n_substs`, short-circuit before entering
   inst_aux entirely. For inst_beta: `push_shift_down(e, n_substs)`. For inst: return `e`.
2. **inst_aux_quick sh_amt==0**: on per-depth cache miss, check fvar_lb. Catches all Shift
   children in single-arg beta reduction (the common case), since Shift implies fvar_lb ≥ 1.
3. **inst_aux_quick sh_amt>0**: when `fvar_lb > sh_cut`, compute effective_fvar_lb and check.

Also: `expr_fvar_lb: Vec<u16>` parallel array (like `expr_nlbv`) for O(1) fvar_lb access
without reading the full Expr. inst_cache enlarged from 4096 to 64K entries.

**Impact**: Declaration #272519 from 48.5s → 28.5s (41% faster). inst_aux calls 398M → 280M.
Full Mathlib panics: 6 → 5 (borderline declarations still ~28-30s vs 30s timeout).

### Pre-peel cache for infer/whnf/wnu

Before peeling Shift(core, n) at depth d (expensive split_off/extend), check if core's
result is already cached at the inner depth d-n. If so, shift the cached result and return
without peeling. Eliminates >99% of infer/whnf peels and 67% of wnu peels.

### inst_aux_quick fast path

Inlined `#[inline(always)]` wrapper that checks nlbv and fvar_lb early exits before calling
the full inst_aux (which involves stacker::maybe_grow + cache lookup). Avoids ~24M+ function
calls for trivial cases (closed expressions, nlbv below offset, dead substitutions).

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

- **OSNF everywhere (including TC-generated expressions)**: Use OSNF even for TC-generated
  expressions, not just parser expressions. Without this, pointer equality doesn't work
  reliably (same structural expression can have different pointers if fvar_lb differs).
  This is the most likely fix for the memory regression — cache misses cause repeated
  computation, which creates more TC DAG entries.

- **SExprPtr instead of Shift constructor**: Replace the Shift expression variant entirely
  with a shifted pointer type `SExprPtr = (ExprPtr, u16)` used in recursive Expr positions.
  An `Expr` is always a core expression. Benefits:
  - Less allocation for Shift nodes (no DAG entries for Shifts)
  - Fewer entries in the DAGs
  - Caches only cache core expressions anyway

- **Optimize view_expr usage**: Don't use view_expr when only checking closed constructors
  (Sort, Const, NatLit) — these can never be Shift-wrapped, so read_expr suffices.
  Use `is_app_of_const(e, name, arity)` pattern (peel Shift+App via read_expr without
  pushing shifts) instead of view_expr chains for simple head-const checks.
  Cache unfold_apps results for heavy declarations (lazily allocated, like mk_app DM cache).

- **fvar_lb removal**: If all expressions are in OSNF, then fvar_lb is derivable:
  - Var(k) → fvar_lb = k
  - Shift(n, core) → fvar_lb = n (core has fvar_lb = 0)
  - Core compound → fvar_lb = 0
  So fvar_lb could be removed as a stored field, shrinking Expr.

- **Depth-stacked UF for def_eq**: DONE. Cross-shift weighted UF with per-depth buckets
  in DepthFrame. Unions for closed expressions go to bucket 0; open expressions to
  `depth - shift`. The `uf_find` method follows chains across buckets via `sptr_shift`.

- **Lazy frame invalidation**: DONE. On `pop_local`, frames are hidden (depth counter
  decremented) rather than destroyed. On `push_local`, if a hidden frame exists with
  matching binder type, it is reused with all its caches intact. This gives the same
  cache reuse as nanoda's flat DbjLevel cache for the common pop-all/push-all-same
  pattern (e.g., checking a declaration's type then its value traverses the same binders).
  Verified on `instHPow`: frame reuse enables the exact same infer cache hit that
  nanoda gets with its flat cache.

- **MAXINT shift for closed expressions**: Use `u16::MAX` as the SPtr shift to indicate
  "closed expression". This makes closed detection O(1) from the shift alone (check
  `shift == u16::MAX`), and `min` operations naturally work (`min(MAX, k) = k`).
  Requires careful handling in shift arithmetic to avoid overflow.

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
