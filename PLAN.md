# lean-slop-kernel

Forked from [nanoda_lib](https://github.com/ammkrn/nanoda_lib) (Rust Lean 4 type checker).

**Goal**: Replace locally-nameless binding with pure de Bruijn indices + shift-homomorphic
caching. Avoid the expensive substitution on binder entry while retaining cross-depth
cache hits via shift-invariant keys.

## Design (changes from vanilla nanoda)

### Pure de Bruijn (no locally nameless)

Vanilla nanoda substitutes `bvar(0)` with a fresh fvar on binder entry (full traversal).
We use a local context array with `push_local`/`pop_local` (zero allocation).

- `inst` split into `inst` (no shift-down) and `inst_beta` (shift-down for beta/let/Pi)
- `inst_aux` shifts substitution values under binders
- `lookup_var` retrieves types from `local_ctx[depth - 1 - idx]` and shifts to current depth
- Unified infer cache (see Shift-invariant hashing and caching section)
- `inductive.rs`/`quot.rs` still use old Local approach (works correctly)

### Shift nodes (delayed shifting)

`Shift { inner, amount, cutoff }` expression variant wraps expressions for O(1) shifting.
Semantics: free Var indices in `inner` with index >= `cutoff` are shifted up by `amount`.
This is exactly a deferred `force_shift_aux(inner, amount, cutoff)`.

- `mk_shift` (cutoff=0): creates wrappers, collapses `Shift(Shift(e, j, 0), k, 0) → Shift(e, j+k, 0)`,
  elides on closed expressions, eagerly forces `Var` (O(1))
- `mk_shift_cutoff`: general version with cutoff parameter. Collapses when cutoffs match:
  `Shift(Shift(e, j, c), k, c) → Shift(e, j+k, c)`. Cannot collapse different cutoffs.
- `push_shift(e, amount, cutoff)`: pushes shift one level into constructor.
  App → recurses on both `fun` and `arg`: `App(shallow(fun), shallow(arg))`.
  This ensures the entire App spine AND all args are shift-free (real constructors),
  with Shift wrappers only on grandchildren. O(spine_length) work.
  Lambda/Pi → `Lambda(Shift(ty, k, c), Shift(body, k, c+1))` — fully lazy, no traversal.
  This is the key advantage of cutoff: binder bodies get `cutoff+1` instead of requiring
  a full `shift_expr(body, amount, cutoff+1)` traversal.
- `fvar_shift_cutoff`: shifts FVarList entries >= cutoff by k. Walks to the cutoff point,
  adds k to first entry >= cutoff, shares tail. O(1) for cutoff=0, O(position) for cutoff>0.
- `infer_inner` handles cutoff=0 Shift without forcing via context-shrinking. For cutoff>0, shallow-forces first.
- whnf/whnf_no_unfolding peel cutoff=0 Shifts iteratively; shallow-force cutoff>0 Shifts.
  Must also shrink local_ctx (save/restore) because whnf can indirectly call infer
  (via reduce_rec → to_ctor_when_k).
- `shift_eq` handles Shift nodes where the Shift's cutoff matches the comparison cutoff.
  Amounts are additive: `shift_eq_aux(Shift(e, k, c), b, delta, c)` checks `shift_eq_aux(e, b, delta+k, c)`.
  Works because `push_shift` creates `cutoff+1` on binder bodies and `shift_eq_aux`
  increments its cutoff under binders in sync.
  **Mismatched cutoff handling** (both sc < cutoff AND sc > cutoff):
  - **Fast path**: When `fvar_lb(inner) >= max(sc, cutoff)` (all vars above both cutoffs), the
    shift only affects free variables and is equivalent to `Shift(inner, amount, cutoff)` — safely
    absorbable into the delta. Handles the vast majority of cases.
  - **General path** (`shift_eq_pending`): For the remaining cases where `fvar_lb < max(sc, cutoff)`,
    uses a two-layer "BiShift" representation per side. Each side carries pending shifts
    `(amt1, sc1, amt2, sc2)` representing `shift(shift(e, amt1, sc1), amt2, sc2)`. Variable indices
    are computed by applying both layers. Under binders, all `sc` values increment. Nested Shifts
    are absorbed by composing with the inner layer (works when cutoffs match or the inner shift
    lifts past the outer's cutoff). Conservative false only when three distinct cutoff levels
    would be needed (extremely rare in practice).
  - **Impact**: #134719 above-depth VFs: 207K → 299 (all remaining are genuine hash collisions).
    #334175: ~1M → 1. #63709: 9654 (all genuine collisions, confirmed by mk_shift + sem_eq check).

**Current state**: whnf uses `push_shift` on results from both the direct
Shift-peeling path and the shift-invariant cache hit path for ALL result types
(including App). This is possible because `push_shift` recurses into App's
`fun` and `arg`, ensuring the entire App spine and all args are real constructors
(not Shift wrappers). Only grandchildren of the spine nodes carry Shift wrappers.
No full traversal (`force_shift_aux`) needed in the whnf cache hit path.

`unfold_apps` returns lazy (Shift-wrapped) args: accumulates cutoff=0 shifts through the App
spine and wraps each arg with `mk_shift` instead of full traversal. O(n_args) instead of
O(n_args × expr_size). `inst_aux` uses `mk_shift(val, offset)` for substitution values —
fully lazy, no forcing needed since all comparisons use `sem_eq`.

`view_expr(e)` is a view function that transparently handles Shift nodes: returns `Expr<'t>`
with Shift pushed one level inside via `push_shift`. Never returns `Shift` variant;
children may be Shift-wrapped. Replaces the common `force_shift(e); match read_expr(e)` pattern.
Used by: `unfold_apps_fun`, `unfold_apps_stack`, `inst_forall_params`, `infer_app`, `subst_aux`,
`inst_aux`, `shift_expr_aux`, and all whnf-result consumption sites (ensure_sort, ensure_pi,
infer_sort_of, reduce_proj, strong_reduce, iota_reduce_recursor, reduce_quot, is_sort_zero,
try_eta_expansion_aux, get_bignum_from_expr, get_bignum_succ_from_expr).

`force_shift_aux` has been deleted. All shifting uses `mk_shift` (O(1) wrapper) or
`push_shift` (one-level push). `inst_aux` uses `mk_shift(val, offset)` for
substitution value shifting — fully lazy, no traversal.
`push_shift` handles nested Shift with mismatched cutoff via two sequential
shallow forces.

### sem_eq (replaces canon_eq and pointer equality)

`sem_eq(a, b)` = `shift_eq_aux(a, b, 0, 0)` — structural walk that transparently handles
Shift wrappers by accumulating deltas. No allocation, no new node creation. Replaces all
pointer equality (`==`) and `canon_eq` comparisons throughout the system.

Used in: `def_eq_quick_check`, all cache collision guards (eq_cache, failure_cache,
defeq_open_lookup), whnf/whnf_no_unfolding cache hits, infer cache hits,
`try_unfold_proj_app`, `strong_reduce`, `def_eq_nat`.

`shift_eq_aux` handles Shift on the b-side when `amount > delta` by reversing the
comparison: `shift(a, delta) == shift(inner_b, amount)` iff `shift(inner_b, amount - delta) == a`.
Still used for cross-depth shift-invariant cache lookups (delta > 0).

All deep shift resolution code has been removed: `canonicalize`, `canon_eq`,
`resolve_shifts`, `resolve_shifts_aux`, `peel_shifts`, `canon_cache`, `canon_degraded`,
`sem_eq_cache`. The system uses only `sem_eq` (non-allocating structural walk) for
equality and `shift_eq` for cross-depth cache reuse.

### Lazy zeta in whnf Let case

whnf_no_unfolding_aux handles `Let { val, body, .. }` lazily: pushes the let-binding
onto local_ctx, reduces the body in the extended context, pops, then `inst_beta(result, [val])`
on the much smaller whnf result. This avoids unbounded inst_beta growth on deeply nested lets.

When whnf encounters `Var(k)` pointing to a let-binding (`lookup_var_value`), it performs
zeta reduction: unfolds to the shifted let value and continues reducing.

**Cache soundness**: With zeta reduction, `whnf(Shift(e, k)) ≠ Shift(whnf(e), k)` when
shifted vars point to different let-bindings. The whnf and wnu caches use fvar_lb-based
bucketing (like the infer cache): `bucket_idx = depth - fvar_lb`. Expressions at different
depths land in the same bucket only if they reference the same context range. Cross-depth
hits use `shift_eq(stored, query, depth_delta)` and return `push_shift(result, delta, 0)`.
This is sound because Shift peeling shrinks context to the stored depth, making let-bindings
above that depth irrelevant. The `context_range_is_let_free` guard has been removed.

`whnf_no_unfolding_aux` uses `view_expr` for the Lambda body-collection loop (handles
Shift-wrapped bodies from `push_shift` results) and `push_shift` in the
Shift arm.

### Shift-invariant hashing and caching

Each expression stores `struct_hash: u64` — a purely structural hash: tag + children's
struct_hashes + binder_name/style. Bvar indices are replaced by a constant (VAR_HASH),
so shifted expressions share the same struct_hash. No per-child deltas or normalized
fvar hashes are mixed in — those were removed as unnecessary (FVarList handles
shift-invariant discrimination).

**FVarList** (delta-encoded free variable set): Replaces the old `bvar_mask: u64` which
aliased at binder depth ≥ 64. Stores the sorted set of free bvar indices as a
delta-encoded linked list: `{0, 3, 7}` → `[0, 2, 3]` (head = lb, subsequent = gaps - 1).

- `shift k`: increment head → O(1)
- `unbind`: decrement head (or pop if 0) → O(1)
- `normalize`: set head to 0 → O(1), shift-invariant canonical form
- `union`: merge two delta lists → O(n+m), shared tails give O(1) common case
- **No false negatives at any depth** (proved in Theory.lean)

Canonical hash = `(struct_hash, normalized FVarList hash)`.

**WHNF cache**: fvar_lb-based bucketing (`bucket_idx = depth - fvar_lb`). Keyed by
canonical hash; on hit, verify with `sem_eq` (same-depth) or `shift_eq` + `push_shift`
(cross-depth, delta = `depth - stored_depth`). Cache entries store `(input, result, stored_depth)`.
Prefers lower stored_depth (more reusable across depths).

**2-slot overflow cache**: When different shift-families collide on the same canonical hash,
the primary HashMap stores one family and a separate overflow HashMap stores the second.
On store, `shift_eq` determines whether a new entry belongs to the primary's family; if not,
it goes to overflow. On lookup, primary is tried first, then overflow. This eliminates
verify_fails on pathological cases without regressing Init (overflow map is rarely populated
for non-pathological declarations).

**Cache hit promotion (replace primary)**: After a successful **same-depth** shift_eq-verified
cache hit where `stored_input != query`, replace the primary slot with `(query, result, depth)`.
This enables future lookups with the same ExprPtr to hit via ptr_eq without needing the
expensive shift_eq tree walk. **Critical: on above-depth hits, do NOT replace the primary.**
Replacing with a higher-depth entry loses the low-depth canonical entry that whnf_cache_store
deliberately preserves (prefers lowest depth for maximum cross-depth reuse). This caused
catastrophic cascading misses on commBialgCat (3 timeouts, 26s parent → 2s after fix).
Applied to both whnf and infer caches (primary hit path only; overflow hits are not promoted).
- Original promotion: #134719: 78s → 70s (10-11% improvement), Init: 32s → 30s (6-9%)
- Above-depth fix: commBialgCat parent 26s → 2s, overall 350K: 1315s → 987s

**Below-depth cache hits (infer only)**: When `depth < stored_depth`, we use reverse
`shift_eq(query, stored, delta)` to detect that the query is a shift-down of the stored
entry. On hit, `push_shift_down(result, delta)` subtracts `delta` from free variable
indices in the result. Precondition: `fvar_lb(result) >= delta` (always holds when the
stored entry was computed at a deeper context).

**Important**: below-depth hits are ONLY used for the infer cache, NOT for whnf/wnu caches.
`push_shift_down` does a full O(result_size) traversal, creating new expressions at every
level. For whnf results (which can be arbitrarily large), this is catastrophically expensive:
700M+ alloc_expr calls on Mathlib declarations with complex types. Infer results (types)
are typically small enough that push_shift_down is acceptable. On Init, below-depth infer
hits eliminate 95K-104K verify_fails per declaration (1.5s total improvement).

**whnf_no_unfolding cache**: same fvar_lb-based bucketing and cross-depth shift_eq pattern
as the whnf cache. Also peels top-level Shifts (shift-equivariance) before cache lookup.
Uses inline 2-slot entries: each HashMap value stores `(primary, Option<overflow>)` to
handle shift-family collisions without a separate overflow HashMap. On store, uses
depth-based replacement without shift_eq family check (avoids overhead in the hot store
path). A previous attempt with a separate overflow HashMap regressed Init by 7% due to
per-store overhead; the inline approach has zero overhead when overflow is None.
On #63709 (93s): 2524 overflow hits, 31% fewer verify_fails, 5.4% wall time improvement.
On #179806 (103s): 83K overflow hits from 117K overflow stores.

**Infer cache**: unified stack of maps. Bucket 0 holds closed expressions (never evicted).
Buckets 1..depth hold open expressions, indexed by `bucket_idx = depth - fvar_lb`.
Each map keys by canonical hash → (stored_input, stored_result, stored_depth, checked).
`checked=true` entries (from Check pass) serve both Check and InferOnly queries;
`checked=false` entries only serve InferOnly. On hit, verify with `shift_eq`, apply
delta via `mk_shift`. Stack push/pop follows `push_local`/`pop_local` for O(1) eviction.
Replaces the old three-cache design (infer_cache_check, infer_cache_no_check, infer_open_cache).
Also has a 2-slot overflow HashMap (same pattern as whnf cache) for shift-family collisions.
On #334175, this reduces infer verify_fails from 1.81M to 1,426, cascading into 23% fewer
infer calls, 28% fewer whnf calls, and 21% fewer inst_aux traversals.
Entries in shallow buckets survive push/pop of deeper context entries (correct, since
they only depend on the unchanged shallow context). If an entry was stored at a deeper
depth than the current query, we cannot reuse it (would need an "unshift"/shift-down
operation we don't have); instead we recompute and store at the lower depth, which
then serves as the base for future shifted lookups.

**DefEq cache (closed expressions)**: `eq_cache` and `failure_cache` use
`FxHashMap<((u64,u64),(u64,u64)), (ExprPtr, ExprPtr)>` — canonical hash pair as key,
stored ExprPtrs verified via `sem_eq`. Additionally, a pointer-based `UnionFind<ExprPtr>`
(`eq_cache_uf`) provides transitive equality: if A=B and B=C are proven, A=C resolves in
O(α(n)) without a direct cache entry. `check_uf_eq` is query-only (no insertion on lookup).

**Shift-aware UF**: When proving def_eq(x, y) where both are Shift nodes with matching
amounts (Shift(xi, k, 0) and Shift(yi, k, 0)), also union(xi, yi). On lookup, if both
query expressions are Shift nodes with matching amounts, check UF on inner expressions.
Sound because Shift(a,k,0) = Shift(b,k,0) iff a = b. Guard is `matches!((read(x), read(y)),
(Shift, Shift))` — zero overhead for non-Shift pairs (Init), effective for shift-heavy
pathological declarations. Checked after open cache (cheaper checks first).

Results with shift-aware UF (cumulative with plain UF):
- #134719: 6.9K UF hits → 80.6s (was 86s with plain UF, 98s without UF) = 7% further improvement
- Init: 33.0s (neutral or slight improvement from baseline 34.0s)
- #63709: neutral (shift patterns don't match in this declaration)

**Shift node dedup**: `mk_shift_cutoff(inner, amount, cutoff)` returns the same ExprPtr for
repeated calls with the same arguments, via a `(ExprPtr, u16, u16) → ExprPtr` dedup table.
This enables pointer equality to succeed more often in cache verification (sem_eq's `a == b`
fast path), avoiding expensive O(tree_size) structural walks through shift_eq. Profile showed
57% of CPU time in shift_eq for pathological declarations. With dedup, 124K Shift nodes are
reused on #134719. Combined with a small sem_eq positive-result cache:
- #134719: 74.6s (was 80.6s) = 7.4% improvement
- #179806: 68.2s (was 72.9s) = 6.4% improvement
- Init: 30-32s (neutral)

**DefEq cache (open expressions)**: same stack-of-maps design as the infer cache.
Keyed by ordered pair of canonical hashes `((u64,u64), (u64,u64))`.
`bucket_idx = depth - min(fvar_lb(x), fvar_lb(y))` — uses the deeper (more recently
bound) of the two arguments. Separate positive (defeq_pos_open) and negative
(defeq_neg_open) stacks. On hit, verify with `shift_eq` for both sides of the pair.
Result is a boolean (no delta to apply). On init: ~39K shift-invariant hits out of
~913K open stores.

### Infrastructure

- `stacker` crate for dynamic stack growth (deep recursion on mathlib)
- 256 MB worker thread stack in `main.rs`
- Iterative `whnf_no_unfolding_aux` (was recursive, caused stack overflow)

## Results

### Correctness
- Passes all arena tests: app-lam, dag-app-binder, init (accept);
  constlevels, level-imax-leq, level-imax-normalization (correctly rejected)

### Performance

| Benchmark | nanoda (locally nameless) | lean-slop-kernel |
|-----------|--------------------------|------------------|
| Init (54k decls, 310MB) | 26s | 27s (1.04x) |
| app-lam N=4000 | 8.3s | 10ms (830x faster) |
| Mathlib (630k decls, 4.9GB) | **978s (16.3min)** | **1675s (27.9min), 1.71x, 0 timeouts** |
| Mathlib 100k-110k segment | 14s | 34s (2.4x) |
| Mathlib 300k-310k segment | 12s | 76s (6.3x) |
| ofPointTensor_SpecTensorTo (#134719) | 214ms | 67s (313x) |
| Ideal.comap_fiber... (#179806) | ~2s (est.) | 50s |
| ModuleCat.monoidalCategory._proof_4 (#63709) | 503ms | 19s (38x) |
| toPartialMap._proof_6 (pathological) | ~2s | 13.9s |
| nonempty_algHom (was pathological) | 67ms | 1.4s |

Note: Init was 29s before fvar_lb-based bucketing and infer below-depth hits.
After shift_eq cutoff fix (partial): Init 27s, #63709 19s (was 79s), #134719 67s (was 70s).
After general shift_eq_pending + sc>cutoff fix: Init 30s, #63709 16s, #134719 59s, #334175 8.5s (was 50s).
After inst_aux shift-skip optimization: #63709 15s, #134719 52.5s, #334175 8.5s.
  Key finding: 94% of variables in inst_aux shift path were not being substituted.
  The shift-skip optimization returns O(1) when shift pushes vars past subst range.
  Saves 35% of allocations for #134719, 41% speedup for #63709.
After shift_eq direct-mapped cache: #63709 5.6s, #134719 2.9s, #334175 7.0s.
  Key finding: shift_eq was doing 9.6B recursive calls (50% of CPU) due to DAG→tree
  explosion. 1M-slot direct-mapped cache reduces to 1M calls (9,570x reduction).
  #134719 went from 52.5s to 2.9s (18x speedup). Gap to nanoda now ~15x.
Previous Mathlib run (with canonicalize, before fvar_lb bucketing) had 213 timeouts.
Previous full Mathlib run (pre-promotion): 260min wall time, 46 timeouts.
Full Mathlib run (with cache promotion): **13962s (232.7min, 14.5x nanoda)**, 42 timeouts.
**10.6% faster** than pre-promotion baseline across the full run.
Milestone comparison vs pre-promotion (old → new): 50K: 94s→87s (8%), 200K: 3104s→2954s (5%),
300K: 7434s→6684s (10%), 400K: 10890s→9734s (11%), 500K: 13566s→12115s (11%), 629K: 15621s→13962s (10.6%).
Note: 100K shows 9% regression (566s vs 517s) — likely a single pathological declaration.
120 assert_def_eq panics (same in both old and new runs — pre-existing correctness issue, not caused by promotion).

**Latest full Mathlib run** (lazy push_shift + canonical entry preservation):
**~1675s (27.9min, ~1.75x nanoda), 0 timeouts, 0 errors.**
Milestone comparison (previous run → latest):
| Milestone | Previous | Latest | Improvement |
|-----------|----------|--------|-------------|
| 50K | 85s | 62s | 27% |
| 100K | 248s | 174s | 30% |
| 200K | 652s | 440s | 32% |
| 300K | 1094s | 790s | 28% |
| 350K | 1315s | 993s | 24% |
| 400K | 1997s | 1137s | 43% |
| 500K | 2404s | 1422s | 41% |
| 630K | ~3200s (est.) | ~1675s | ~48% |

The 43% jump at 400K reflects the commBialgCat and AlgGeom improvements.
Top 3 slowest: #272519 (30s), #272517/#334136/#426287 (18s each, same underlying proof),
#345976 (18s). Note: #272519 is 19% SLOWER than previous run due to the canonical entry
preservation — the old behavior of replacing with high-depth entries happened to work better
for this declaration's pattern (massive wnu calls on small DAG). Net effect is still very positive.

Profile (init, pre-deletion baseline, 375B instructions): `force_shift_aux` was the
dominant cost — shift cache had ~40% hit rate (8M hits, 12M misses). Now deleted;
all shifting uses `push_shift` (one-level push) or `mk_shift` (O(1) wrapper).

### Current profile (#134719, 2.9s after shift_eq cache)

Previous dominant bottleneck (shift_eq at 50%) eliminated by direct-mapped cache.
shift_eq_aux calls reduced from 9.6B to 1M (9,570x) via DAG-level memoization.

Pre-cache profile (52.5s):
| Function | CPU% | Note |
|----------|------|------|
| shift_eq_aux | 23.4% | tree walk through Shift wrappers |
| shift_eq_struct | 20.6% | structural comparison with delta/cutoff |
| shift_eq_pending | 5.6% | mismatched-cutoff BiShift comparison |
| hashbrown rehash | 3.9% | hash table resizing |
| IndexMap insert | 4.7% | alloc_expr dedup lookups |

Remaining bottleneck after shift_eq cache: inst_aux (11.5x nanoda) and alloc_expr (42x).
The 75.6M alloc_expr calls with 99.4% dedup rate are dominated by hash-and-lookup cost.

Operation count comparison (#134719, after shift-skip optimization):

| Metric | Nanoda | Shift-based | Ratio |
|--------|--------|-------------|-------|
| Time | 190ms | 52.5s | 276x |
| def_eq | 84,582 | 87,433 | 1.03x |
| whnf | 63,040 | 72,878 | 1.16x |
| infer | 97,526 | 106,738 | 1.09x |
| inst | 114,276 | 105,587 | 0.92x |
| alloc_expr | 1,791,251 | 75,602,103 | **42x** |
| inst_aux | 1,633,207 | 18,843,003 | **11.5x** |
| eq cache hits | 20,099 | 7,681 | 0.38x |

TC-level operations (def_eq, whnf, infer) are now essentially identical to nanoda.
The remaining gap is dominated by inst_aux (11.5x) and allocations (42x). The shift-skip
optimization reduced these from 17x/65x but significant overhead remains from:
- 54% of inst_aux calls still in shift path (sh_amt > 0), doing 4.6M structural allocs
- Push_shift creating Shift wrappers that inflate expression trees
- alloc_expr dedup cost: 99.4% dedup rate means 75M hash lookups to store 725K unique nodes

**Experiments that didn't help**:
- Identity check in subst_aux/abstr_aux/push_shift (children unchanged → skip rebuild):
  8% regression on Init due to branch overhead; children almost always change.
- Negative sem_eq cache (cache failing structural walks): 61K hits on #134719 but
  no measurable speedup; individual walks are too cheap.
- Pre-sizing DAG IndexSet to 4096: 8% regression on Init due to wasted allocation for
  small declarations.
- struct_hash early rejection in shift_eq_aux: 13% regression; most shift_eq calls are
  positive matches (expressions DO match), so the extra read_expr + hash is wasted.

## Design goal: match nanoda's cache behavior

Our checker should have **at least all the cache hits/reuse as nanoda**. The only
acceptable overhead vs nanoda is:
- More expensive hash computation (canonical hash rather than pointer identity)
- The cost of creating/carrying Shift wrappers

We should **not** be slower due to missed cache hits. If we are, we need to find and fix
the cache miss, not paper over it with heuristics (DAG size thresholds, degraded mode,
timeouts, etc.).

### WHNF cache collision problem (solved)

On pathological Mathlib declarations (e.g. #334175 `toPartialMap._proof_6`), the whnf cache
had massive hash collisions: 2.9M verify_fails with only 9K no_entry misses. The root cause:

- `canonical_hash = (struct_hash, fvar_normalize_hash)` is deliberately shift-invariant
- This means many different expressions map to the same hash key
- A single HashMap entry per key loses useful entries when different families collide

**Fix**: 2-slot cache with separate overflow HashMap. Primary map stores one shift-family,
overflow map stores a second colliding family. On store, `shift_eq` detects family membership
(with fast-path pointer equality). On lookup, primary is tried first, then overflow.

Results on #334175 `toPartialMap._proof_6`:
- whnf verify_fails: 2.89M → 0 (overflow stores: 77, hits: 1.09M)
- infer verify_fails: 1.81M → 1,426 (infer overflow also added)
- wall time: 29.8s → 17.1s (-43%)
- Init: no regression (29.0s)
- Cascade: 23% fewer infer calls, 28% fewer whnf calls, 21% fewer inst_aux

The overflow HashMap is separate from the primary to preserve memory layout (cache locality)
for the common single-family case.

**nlbv_sign measurement** (sign of nlbv(child1) - nlbv(child2) for App/Pi/Lambda — shift-invariant
1.6-bit discriminator): Instrumented both whnf and infer verify_fail paths on #134719.
Results show nlbv_sign is ineffective — but the verify_fails it was measured against turned out
to be mostly mismatched-cutoff Shift failures (not true hash collisions). After the shift_eq
cutoff fix, above-depth VFs dropped from 207K to 303, making the original measurement moot.
The remaining VFs are a mix of true hash collisions and below-depth shift variants.

**No shift resolution**: The whole point of Shift nodes is to avoid traversals.
We use `sem_eq` (non-allocating structural walk) for all equality comparisons — no deep
canonicalization or shift resolution anywhere. All deep shift resolution code has been
removed (`canonicalize`, `resolve_shifts`, `canon_cache`, etc.). The `struct_hash` is
shift-invariant by design (Shift nodes inherit their inner's struct_hash), so canonical
hashes match for shifted and unshifted versions.

**Approach**: Add tracing/instrumentation to both nanoda and our checker to compare cache
hit rates side-by-side. nanoda's TC code is included in this project (module `nanoda_tc`)
with a runtime flag to switch between checkers, making A/B comparison easy.

### Tracing results (declaration #122833: colimitLimitToLimitColimit_surjective)

| Counter | Shift TC (10s timeout) | Nanoda (82ms) |
|---------|----------------------|---------------|
| def_eq | 13,637 | 13,924 |
| whnf | 2,447 | 2,942 |
| infer | 16,440 | 15,695 |
| inst/inst_beta | 15,887 | 17,941 |
| infer cache hits | 12,386 | 11,707 |
| whnf cache hits | 2,179 | 2,560 |
| eq cache hits | 1,432 | 1,650 |
| inst_aux nodes | 1,724,533 | ~1.8M (est.) |
| canonicalize calls | 109,383 | N/A |
| push_shift calls | 122,175 | N/A |
| DAG growth | 69K→234K | ~0 |

**Conclusion**: TC-level operation counts are comparable. Cache hit rates are comparable
(infer hits even slightly better than nanoda). The bottleneck is **per-operation overhead**:
- `inst_aux` with Shift handling (view_expr→push_shift) vs nanoda's plain read_expr
- `canonicalize` traversals for cache verification (canon_eq) and whnf result normalization
- `alloc_expr` HashMap lookups on the growing TcCtx DAG (69K→234K new expressions)
- 93% of heartbeats are in inst_aux (substitution traversal)

**Key insight**: the Shift approach has fundamentally higher constant factor per operation.
Each node visit in inst_aux does: check_heartbeat + inst_cache lookup + view_expr (which may
push_shift on Shift nodes) + alloc_expr. Nanoda does: read_expr + match + recurse. Reducing
the number of operations (better caching at higher levels) is more impactful than optimizing
each operation.

### Combined inst_shift_aux optimization

`inst_aux` now carries pending shift parameters `(sh_amt, sh_cut)` instead of creating
intermediate Shift wrapper expressions when distributing shifts to children. When encountering
`Shift { inner, amount, cutoff }`, it recurses on `inner` directly with the shift params.

| Metric (init 54k decls) | Before | After | + nlbv canon skip |
|--------------------------|--------|-------|-------------------|
| Wall time | 54s (2.1x nanoda) | 33s (1.27x) | 31s (1.19x) |

| Metric (#122833, 10s timeout) | Before | After |
|-------------------------------|--------|-------|
| alloc_expr at timeout | 1,386K | 1,044K |
| inst_aux work nodes | 936K | 938K |
| Progress (def_eq) | 13,867 (~95%) | 13,867 (~95%) |

The optimization reduces alloc_expr calls (~25% fewer intermediate Shift wrappers) but
doesn't reduce inst_aux traversal count — the shift TC still traverses ~4.8x more inst_aux
nodes than nanoda (938K vs 196K). This is fundamental: Shift wrappers in the expression tree
add layers that inst_aux must traverse through, even with the combined approach.

**Experiments that didn't help**:
- `canonicalize(result)` after inst_beta: 376K canon calls, only 37% progress at timeout.
  Deep canonicalization on every inst_beta result far exceeds the benefit of preventing cascading.
- `canonicalize(body)` before inst_beta: 444K canon calls, less progress per heartbeat.
  Even targeted pre-canonicalization adds too much push_shift overhead.
- Eager `shift_expr_aux(val, offset, 0)` instead of `mk_shift(val, offset)` in inst_aux Var case:
  Much worse (1.23M heartbeats at timeout vs 1.9M). Full traversal of substitution values is
  more expensive than the cascading lazy Shift wrappers.
- Unchanged-children check in inst_aux (avoid alloc when children unchanged): slightly slower
  due to comparison overhead outweighing the rare alloc savings.
- Skip export DAG lookup for Shift exprs in alloc_expr: slightly slower from matches! overhead.

**Root cause of 4.8x inst_aux gap**: Each inst_beta creates `mk_shift(val, offset)` wrappers
for substitution values under binders. These Shift wrappers cascade — subsequent inst_beta
calls must traverse through them, creating more wrappers. This is the fundamental cost of
deferred shifts. Nanoda's locally-nameless approach substitutes fvars that don't need shifting.

### Let-in-context (partial: lazy whnf Let only)

The kernel processes `let x := val in body` by substituting val for Var(0) in body
via `inst_beta`. For nested let chains, this creates O(N²) cascading substitution work
because each substitution must traverse Shift wrappers from previous substitutions.

**Let-in-context approach**: Instead of eager substitution, push `(type, Some(val))` onto
`local_ctx` and infer body at depth+1. When whnf encounters `Var(k)` pointing to a
let-binding, it performs "zeta reduction": unfolds to the shifted let value. After inference,
`inst_beta(result, [val])` brings the result type back to the caller's depth.

Infrastructure:
- `local_ctx` changed from `Vec<ExprPtr>` to `Vec<(ExprPtr, Option<ExprPtr>)>` (type + optional value)
- `lookup_var_value(k)`: returns shifted let-value if context position is a let-binding
- `push_local_let(ty, val)` / updated `pop_local()`: manage let entries in context
- Zeta reduction in whnf_no_unfolding_aux `Var` case: unfolds let-bound vars
- Stacked whnf/wnu caches: `Vec<FxHashMap>` with fvar_lb-based bucketing, invalidated on pop

**Fundamental blocker for infer_let**: Always-let-in-context in `infer_let` causes
8/54086 Init declarations to diverge (timeout at 30s). Root cause: `inst_beta(result, [val])`
after pop creates expressions that are genuinely structurally different from what eager
inference produces — NOT shift-variants. The wnu cache correctly identifies no shift
relationship (only 42 hits out of 44K calls with let-in-context infer_let). The official
Lean kernel avoids this because fvar-based zeta reduction returns the original `val`
pointer (no shifting), so reduction paths converge to the same DAG nodes.

**Current state**: `infer_let` uses eager `inst_beta(body, [val])`. The lazy zeta approach
in whnf Let case (push/pop/inst_beta on reduced result) works correctly and avoids
nested-let cascade. Together these handle all Init declarations.

| Benchmark | Eager infer_let + lazy whnf Let |
|-----------|--------------------------------|
| Init (54k decls) | 33s |
| shift-cascade N=1000 | ~2ms |

## TODO

- **Remove remaining dead code**: thread_local profiling counters, dead locally-nameless
  code (Local variant, FVarId, abstr, etc.)

- **Reduce TC-level operation count**: On the worst Mathlib declarations, the shift checker
  has 2.4x more def_eq calls, 4.7x more whnf calls, and 3.7x more inst calls than nanoda.
  These cascade: more def_eq → more whnf → more inst_beta → more expressions → lower cache
  hit rates → more def_eq. Breaking this cycle at any point helps.

  **inst_aux analysis** (#63709, 221M calls vs nanoda 3.2M = 68x):
  - Shift node traversals: 2.4M (1.1%) — NOT the bottleneck
  - Cutoff mismatches: 2.0M (86% of Shift traversals)
  - Cache hits: 79M (36%)
  - Early exit (elided): 24M (11%)
  - Real work nodes: 115M (52%) — expressions are genuinely larger
  The 68x gap comes from: 3.7x more inst_beta calls × 18.7x more nodes per call.
  The per-call overhead is from accumulated Shift wrappers inflating effective tree size.
  Each mk_shift(val, offset) in the Var case wraps val, and subsequent inst_beta calls
  must traverse through these wrappers.

  Ideas (not yet implemented):
  - Persistent inst_cache across inst_beta calls (include subst fingerprint in key)
  - Size-bounded eager shift (resolve small vals, defer large ones)
  - Avoid creating Shift wrappers for subst vals consumed by whnf
  - Improve def_eq/infer cache hit rates to reduce operation count at the source

- **Investigate fvar_lb computation overhead**: fvar_lb-based bucketing regressed Init
  from 29s to 33s. The fvar_lb computation on every cache access may outweigh the
  cross-depth hit benefit for Init. Profile and consider caching fvar_lb.

- **Optimize local context adjustments under shift**: When `infer` or `whnf` operates
  under a `shift`, the local context is temporarily adjusted (popping entries). The data
  structures aren't well-suited for this. Key improvements:
  - Skip local context adjustment entirely when there's a cache hit (the result is already
    shifted, no need to reconstruct the context).
  - Investigate better data structures for temporary local context/cache truncation (e.g.,
    persistent data structures, versioned contexts).
  - Consider whether caches and local context should live in the same data structure for
    efficient co-truncation.

- **Investigate always-let-in-context alternatives**: Current eager infer_let works but
  doesn't avoid O(N²) cascade for deep lets in infer. Options:
  - Accept the limitation (whnf lazy zeta already handles the cascade for reduction)
  - Find a convergence-preserving approach to Shift-aware let-in-context
  - Consider hybrid: de Bruijn + locally-nameless for let-bound vars only

- **Fill in Theory.lean sorry's**: `decode_shift`, `fvars_shift_zero`

## Lessons learned (things that didn't work)

- **Bitmask shift-invariance breaks at depth ≥ 64**: `bvar(0)` and `bvar(64)` alias to
  the same bit. Replaced with delta-encoded FVarList — no aliasing at any depth.

- **struct_hash without per-child deltas had too many collisions** (old bitmask era):
  all single-bvar expressions got `norm_mask = 1<<63`, so `app(bvar 0, bvar 1)` and
  `app(bvar 0, bvar 0)` had the same canonical hash. This was fixed by mixing
  `(bvar_lb_delta, bvar_ub_delta)` into struct_hash, but those deltas were later removed
  once FVarList replaced bitmasks — FVarList's normalized hash already distinguishes these
  cases. struct_hash is now purely structural (tag + children's struct_hashes).

- **`restore_depth` off-by-one caused exponential blowup**: the cache eviction in
  `def_eq_binder_aux` used `d < depth` instead of `d <= depth`, discarding valid entries
  at the current depth. This made app-lam O(2^n) instead of O(n).

- **Shift-wrapped App whnf results break via ExprPtr identity divergence**: Both
  `push_shift` and `mk_shift` on whnf cache results cause type errors for App
  results, but NOT for Pi/Lambda. The mechanism: `unfold_apps` decomposes the App spine,
  and Shift-wrapped args produce different ExprPtrs than fully-forced args. These different
  ExprPtrs cause different cache hit/miss patterns in downstream infer/def_eq code, which
  changes execution paths. The failure manifests at `Lean.Grind.Ring.intCast_nat_sub`
  (depth=9) via `proof_irrel_eq` receiving an expression with wrong variable references.
  Disabling eq_cache, failure_cache, or whnf_no_unfolding_cache individually does NOT fix it.
  Initial fix: only use push_shift for non-App whnf results; App results use
  force_shift_aux. Later resolved fully: making push_shift recurse into App's
  fun AND arg (see below) made it safe for all result types, and force_shift_aux was deleted.
  Note: `infer` successfully returns mk_shift results because infer results go through
  whnf (which forces Shifts) before reaching def_eq.

- **Metadata cost dominates on small workloads**: computing struct_hash + FVarList
  for every expression adds overhead, but shift hits only save ~1s on init. The break-even
  point needs larger workloads (mathlib) where shift hits accumulate.

- **Inlining mk_* into force_shift_aux made it worse** (375B → 382B): code bloat hurt
  icache. Similarly, adding an Option<u64> parameter for struct_hash reuse made it worse
  (375B → 385B) due to branch overhead on every mk_* call.

- **Shift-invariant shift cache causes infinite recursion**: Attempted keying the shift
  cache by `(canonical_hash, amount, cutoff)` instead of `(ExprPtr, amount, cutoff)`, with
  shift_eq verification + force_shift_aux(result, delta) on hit. Problem: the result of
  force_shift_aux has the same canonical hash as the input (struct_hash is shift-invariant!),
  so looking up the result in the cache finds the same entry, computing another delta,
  recursing infinitely → OOM. The whnf cache doesn't have this problem because whnf
  *reduces* expressions, changing the canonical hash. The shift cache can't benefit from
  shift-invariant keys because the operation itself preserves structural identity.
  The underlying issue is the same as shallowish force: to reuse shift results across
  depths, you'd need to return Shift-wrapped results, but inner Shift nodes break def_eq.

- **push_shift on whnf results WORKS for ALL types** (including App):
  Making `push_shift` recurse into App's `fun` AND `arg` (not just wrapping with
  mk_shift_cutoff) ensures the entire App spine and all args are real constructors. Only
  grandchildren carry Shift wrappers. This produces ExprPtrs consistent with fresh computation
  because unfold_apps → foldl_apps reassembly sees the same args. Key: recursing on `fun` alone
  was insufficient — Shift-wrapped args in foldl_apps output create different ExprPtrs that
  cascade through def_eq/eq_cache/failure_cache causing type errors.

- **Lazy unfold_apps requires companion fix**: `inst_aux` must shallow-force subst
  values, otherwise Shift wrappers propagate through inst_beta. Using `mk_shift` (fully lazy)
  was attempted but fails because `Shift(Lambda, k, 0)` and `Lambda(Shift_ty, Shift_body)`
  have different ExprPtrs despite being semantically equivalent, causing cache identity
  divergence throughout the system. `push_shift` is the minimum viable forcing level.

- **shift_eq must track binder depth**: The old shift_eq checked `j == i + delta` for all Var
  nodes, including bound vars inside Pi/Lambda bodies. This is wrong: bound Var(0) in a Pi body
  should compare as 0 == 0, not 0 == 0+delta. Fixed by adding a `cutoff` parameter that
  increments under binders. The old bug was masked because expressions rarely had Shift wrappers
  inside binder bodies (no push_shift on whnf results). The Shift handling in shift_eq
  was initially restricted to cutoff=0. Later generalized: Shift handling works for any cutoff
  matching the comparison cutoff (amounts are additive when cutoffs match). Mismatched cutoffs
  still fall back to false (conservative).

- **whnf/whnf_no_unfolding Shift stripping must shrink local_ctx**: Stripping top-level
  Shift wrappers for shift-equivariant processing is correct in principle, but whnf can
  indirectly call `infer` (via `reduce_rec → to_ctor_when_k → infer_then_whnf`) which
  depends on `local_ctx`. Without shrinking local_ctx before recursing, the inner
  expression's bvars reference wrong context entries, causing type mismatches (e.g.,
  structure type inferred as `Eq` instead of `ULift` in mathlib). Fix: save/restore
  `local_ctx` and depth-indexed caches when stripping Shifts, matching the pattern used
  in `infer_inner`. The original nanoda doesn't have this issue because it never creates
  Shift wrappers.

- **shift_eq in def_eq_quick_check works**: Adding `shift_eq(inner, other_side, amount)` for
  single-sided Shift comparisons is cheap (non-allocating) and correct. This makes def_eq
  robust against Shift-wrapped inputs from infer (which returns mk_shift results).

- **ExprPtr identity divergence requires sem_eq, not just cache fixes**: Replacing
  `force_shift_aux` with `mk_shift` in inst_aux initially failed even after making
  eq_cache/failure_cache shift-tolerant. The problem was pervasive: pointer equality
  (`==`) was used throughout the system — cache collision guards, whnf cache hits,
  def_eq_quick_check, try_unfold_proj_app change detection, strong_reduce, shift_eq_aux
  base cases. The fix: introduce `sem_eq` (semantic equality modulo Shift wrappers)
  and replace ALL pointer equality comparisons. Also required fixing shift_eq_aux to
  not short-circuit at delta=0, and adding b-side Shift handling for amount > delta.
  Once all comparisons became shift-transparent, mk_shift in inst_aux works and
  force_shift_aux was deleted entirely.

- **shift_eq_pending had no cache — exponential blowup**: `shift_eq_pending` (the bi-shift
  structural comparison for mismatched cutoffs) had no result cache, causing up to 17 billion
  calls on #122833 (85s!). These arise because cache verification via `shift_eq` encounters
  Shift nodes with mismatched cutoffs, falling into the uncached `shift_eq_pending` path.
  The same sub-expression comparisons are repeated exponentially through DAG sharing.
  Fix: add a direct-mapped cache (256K entries, lazily allocated to avoid 2MB zero-init
  per declaration). Results: #122833: 85s→5s (16x), #329219: 52s→31s, #89921: 4.0s→3.5s.
  The lazy allocation also fixed a 100s Init regression from the eager shift_eq_cache (1M
  entries × 16 bytes = 16MB zeroed per declaration).

- **Below-depth whnf cache matching is impractical**: `push_shift_down` on whnf results
  to reuse cached results at shallower depths costs more than recomputation. On algebraic
  geometry declarations with huge types, `push_shift_down` triggers 1B+ allocations.
  Even with `fvar_lb >= delta` safety check, traversal cost cancels savings. Only infer
  cache benefits from below-depth matching (types are smaller).

- **Eagerly resolving shifts is counterproductive**: All attempts to eagerly push/resolve
  shifts (push_shift in lookup_var, push_shift in inst_aux substitution values) made
  things worse because they create different expression identities that cascade poorly
  through downstream caches. #63709: 24% slower with push_shift in lookup_var.
  #134719: 9x slower (push_shift traverses huge AlgGeom type expressions).

- **Identity check in inst_aux shift path**: In the shift path of inst_aux, checking
  if children are unchanged (new_fun == fun && new_arg == arg) before allocating saves
  ~46% of shift path allocations. 11% overall speedup on #63709.

- **mk_app/pi/lambda memoization caches**: Adding (children) → ExprPtr caches skips
  expensive metadata computation (fvar_list, struct_hash, nlbv) and alloc_expr hash
  lookup on repeated calls. Huge win because 99.9% of alloc_expr calls are dedup hits.
  Results: #409494: 60s→29s (2x), #329219: 31s→11s (2.8x), #63709: 4.6s→2.6s (1.8x),
  #122833: 5.2s→2.3s (2.3x).

- **O(1) below-depth whnf cache matching works for simple results**: When a whnf cache entry
  exists at higher depth, we can reuse it at lower depth if the result is: (1) closed
  (depth-independent), (2) Shift(inner, k, 0) with k >= delta (subtract delta), or
  (3) identity (whnf was no-op, return query). Check adjustability FIRST (O(1)) before
  shift_eq verification. Init: 37.9s → 35.6s (6%).

### Current profile (full Mathlib benchmark, after shift composition)

| Declaration | Nanoda | Baseline | Pre-compose | Post-compose | Speedup | Notes |
|-------------|--------|----------|-------------|--------------|---------|-------|
| Init (54k) | 26s | ~38s | 35.6s | 32.2s | 1.18x | |
| #235200 AlgGeom.exists_eq | ? | 98,879ms | timeout | **476ms** | **207x** | shift composition eliminates 99% mismatch |
| #272519 AlgGeom.PartialMap | 10,753ms | 41,650ms | 26,024ms | **26,051ms** | ~1x | def_eq-heavy (27.7M calls), not shift-heavy |
| #329219 HopfAlgCat | 65ms | ~52,000ms | timeout | **6,179ms** | **>19x** | |
| #350525 commBialgCat._proof_10 | ? | 24,249ms | timeout | **788ms** | **>152x** | |
| #380722 Algebra.H1Cotangent | ? | timeout | timeout | **3ms** | ∞ | |
| #409494 AlgGeom.toNormalization | ? | timeout | timeout | **12,025ms** | ∞ | |

Previous pre-composition benchmark (134 timeouts). Shift composition fixed the 5 remaining timeout-class failures.

**Lazy zeta args-shift bug** (fixed): The `whnf_no_unfolding_aux` Let handler used
"lazy zeta" — pushing the let binding into context and reducing the body there. When the
Let was applied to arguments (via `unfold_apps`), the args' de Bruijn indices were NOT
shifted to account for the new let binder. This caused 120+ def_eq assertion failures
across Mathlib (e.g. `MeasureTheory.SimpleFunc.inst*`, `iInf_dite`, `OrderedFinpartition.*`).
Fix: shift args up by 1 with `mk_shift(a, 1)` before combining with the let body.

**Shift composition optimization** (implemented and benchmarked):
When cutoff < sh_cut and amount >= (sh_cut - cutoff), the two shifts compose into
a single (sh_amt + amount, cutoff). This eliminates the force_shift call entirely.
For the common case (cutoff=0, amount≥1, sh_cut=1), this captures ~100% of first-level
binder mismatches. The pattern repeats at every binder depth because composition resets
sh_cut to the inner cutoff (0), then the next binder increments it to 1, and the next
Shift(inner, amount≥1, 0) composes again.

**mk_var cache and direct-mapped mk_app cache** (implemented):
Profiling #298261 (PiTensorProduct.norm_eval_le_injectiveSeminorm) revealed 1.48B
alloc_expr calls dominated by 1.475B mk_var calls (no cache) and 2.47B mk_app calls
(FxHashMap cache hit overhead). Fix: added a per-index Vec cache for mk_var (O(1)
array lookup, eliminates 1.475B hash table lookups), and a 1M-entry direct-mapped
cache for mk_app (tag-based, lazily allocated after 10K misses to avoid 16MB
per-declaration overhead for small declarations). Results:
- #298261: 45.1s → 25.6s (1.76x speedup)
- Init 54K: 130s → 119s (slight improvement)
Per-function alloc breakdown (mka/mkv/mkp/etc.) counters added for future profiling.

**Remaining bottleneck: pointer identity divergence from nanoda.**

Root cause analysis: nanoda uses de Bruijn LEVELS (Local variables) to open binders,
while our TC uses de Bruijn indices directly. This fundamental difference means:
1. Nanoda's `inst` never needs shift_down (no binder removal changes variable indices)
2. Nanoda's inst_cache key is 2D (e, offset) vs our 4D (e, offset, sh_amt, sh_cut)
3. Nanoda has no Shift AST nodes, no push_shift, no shift_eq machinery
4. Nanoda's whnf cache achieves 99.997% hit rate because pointer identity is preserved

The cascade: Shift wrappers → pointer identity divergence → lower cache hit rates →
more whnf/infer calls → more inst calls → billions of mk_app/mk_var calls.

Quantified comparison (per declaration):
| Declaration | Our TC | Nanoda TC | Ratio | Key metric |
|-------------|--------|-----------|-------|------------|
| #228736 | 8.4s | 241ms | 35x | mk_var: 401M vs 227 |
| #170616 | 2.3s | 431ms | 5.4x | inst_aux: 6.1M vs 2.2M |
| #63709 | 1.2s | 416ms | 2.8x | whnf: 481K vs 120K |
| #272519 | 24.8s | 10.0s | 2.5x | fundamentally heavy (10s nanoda) |

Attempted fix: using push_shift_down for below-depth whnf cache hits (converting
24K verify fails into hits for #228736). Result: CATASTROPHIC regression from 8.4s
to 72s. The shifted-down results have different pointer identity from "naturally
computed" whnf results at the target depth, causing cascading cache misses downstream.
This confirms that the fix must be architectural (eliminate Shift nodes) rather than
incremental (adjust cached results).

The architectural fix would be switching tc.rs to use de Bruijn levels (Locals) like
nanoda_tc.rs. This is a major refactor touching most of tc.rs but could close the
2.5-35x gap vs nanoda.

**Incremental fix: lazy push_shift for App args.**
push_shift previously recursed into BOTH fun and arg of App nodes, traversing entire
expression trees. For #228736 (8.8s), this caused 401M mk_var calls from push_shift
traversals of above-depth cache results (sd=782K hits). Changed to only recurse into
fun (keeping the App spine visible for unfold_apps) and lazily Shift-wrap args. This
defers arg shift work to when the args are actually inspected (inst_aux, unfold_apps).
Expected savings: proportional to total arg subtree size (bulk of the 401M mk_var
calls). The commBialgCatEquivComonCommAlgCat family shows exponential growth of
push_shift calls (proof_5: 4K → proof_9: 1.1M → proof_11: timeout), making this
optimization critical for avoiding timeouts on algebraically complex declarations.

**Cache canonical entry preservation fix.**
On above-depth cache hits, the whnf and infer caches were replacing the primary slot
with (query, shifted_result, higher_depth). This lost the low-depth canonical entry
that `whnf_cache_store` deliberately preserves (prefers lowest depth for maximum
cross-depth reuse). The cascade: low-depth entry evicted → subsequent queries at
intermediate depths become verify-fails → full recomputation → exponential blowup.
Fix: only replace primary on same-depth hits (for pointer identity optimization),
not on above-depth hits. Combined with lazy push_shift, results:

| commBialgCat declaration | Old (pre-fix) | New (both fixes) | Speedup |
|--------------------------|---------------|------------------|---------|
| proof_7 | 91ms | 66ms | 1.4x |
| proof_8 | 251ms | 164ms | 1.5x |
| proof_9 | 749ms | 530ms | 1.4x |
| proof_11 | TIMEOUT (120s) | 1646ms | **73x** |
| proof_12 | TIMEOUT (120s) | 1656ms | **72x** |
| proof_13 | TIMEOUT (120s) | 2251ms | **53x** |
| parent (all proofs) | 26063ms | 2050ms | **12.7x** |

Overall 350K declarations: 1315s → 987s (25% faster).
54K Init: 101s → 72s (29% faster).
mk_var calls for parent: 1.4B → 255K (5500x reduction).

## Full Nanoda Comparison (630K Mathlib declarations)

**Total time**: Our TC 1675s, Nanoda 978s, **ratio 1.71x** (consistently 1.65-1.74x throughout).

Timing at checkpoints:
| Declarations | Our TC | Nanoda | Ratio |
|-------------|--------|--------|-------|
| 100K | 174s | 104s | 1.68x |
| 200K | 440s | 267s | 1.65x |
| 300K | 790s | 455s | 1.74x |
| 400K | 1137s | 663s | 1.71x |
| 500K | 1422s | 822s | 1.73x |
| 600K | 1617s | 942s | 1.72x |

### Gap breakdown by ratio band

| Ratio band | Count | Extra time |
|-----------|-------|-----------|
| >=10x | 11 | 16s |
| 5-10x | 105 | 13s |
| 3-5x | 4,868 | 68s |
| 2-3x | 33,151 | 239s |
| 1-2x | 61,573 | 262s |

**84% of the gap (501s / 598s) is in the 1-3x ratio band** — uniform overhead, not outliers.
We save 11s on declarations where we're faster than nanoda (22 declarations at ratio < 0.5).

### Top outlier declarations

| # | Declaration | Ours | Nanoda | Ratio | Root cause |
|---|-----------|------|--------|-------|-----------|
| 357120 | isBasis_preimage_isAffineOpen | 2308ms | 49ms | 47x | 32M push_shift, 112M mk_var, 200M mk_app |
| 298261 | norm_eval_le_injectiveSeminorm | 11490ms | 443ms | 26x | |
| 228736 | retractionKer | 2753ms | 237ms | 11.6x | |
| 211138 | freeObj._proof_2 | 2406ms | 406ms | 5.9x | inst_aux 67.5M vs 10.6M (6.4x) |

### Root cause: inst shift_down creates new Var nodes

Nanoda's inst does NOT shift_down: free variables are Locals (absolute level refs), so
Var(k) past the substitution range returns `e` UNCHANGED (original pointer). Our inst
with shift_down creates `mk_var(k - n_substs)` — a new Var node. This propagates up:
new Var → new App/Pi/Lambda parents → all the way to root. Every beta reduction
creates O(tree_size) new nodes that break pointer identity for all caches.

Representative comparison (#20700, ratio 1.58x, typical medium declaration):
| Metric | Ours | Nanoda | Ratio |
|--------|------|--------|-------|
| def_eq | 16,806 | 14,776 | 1.14x |
| whnf | 6,174 | 5,361 | 1.15x |
| inst_aux | 280,660 | 251,180 | 1.12x |
| mk_var | **11,456** | 372 | **31x** |
| mk_shift | 3,781 | 0 | ∞ |
| eq_hits | 611 | 1,291 | 0.47x |

Even with nearly identical operation counts (1.1-1.15x), the mk_var/mk_shift overhead
and reduced cache hit rates (eq_hits 0.47x) create the 1.58x time ratio.

### Attempted: overflow store for above-depth hits

Storing shifted results from above-depth whnf/infer cache hits in the overflow slot.
For #357120 specifically: stored 9K entries, 0 hits (each above-depth query is for
a different expression). For #272519: stored 82M entries, 1461 hits (massive overhead).
General case: **14.5% slower at 100K declarations** due to HashMap insertion overhead.
Reverted. The fundamental issue is that each above-depth hit is for a different
expression, so caching the shifted result doesn't help.

### Architectural fix: switch to Locals (de Bruijn levels) for free variables

The definitive fix is adopting nanoda's approach: represent free variables as
Local(DbjLevel(n)) instead of Var(k). This eliminates shift_down entirely:
- inst replaces Var(0) with substitution value, leaves other Vars unchanged
- inst cache key is 2D (e, offset) instead of 4D (e, offset|sh_amt|sh_cut)
- Subexpressions not containing the bound variable keep their pointer identity
- All caches (whnf, infer, wnu, defeq) get nanoda-like hit rates

Cost: Additional inst call per binder opening (to replace Var(0) with Local),
plus abstract call when closing (Local back to Var). But each inst is cheaper
(no shift_down), and the cache hit improvement dwarfs the opening cost.

This is a major refactor touching most of tc.rs but would close the 1.71x gap.

## References

- [Lean Kernel Arena](https://arena.lean-lang.org/) — benchmarks and test cases
- [Arena results](https://leanprover.github.io/lean-kernel-arena/)
- [Kernel implementation analysis](https://gist.github.com/nomeata/b0d8da6857cd2fd4c4a22c03ca404164)
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/title_page.html)
- [Lean Type Theory](https://github.com/digama0/lean-type-theory)
