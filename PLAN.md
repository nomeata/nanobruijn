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
  increments its cutoff under binders in sync. Returns false for mismatched cutoffs (conservative).

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

### Canonicalize and canon_eq (replaces sem_eq)

`canonicalize(e)` fully resolves all Shift wrappers in an expression tree, memoized in
`expr_cache.canon_cache`. Due to arena hash-consing (`alloc_expr` deduplicates),
`canonicalize(a) == canonicalize(b)` iff the expressions are semantically equal modulo shifts.

`canon_eq(a, b)` checks `a == b || canonicalize(a) == canonicalize(b)` — pointer equality
first, then canonicalize both sides. Replaces `sem_eq` throughout the system.

**Key optimization**: `whnf`, `whnf_no_unfolding`, and `whnf_no_unfolding_cheap_proj` all
canonicalize their results before returning. This ensures downstream code (especially def_eq)
can rely on pointer equality for already-reduced expressions, reducing canonicalize calls from
11M to much fewer (most comparisons are pointer-equal after whnf canonicalization).

`shift_eq_aux` handles Shift on the b-side when `amount > delta` by reversing the
comparison: `shift(a, delta) == shift(inner_b, amount)` iff `shift(inner_b, amount - delta) == a`.
Still used for cross-depth shift-invariant cache lookups (delta > 0).

Used in: `def_eq_quick_check`, all cache collision guards (eq_cache, failure_cache,
defeq_open_lookup), whnf/whnf_no_unfolding cache hits, infer cache hits,
`try_unfold_proj_app`, `strong_reduce`, `def_eq_nat`.

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

**WHNF cache**: keyed by canonical hash; on hit, verify with `sem_eq` (same-depth) or
`shift_eq` + `push_shift` (cross-depth). Both paths now enabled.

**whnf_no_unfolding cache**: keyed by canonical hash; `sem_eq` for same-depth hits.
`whnf_no_unfolding` also peels top-level Shifts (shift-equivariance) before cache lookup.

**Infer cache**: unified stack of maps. Bucket 0 holds closed expressions (never evicted).
Buckets 1..depth hold open expressions, indexed by `bucket_idx = depth - fvar_lb`.
Each map keys by canonical hash → (stored_input, stored_result, stored_depth, checked).
`checked=true` entries (from Check pass) serve both Check and InferOnly queries;
`checked=false` entries only serve InferOnly. On hit, verify with `shift_eq`, apply
delta via `mk_shift`. Stack push/pop follows `push_local`/`pop_local` for O(1) eviction.
Replaces the old three-cache design (infer_cache_check, infer_cache_no_check, infer_open_cache).
Entries in shallow buckets survive push/pop of deeper context entries (correct, since
they only depend on the unchanged shallow context). If an entry was stored at a deeper
depth than the current query, we cannot reuse it (would need an "unshift"/shift-down
operation we don't have); instead we recompute and store at the lower depth, which
then serves as the base for future shifted lookups.

**DefEq cache (closed expressions)**: `eq_cache` and `failure_cache` use
`FxHashMap<((u64,u64),(u64,u64)), (ExprPtr, ExprPtr)>` — canonical hash pair as key,
stored ExprPtrs verified via `sem_eq`. Replaced the old `UnionFind` eq_cache and
`FxHashSet<(ExprPtr, ExprPtr)>` failure_cache. The UnionFind module is now deleted.

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
| Init (54k decls, 310MB) | 24s | 35s (1.5x) |
| app-lam N=4000 | 8.3s | 10ms (830x faster) |
| Mathlib (630k decls, 4.9GB) | ~16min (est.) | ~65min (est. ~4x) |
| sheafedSpaceMap_comp (worst case) | ~2s | 12s (6x) |

Profile (init, pre-deletion baseline, 375B instructions): `force_shift_aux` was the
dominant cost — shift cache had ~40% hit rate (8M hits, 12M misses). Now deleted;
all shifting uses `push_shift` (one-level push) or `mk_shift` (O(1) wrapper).

## Design goal: match nanoda's cache behavior

Our checker should have **at least all the cache hits/reuse as nanoda**. The only
acceptable overhead vs nanoda is:
- More expensive hash computation (canonical hash rather than pointer identity)
- The cost of creating/carrying Shift wrappers

We should **not** be slower due to missed cache hits. If we are, we need to find and fix
the cache miss, not paper over it with heuristics (DAG size thresholds, degraded mode,
timeouts, etc.).

**No forced canonicalization**: The whole point of Shift nodes is to avoid traversals.
We must never canonicalize (force all Shifts deep) on the critical path (e.g., before
cache lookups). The `struct_hash` is already shift-invariant by design (Shift nodes
inherit their inner expression's struct_hash), so canonical hashes match for shifted
and unshifted versions. Cache lookups should work without forcing. If they don't, the
bug is in the cache verification logic (canon_eq/shift_eq), not a reason to force.

**Approach**: Add tracing/instrumentation to both nanoda and our checker to compare cache
hit rates side-by-side. nanoda's TC code is included in this project (module `nanoda_tc`)
with a runtime flag to switch between checkers, making A/B comparison easy.

## TODO

- **Tracing**: Instrument both nanoda TC and our TC to log cache hits/misses for whnf,
  def_eq, infer. Compare on pathological declarations to find where we miss hits.

- **Remove dead code**: `sem_eq` (now unused, replaced by `canon_eq`), thread_local
  profiling counters, `struct_hash`/`fvar_list_of` (unused)

- **Remove dead locally-nameless code** (Local variant, FVarId, abstr, etc.)

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

## References

- [Lean Kernel Arena](https://arena.lean-lang.org/) — benchmarks and test cases
- [Arena results](https://leanprover.github.io/lean-kernel-arena/)
- [Kernel implementation analysis](https://gist.github.com/nomeata/b0d8da6857cd2fd4c4a22c03ca404164)
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/title_page.html)
- [Lean Type Theory](https://github.com/digama0/lean-type-theory)
