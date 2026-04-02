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

**whnf_no_unfolding cache**: same fvar_lb-based bucketing and cross-depth shift_eq pattern
as the whnf cache. Also peels top-level Shifts (shift-equivariance) before cache lookup.

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
| Init (54k decls, 310MB) | 26s | 33s (1.27x) |
| app-lam N=4000 | 8.3s | 10ms (830x faster) |
| Mathlib (630k decls, 4.9GB) | ~16min (est.) | 153min (0 timeouts, ~9.5x) |
| sheafedSpaceMap_comp (worst case) | ~2s | 12s (6x) |

Note: Init was 29s before fvar_lb-based bucketing (depth-only bucketing, no cross-depth
shift_eq). The 4s regression comes from fvar_lb computation overhead on every cache access.
Previous Mathlib run (with canonicalize, before fvar_lb bucketing) had 213 timeouts.
Current code: 0 timeouts, 153min wall time (~9.5x nanoda).

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

### WHNF cache collision problem (main Mathlib bottleneck)

On pathological Mathlib declarations (e.g. #334175 `toPartialMap._proof_6`), the whnf cache
has massive hash collisions: 2.9M verify_fails with only 9K no_entry misses. The root cause:

- `canonical_hash = (struct_hash, fvar_normalize_hash)` is deliberately shift-invariant
- This means many different expressions map to the same hash key
- The HashMap stores ONE entry per key — last writer wins
- When different (non-shift-variant) expressions share a canonical hash, they evict useful entries

The dominant collision pattern is **stored_depth > query_depth**: an entry stored at depth D
cannot serve a query at depth D' < D (we only support upward cross-depth shift_eq, not
downward). The "prefer lower depth" store policy eventually fixes this, but every depth
transition wastes a recomputation.

Impact: nanoda gets near-100% whnf cache hit rate (5.99M/5.99M), we get 69% (9.4M/13.6M).
The 4.2M extra whnf reductions cascade into 2x more infer/inst calls and 35x more inst_aux
nodes (542M vs 15M).

Confirmed fix: multi-entry cache (Vec per slot, cap=4) drops verify_fails from 2.9M to 92,
cuts inst_aux from 542M to 135M, halves the pathological case time. But regresses Init
slightly due to Vec allocation overhead. Needs a low-overhead multi-entry approach.

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

- **Reduce inst_aux traversal count**: The 4.8x gap (938K vs 196K) is the main pathological-
  case blocker, but general performance is now ~1.27x. Ideas:
  - Persistent inst_cache across inst_beta calls (include subst in key)
  - Size-bounded eager shift (resolve small vals, defer large ones)
  - Avoid creating Shift wrappers for subst vals that will be immediately consumed by whnf

- **Investigate fvar_lb computation overhead**: fvar_lb-based bucketing regressed Init
  from 29s to 33s. The fvar_lb computation on every cache access may outweigh the
  cross-depth hit benefit for Init. Profile and consider caching fvar_lb.

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

## References

- [Lean Kernel Arena](https://arena.lean-lang.org/) — benchmarks and test cases
- [Arena results](https://leanprover.github.io/lean-kernel-arena/)
- [Kernel implementation analysis](https://gist.github.com/nomeata/b0d8da6857cd2fd4c4a22c03ca404164)
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/title_page.html)
- [Lean Type Theory](https://github.com/digama0/lean-type-theory)
