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
- Scope-local infer cache for open expressions, keyed by `(ExprPtr, depth)`, evicted on `pop_local`
- `inductive.rs`/`quot.rs` still use old Local approach (works correctly)

### Shift nodes (delayed shifting)

`Shift { inner, amount, cutoff }` expression variant wraps expressions for O(1) shifting.
Semantics: free Var indices in `inner` with index >= `cutoff` are shifted up by `amount`.
This is exactly a deferred `force_shift_aux(inner, amount, cutoff)`.

- `mk_shift` (cutoff=0): creates wrappers, collapses `Shift(Shift(e, j, 0), k, 0) → Shift(e, j+k, 0)`,
  elides on closed expressions, eagerly forces `Var` (O(1))
- `mk_shift_cutoff`: general version with cutoff parameter. Collapses when cutoffs match:
  `Shift(Shift(e, j, c), k, c) → Shift(e, j+k, c)`. Cannot collapse different cutoffs.
- `force_shift_shallow(e, amount, cutoff)`: pushes shift one level into constructor.
  App → `App(Shift(fun, k, c), Shift(arg, k, c))`.
  Lambda/Pi → `Lambda(Shift(ty, k, c), Shift(body, k, c+1))` — fully lazy, no traversal.
  This is the key advantage of cutoff: binder bodies get `cutoff+1` instead of requiring
  a full `shift_expr(body, amount, cutoff+1)` traversal.
- `fvar_shift_cutoff`: shifts FVarList entries >= cutoff by k. Walks to the cutoff point,
  adds k to first entry >= cutoff, shares tail. O(1) for cutoff=0, O(position) for cutoff>0.
- `force_shift_aux`: full traversal when needed (now uses cutoff from Shift nodes)
- `force_shift`: convenience wrapper that forces a top-level Shift node (any cutoff)
- `infer_inner` handles cutoff=0 Shift without forcing via context-shrinking. For cutoff>0, forces first.
- whnf peels cutoff=0 Shifts iteratively; forces cutoff>0 Shifts.
- `shift_eq` handles cutoff=0 Shift nodes; returns false for cutoff>0 (conservative).

**Current state**: whnf uses `force_shift_shallow` on results from both the direct
Shift-peeling path and the shift-invariant cache hit path (for non-App results).
App results still require `force_shift_aux` (full traversal) because `unfold_apps`
decomposes the App spine, and Shift-wrapped args create different ExprPtrs that
cause downstream cache/path divergence. Pi/Lambda/Var consumers use `view_expr`
which transparently handles Shift-wrapped children, so shallow shifting is safe.

`unfold_apps` returns lazy (Shift-wrapped) args: accumulates cutoff=0 shifts through the App
spine and wraps each arg with `mk_shift` instead of `force_shift_aux`. O(n_args) instead of
O(n_args × expr_size). Two companion fixes ensure correctness:
1. `inst_aux` forces substitution values with `force_shift` at offset=0, preventing cascading
   Shift wrappers in inst_beta results.
2. The whnf shift-invariant cache uses `force_shift_aux` for App results (not
   `force_shift_shallow`), because unfold_apps produces different ExprPtrs.

`view_expr(e)` is a view function that transparently handles Shift nodes: returns `Expr<'t>`
with Shift pushed one level inside via `force_shift_shallow`. Never returns `Shift` variant;
children may be Shift-wrapped. Replaces the common `force_shift(e); match read_expr(e)` pattern.
Used by: `unfold_apps_fun`, `unfold_apps_stack`, `inst_forall_params`, `infer_app`, `subst_aux`,
`inst_aux`, `shift_expr_aux`, and all whnf-result consumption sites (ensure_sort, ensure_pi,
infer_sort_of, reduce_proj, strong_reduce, iota_reduce_recursor, reduce_quot, is_sort_zero,
try_eta_expansion_aux, get_bignum_from_expr, get_bignum_succ_from_expr).

Remaining `force_shift_aux` call sites (outside its own implementation):
- **whnf cache hit for App results** (tc.rs): Pi/Lambda use force_shift_shallow (O(1)),
  but App results still need full traversal. This is the remaining dominant cost.
- **inst_aux val shifting**: `force_shift_aux(val, offset, 0)` for shifting subst values up.
  Needed for canonical results.
- **cutoff>0 Shifts** (unfold_apps, whnf, infer_inner): rare, unavoidable without lazy cutoff>0.
- **force_shift_shallow itself** (util.rs): forces inner Shift with mismatched cutoff.

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

**WHNF cache**: keyed by canonical hash; on hit, verify with `shift_eq` (non-allocating
traversal), then apply delta via `force_shift_aux`.

**Infer cache (open expressions)**: organized as a stack of maps indexed by
`bucket_idx = depth - 1 - fvar_lb` (the shallowest context entry the expression depends
on). Each map keys by canonical hash → (stored_input, stored_result, stored_depth).
On hit, verify with `shift_eq`, apply delta via `mk_shift`. Stack push/pop follows
`push_local`/`pop_local` for O(1) eviction (replaces O(n) `retain` scan).
Entries in shallow buckets survive push/pop of deeper context entries (correct, since
they only depend on the unchanged shallow context). If an entry was stored at a deeper
depth than the current query, we cannot reuse it (would need an "unshift"/shift-down
operation we don't have); instead we recompute and store at the lower depth, which
then serves as the base for future shifted lookups.

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
| Init (54k decls, 310MB) | 21s | ~27s |
| app-lam N=4000 | 8.3s | 10ms (830x faster) |
| Mathlib (630k decls, 4.9GB) | works (<9GB) | OOM-killed at ~120k decls |

Profile (init, 375B instructions): `force_shift_aux` is the dominant cost —
shift cache has ~40% hit rate (8M hits, 12M misses). Each miss traverses
the full expression tree creating new nodes.

## TODO

- **Eliminate force_shift_aux for App whnf cache hits**: On init, 57% of whnf shift-hits
  are non-App (now O(1) via force_shift_shallow), 43% are App (still O(n) force_shift_aux).
  Total shift-hits: ~81K. Approaches: (a) make unfold_apps normalize output so Shift-wrapped
  and fully-forced args produce the same ExprPtrs, (b) make downstream caches shift-invariant,
  or (c) "medium force": fully force the App spine args but leave deeper children as Shift nodes.

- **mk_shift_cutoff optimizations** (implemented, verify on larger workloads):
  - Short-circuit: if cutoff > fvar_ub, expression has no free vars above cutoff → no-op
  - Cutoff normalization: if fvar_lb >= cutoff, normalize cutoff to 0 for more collapsing

- **Fix mathlib OOM**: instrument memory per-declaration, find what's blowing up;
  consider periodic cache eviction or more compact expression representation

- **Extend shift-invariant caching to def_eq cache** (whnf and infer done)

- **DefEq cache with canonical keys**: current union-find doesn't support shift-invariant
  lookup; switch to HashMap with canonical keys + delta

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
  `force_shift_shallow` and `mk_shift` on whnf cache results cause type errors for App
  results, but NOT for Pi/Lambda. The mechanism: `unfold_apps` decomposes the App spine,
  and Shift-wrapped args produce different ExprPtrs than fully-forced args. These different
  ExprPtrs cause different cache hit/miss patterns in downstream infer/def_eq code, which
  changes execution paths. The failure manifests at `Lean.Grind.Ring.intCast_nat_sub`
  (depth=9) via `proof_irrel_eq` receiving an expression with wrong variable references.
  Disabling eq_cache, failure_cache, or whnf_no_unfolding_cache individually does NOT fix it.
  Fix: only use force_shift_shallow for non-App whnf results; App results still use
  force_shift_aux. Pi/Lambda consumers use view_expr which transparently handles Shifts.
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

- **force_shift_shallow on whnf results WORKS** (previously thought impossible):
  Using `force_shift_shallow` instead of `force_shift_aux` on whnf results preserves the
  top-level constructor tag (Pi/Lambda/App) while keeping children as lazy Shift nodes.
  The key insight: whnf consumers pattern-match on the top-level tag, not on children.
  Children flow into infer/def_eq/inst_beta which can handle Shift nodes.
  However, making unfold_apps return Shift-wrapped args still breaks (see TODO).

- **Lazy unfold_apps requires two companion fixes**: (1) `inst_aux` must `force_shift` subst
  values at offset=0, otherwise Shift wrappers propagate through inst_beta creating expressions
  with embedded Shifts that cascade through the system. (2) The whnf shift-invariant cache must
  use `force_shift_aux` (full traversal) not `force_shift_shallow`, because Shift-wrapped whnf
  results produce structurally different ExprPtrs that change cache behavior in def_eq and
  infer_proj, eventually causing type errors. With both fixes, lazy unfold_apps works correctly.

- **shift_eq must track binder depth**: The old shift_eq checked `j == i + delta` for all Var
  nodes, including bound vars inside Pi/Lambda bodies. This is wrong: bound Var(0) in a Pi body
  should compare as 0 == 0, not 0 == 0+delta. Fixed by adding a `cutoff` parameter that
  increments under binders. The old bug was masked because expressions rarely had Shift wrappers
  inside binder bodies (no force_shift_shallow on whnf results). The Shift handling in shift_eq
  is restricted to cutoff=0 (composition of cutoff=0 Shifts is additive; cutoff>0 requires
  conservative fallback to false).

- **shift_eq in def_eq_quick_check works**: Adding `shift_eq(inner, other_side, amount)` for
  single-sided Shift comparisons is cheap (non-allocating) and correct. This makes def_eq
  robust against Shift-wrapped inputs from infer (which returns mk_shift results).

## References

- [Lean Kernel Arena](https://arena.lean-lang.org/) — benchmarks and test cases
- [Arena results](https://leanprover.github.io/lean-kernel-arena/)
- [Kernel implementation analysis](https://gist.github.com/nomeata/b0d8da6857cd2fd4c4a22c03ca404164)
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/title_page.html)
- [Lean Type Theory](https://github.com/digama0/lean-type-theory)
