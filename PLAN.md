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

`Shift { inner, amount }` expression variant wraps expressions for O(1) shifting.

- `mk_shift`: creates wrappers, collapses `Shift(Shift(e, j), k) → Shift(e, j+k)`, elides
  on closed expressions, eagerly forces `Var` (O(1))
- `force_shift_aux`: full traversal when needed (pattern matching, substitution under binders)
- `force_shift`: convenience wrapper that forces a top-level Shift node
- All `unfold_apps*` functions call `force_shift` before peeling App nodes
- `infer_app` calls `force_shift` before matching Pi on function type
- `infer_inner` has explicit Shift arm that forces before inferring
- whnf iteratively peels nested Shifts before reducing

**Current state**: Shift nodes only wrap top-level expressions (e.g. `lookup_var` results).
All consumers force Shift fully before pattern matching. This is correct but expensive
(full O(n) traversal). See TODO for the "shallowish" force optimization.

### Shift-invariant hashing and caching

Each expression stores `struct_hash: u64` — a hash where bvar indices are replaced by a
constant, so shifted expressions share the same struct_hash.

**FVarList** (delta-encoded free variable set): Replaces the old `bvar_mask: u64` which
aliased at binder depth ≥ 64. Stores the sorted set of free bvar indices as a
delta-encoded linked list: `{0, 3, 7}` → `[0, 2, 3]` (head = lb, subsequent = gaps - 1).

- `shift k`: increment head → O(1)
- `unbind`: decrement head (or pop if 0) → O(1)
- `normalize`: set head to 0 → O(1), shift-invariant canonical form
- `union`: merge two delta lists → O(n+m), shared tails give O(1) common case
- **No false negatives at any depth** (proved in Theory.lean)

Canonical hash = `(struct_hash, normalized FVarList)`.
WHNF cache keyed by canonical hash; on hit, verify with `shift_eq` (non-allocating
traversal), then apply delta via `force_shift_aux`.

### Infrastructure

- `stacker` crate for dynamic stack growth (deep recursion on mathlib)
- 256 MB worker thread stack in `main.rs`
- Iterative `whnf_no_unfolding_aux` (was recursive, caused stack overflow)

## Results

### Correctness
- Passes app-lam, dag-app-binder, init arena tests
- Pre-existing failures on constlevels, level-imax-leq, level-imax-normalization
  (not caused by our changes — also fail on baseline)

### Performance

| Benchmark | nanoda (locally nameless) | lean-slop-kernel |
|-----------|--------------------------|------------------|
| Init (54k decls, 310MB) | 21s | ~29s |
| app-lam N=4000 | 8.3s | 10ms (830x faster) |
| Mathlib (630k decls, 4.9GB) | works (<9GB) | OOM-killed at ~120k decls |

Profile (init, 375B instructions): `force_shift_aux` is the dominant cost —
shift cache has ~40% hit rate (8M hits, 12M misses). Each miss traverses
the full expression tree creating new nodes.

## TODO

- **"Shallowish" force_shift**: Replace full `force_shift_aux` calls in unfold_apps/whnf/def_eq
  with a lazy force that pushes Shift just far enough for consumers:
  1. Peel the entire App spine: shift each arg (lazy `mk_shift`), shift the head
  2. Force the head one level to expose its constructor + immediate fields:
     Var → shifted index, Const/Sort → as-is, Pi/Lambda → binder_type (lazy),
     body (shift_expr cutoff=1), Let → similar, Proj → structure (lazy)
  3. Leave everything deeper as Shift nodes

  This is O(n_args) per step instead of O(expr_size). The blocker is def_eq:
  inner Shift nodes cause subtle failures in def_eq's recursive comparison
  (interaction with eq_cache/failure_cache/proof_irrel_eq). Needs careful
  investigation of def_eq's full control flow with inner Shift nodes.
  See `force_shift_shallow` in util.rs for the one-level version and detailed notes.

- **Fix pre-existing arena test failures**: constlevels, level-imax-leq,
  level-imax-normalization fail on baseline too. Investigate.

- **Fix mathlib OOM**: instrument memory per-declaration, find what's blowing up;
  consider periodic cache eviction or more compact expression representation

- **Extend shift-invariant caching to infer and def_eq caches** (currently only whnf)

- **DefEq cache with canonical keys**: current union-find doesn't support shift-invariant
  lookup; switch to HashMap with canonical keys + delta

- **Remove dead locally-nameless code** (Local variant, FVarId, abstr, etc.)

- **Fill in Theory.lean sorry's**: `decode_shift`, `fvars_shift_zero`

## Lessons learned (things that didn't work)

- **Bitmask shift-invariance breaks at depth ≥ 64**: `bvar(0)` and `bvar(64)` alias to
  the same bit. Replaced with delta-encoded FVarList — no aliasing at any depth.

- **struct_hash without per-child deltas had too many collisions**: all single-bvar
  expressions got `norm_mask = 1<<63`, so `app(bvar 0, bvar 1)` and `app(bvar 0, bvar 0)`
  had the same canonical hash. Mixing `(bvar_lb_delta, bvar_ub_delta)` between siblings
  into struct_hash fixed this (0 verify failures).

- **`restore_depth` off-by-one caused exponential blowup**: the cache eviction in
  `def_eq_binder_aux` used `d < depth` instead of `d <= depth`, discarding valid entries
  at the current depth. This made app-lam O(2^n) instead of O(n).

- **Shallow force in whnf (12x speedup but broken)**: Replacing `force_shift_aux` with
  `force_shift_shallow` in whnf reduced init from 375B to 30.6B instructions. But inner
  Shift nodes broke def_eq — expressions that should be definitionally equal returned false.
  The issue: after whnf produces Shift-wrapped children, def_eq's recursive comparison
  encounters Shift at every level. While this should converge at leaves, subtle cache
  interactions cause incorrect results. Full force in def_eq_inner fixes correctness but
  defeats the performance gain.

- **Metadata cost dominates on small workloads**: computing struct_hash + FVarList
  for every expression adds overhead, but shift hits only save ~1s on init. The break-even
  point needs larger workloads (mathlib) where shift hits accumulate.

- **Inlining mk_* into force_shift_aux made it worse** (375B → 382B): code bloat hurt
  icache. Similarly, adding an Option<u64> parameter for struct_hash reuse made it worse
  (375B → 385B) due to branch overhead on every mk_* call.

## References

- [Lean Kernel Arena](https://arena.lean-lang.org/) — benchmarks and test cases
- [Arena results](https://leanprover.github.io/lean-kernel-arena/)
- [Kernel implementation analysis](https://gist.github.com/nomeata/b0d8da6857cd2fd4c4a22c03ca404164)
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/title_page.html)
- [Lean Type Theory](https://github.com/digama0/lean-type-theory)
