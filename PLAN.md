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

## References

- [Lean Kernel Arena](https://arena.lean-lang.org/) — benchmarks and test cases
- [Arena results](https://leanprover.github.io/lean-kernel-arena/)
- [Kernel implementation analysis](https://gist.github.com/nomeata/b0d8da6857cd2fd4c4a22c03ca404164)
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/title_page.html)
- [Lean Type Theory](https://github.com/digama0/lean-type-theory)
