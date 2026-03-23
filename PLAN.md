# lean-slop-kernel: De Bruijn Indices with Shift-Homomorphic Caching

Forked from [nanoda_lib](https://github.com/ammkrn/nanoda_lib) (Rust Lean 4 kernel).

## Hypothesis

The standard Lean kernel uses locally nameless binding: when entering a binder, it
substitutes the bound variable with a fresh free variable (expensive traversal), but
gains cache hits because expressions at different depths become structurally equal.

Pure de Bruijn indices avoid the substitution cost (just increment a depth counter),
but lose cache hits because the "same" expression at different depths has different
variable indices.

**We hypothesize that de Bruijn indices + a shift-homomorphic hash + delayed shifting
can achieve both: no substitution on binder entry AND effective caching.**

### Architectural Goal: Zero-Copy, Allocation-Free Checking

The ideal kernel reads the export file (possibly mmap'd) and type-checks declarations
directly off the read-only input without allocating new expression nodes for
substitution. With locally nameless, every binder entry forces allocation of fresh
fvars and traversal to substitute. With de Bruijn + `Shift` nodes, entering a binder
is just incrementing a depth counter, and the only allocations are for `Shift` wrappers
(which are small, fixed-size, and can live in a bump allocator or stack). WHNF
reduction still allocates (beta reduction produces new terms), but the common case of
"check type, check defEq, move on" should be nearly allocation-free.

This also enables trivial parallelism: multiple threads can type-check independent
declarations against the same mmap'd input with no synchronization on the expression
store.

## Key Ideas

### 1. Depth-Normalizing Hash

Each expression stores `(canonical_hash, lower_bound)`:

- `BVar(i)`: hash = `BVAR_CONST`, lb = `i`
- `App(f, x)`: hash = `combine(hash_f, hash_x, lb_f - lb_x)`, lb = `min(lb_f, lb_x)`
- `Lam(ty, body)`: hash = `combine(hash_ty, hash_body, lb_ty - (lb_body - 1))`,
  lb = `min(lb_ty, lb_body - 1)`

The delta `lb_f - lb_x` is shift-invariant (shifting both by k cancels). The hash
captures full relative variable structure — no information is lost — but is invariant
under uniform shifting. Two expressions differing only by a uniform shift produce the
same hash.

### 2. `Shift` Nodes (Delayed/Explicit Shifting)

Instead of traversing to shift, wrap: `Shift(e, k)` meaning all free vars in e are
shifted up by k.

- `hash(Shift(e, k)) = hash(e)` — transparent to cache lookup
- `lb(Shift(e, k)) = lb(e) + k` — O(1)
- Pushed down lazily during pattern matching in reduction
- Collapsed: `Shift(Shift(e, j), k) → Shift(e, j+k)`
- Skipped: if `loose_bvar_range(e) == 0`, no shift needed

Cache results are returned wrapped in `Shift` — O(1) instead of O(n) traversal.

### 3. Cache Design

- **DefEq cache**: keyed by `(canonical_hash_a, canonical_hash_b)`, stores bool — works directly
- **WHNF cache**: keyed by canonical_hash, stores result. On retrieval at different depth,
  wrap in `Shift` node
- **Infer cache**: same as WHNF — store canonical result, shift on retrieval

### 4. Expression Metadata

Each expression node stores (computed at construction, O(1)):
- `canonical_hash: u64`
- `lower_bound: u16` (minimum bvar index; sentinel for "no free bvars")
- `loose_bvar_range: u16` (max bvar index + 1, for fast "no free vars" checks)

## Implementation Plan

### Phase 1: Remove FVars, Pure De Bruijn
- Remove `Local` variant and `FVarId` from `Expr`
- Remove `has_fvars` tracking
- Remove `abstr` / `abstr_levels` (abstraction = identity with de Bruijn)
- Change binder entry in `tc.rs`: instead of inst+mk_local, just increment depth counter
- Adapt `inst` to work purely with de Bruijn substitution

### Phase 2: Add `Shift` Node
- Add `Shift { inner: ExprPtr, amount: u16, hash, lower_bound, loose_bvar_range }` to `Expr`
- Implement shift-pushing in all pattern matches (reduction, defEq, infer)
- Implement collapsing and skip-when-closed optimizations

### Phase 3: Shift-Homomorphic Hash
- Replace current hash computation with depth-normalizing scheme
- Add `lower_bound` field to all `Expr` variants
- Cache keys use canonical hash; results wrapped in `Shift` on retrieval

### Phase 4: Adapt Caches
- Modify `TcCache` to use canonical hashes as keys
- WHNF/infer caches return `Shift`-wrapped results
- DefEq cache keyed by canonical hash pairs

### Phase 5: Benchmark
- Validate against arena test cases (133 tests, downloadable tarball)
- Benchmark on mathlib export against unmodified nanoda
- Profile to find remaining bottlenecks

## Open Questions

- **Let-bindings**: Substitute eagerly (avoids shifting let-values, which can be large)
  or delay via `Shift`? Needs benchmarking.
- **Hash function choice**: FxHash-based mixing? Or something with better algebraic
  properties for the delta encoding?
- **Bitmask vs range**: Is `loose_bvar_range` sufficient, or do we need a bitmask of
  which indices appear free? Range is cheaper to maintain.
- **Interaction with union-find**: nanoda's defEq uses union-find for equivalence classes.
  Does depth-normalization interact well with union-find merging?

## References

- [Lean Kernel Arena](https://arena.lean-lang.org/) — benchmarks and test cases
- [Arena results](https://leanprover.github.io/lean-kernel-arena/)
- [Kernel implementation analysis](https://gist.github.com/nomeata/b0d8da6857cd2fd4c4a22c03ca404164)
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/title_page.html)
- [Lean Type Theory](https://github.com/digama0/lean-type-theory)
