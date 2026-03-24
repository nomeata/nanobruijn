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

### Phase 1: Remove FVars, Pure De Bruijn ✅
- [done] Core tc.rs uses pure de Bruijn: `push_local`/`pop_local` instead of `inst`+`mk_local`
- [done] `inst` split into `inst` (no shift-down, for Local-based code) and `inst_beta` (shift-down,
  for beta/let reduction and Pi consumption)
- [done] `inst_aux` shifts substitution values by offset when substituting under binders
- [done] `lookup_var` retrieves types from local_ctx and shifts to current depth
- [done] Infer cache restricted to closed expressions (DAG-shared open exprs are depth-dependent)
- [done] Eta expansion shifts `y` up by 1 when constructing `λ x. y x`
- [deferred] inductive.rs/quot.rs still use old Local approach (works correctly)
- [deferred] Remove dead code (Local variant, FVarId, abstr, etc.)
- **Passes all 88 arena good tests, rejects all 40 bad tests**
- **Performance: init-prelude (2051 decls) 0.08s, grind-ring-5 (2439 decls) 2.97s (release)**

### Phase 2: Shift Nodes ✅
- [done] `Shift { inner, amount }` variant in Expr for delayed shifting
- [done] `mk_shift` creates O(1) wrappers (collapses nested, elides on closed)
- [done] `force_shift` / `force_shift_aux` for full traversal when needed
- [done] `shift_expr` with cutoff=0 creates lazy Shift (cutoff>0 traverses)
- [done] All pattern-matching sites handle Shift: whnf, infer, def_eq, inductive, etc.
- [done] `inst_aux` uses `force_shift_aux` (not `mk_shift`) for substitution values
  under binders — prevents Shift nodes inside Pi/Lambda bodies where pattern-matching
  code expects bare constructors
- [done] `def_eq_quick_check` strips matching Shift wrappers
- **Passes all 88 arena good tests + 5 bad tests**

**Key design constraint**: Lazy Shift nodes should only wrap top-level expressions
(e.g. `lookup_var` results), not appear inside expression trees. Code that pattern-matches
on Pi/Lambda/etc. breaks if those are wrapped in Shift.

### Phase 3–4: Shift-Homomorphic Caching (BLOCKED — design issue)

The original plan called for:
- Depth-normalizing hash: `(canonical_hash, lower_bound)` pairs with shift-invariant deltas
- Depth-invariant caches: keyed by canonical hash

**Problem discovered**: The delta-based hash scheme `hash(App(f,x)) = combine(ch_f, ch_x,
lb_f - lb_x)` is NOT shift-invariant for binder bodies. In `Lambda(ty, body)`, the body
contains both Var(0) (bound, fixed under shifting) and free vars (shifted). The delta
between bound and free vars changes under shifting, breaking the hash invariance.

This affects the overwhelmingly common case of dependent binder bodies (any `(x : A) → B x`
where B references both x and external variables).

**Possible solutions** (not yet implemented):
1. **Two-level normalization**: Compute a normalized body hash at binder construction time
   by shifting free vars to a canonical position. Requires O(body_size) traversal per binder
   at construction, which may negate the caching benefit.
2. **Separate bound/free tracking**: Store `min_bvar_gte1` metadata per expression to
   correctly identify free vars in binder bodies. Adds complexity.
3. **Accept imprecision**: Use the delta scheme with known imprecision for binder bodies.
   Reduces cache hit rate but preserves correctness (with verification on hit).
4. **Shifted pointer pairs**: Carry `(ExprPtr, shift_amount)` through computations instead
   of modifying the expression DAG. Major API refactor.

### Phase 5: Benchmark ✅ (partial)
- [done] Validated against arena test cases (88 good + 45 bad)
- [done] Init export (54,475 decls, 310MB ndjson): **27s** single-threaded (release)
  - Baseline (original nanoda, locally-nameless): **21s** (1.29x slower)
  - Before scope-local cache: 39s → 27s (31% speedup from open-expr caching)
- [done] init-prelude (2,051 decls): 0.08s, grind-ring-5 (2,439 decls): 2.97s (release)
- [todo] Benchmark on mathlib export (requires building mathlib with lean4export)
- [todo] Profile remaining 29% gap vs baseline

## Open Questions

- **Shift-homomorphic hash**: How to handle bound variables in binder bodies? See Phase 2–4.
- **Let-bindings**: Substitute eagerly (avoids shifting let-values, which can be large)
  or delay via `Shift`? Needs benchmarking.
- **Interaction with union-find**: nanoda's defEq uses union-find for equivalence classes.
  Does depth-normalization interact well with union-find merging?
- **Cache strategy without shift-invariant hash**: Could use `(ExprPtr, depth)` keys with
  shift-on-hit for WHNF/infer caches. Simple, correct, but O(result_size) per cache hit.

## References

- [Lean Kernel Arena](https://arena.lean-lang.org/) — benchmarks and test cases
- [Arena results](https://leanprover.github.io/lean-kernel-arena/)
- [Kernel implementation analysis](https://gist.github.com/nomeata/b0d8da6857cd2fd4c4a22c03ca404164)
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/title_page.html)
- [Lean Type Theory](https://github.com/digama0/lean-type-theory)
