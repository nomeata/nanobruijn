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

### Phase 3–4: Shift-Homomorphic Caching ✅

**Metadata** (stored per expression node):

- `struct_hash: u64` — structural hash with bvar indices replaced by a constant,
  plus per-child `(lb_delta, nl_delta)` for shift-invariant discrimination and
  each child's `norm_mask` (bvar_mask rotated by nl).
- `bvar_mask: u64` — bit `i` set iff any `bvar(j)` occurs with `j ≡ i (mod 64)`.
- `unbind(mask) = (mask & !1).rotate_right(1)` for binder bodies — clears the bound
  variable's bit before rotating, eliminating "ghost bits" that break shift-invariance.
  At depth ≥ 64, a free `bvar(64)` aliases with `bvar(0)` and gets incorrectly cleared,
  but this only causes hash collisions (caught by verify), not correctness issues.

**Canonical hash**: `(struct_hash, bvar_mask.rotate_right(nl % 64))` — O(1), shift-invariant
for expressions with binder depth < 64 (proved in Theory.lean for the binder-free fragment).

**Discrimination fix**: Earlier attempt without per-child deltas had too many collisions
(norm_mask maps ALL single-BVar expressions to `1<<63`). Adding `(lb_delta, nl_delta)`
between sibling children to struct_hash fully resolved this — 0 verify failures on init export.

**WHNF cache**: `FxHashMap<(u64,u64), (ExprPtr, ExprPtr, u16)>` keyed by canonical hash,
stores `(input, result, nl)`. On hit:
- Fast path: if `stored_input == query` (pointer equality), return stored result directly.
- Shift path: verify with `shift_eq(stored_input, query, delta)` (non-allocating traversal),
  then return `force_shift_aux(stored_result, delta, 0)`.

**Lazy Shift nodes**: `mk_shift` creates O(1) `Shift` wrappers. whnf peels them off
(shift-equivariance: `whnf(Shift(e,k)) = shift(whnf(e),k)`), always returning bare
(non-Shift) results via `force_shift_aux`.

**Cache stats on init export** (54,475 decls, with bit-clearing unbind):
- 3.6M exact hits (pointer match), 64k shift hits (verified), 0 verify failures
- 11k nl failures (stored_nl > query_nl), 1.1M misses, 112k shift peels

### Phase 5: Benchmark ✅ (partial)
- [done] Validated against arena test cases (89 good + 45 bad)
- [done] Init export (54,475 decls, 310MB ndjson): **324B instructions** (perf stat)
  - Baseline (original nanoda, locally-nameless): **21s**
  - Previous with metadata + canonical cache: **29s**
  - After restore_depth fix: **24.5s** (better open-expr cache retention)
  - After unbind bit-clearing: **324.0B instructions** (vs 324.7B without clearing)
  - Key optimization: scope-local infer cache for open exprs (39s → 26s → 24.5s)
  - Shift-invariant cache: 64k shift hits, 0 verify failures
- [done] grind-ring-5 (2,439 decls): 1.0s
- [done] app-lam (N=4000): **10ms** (original nanoda: 8.3s)
- [todo] Benchmark on mathlib export (requires building mathlib with lean4export)
- [todo] Profile: mk_app at 20%, hash-consing at 14% — dominated by expression allocation,
  not metadata or type checking

**Profiling results** (init export):
- `mk_app`: 20% — expression construction + hash-consing
- `IndexMap` operations: 14% — hash-consing lookups and inserts
- `mk_let`: 8% — expression construction
- `inst_aux`: 1.7% (down from 10% after single-read optimization)
- `whnf_no_unfolding_aux`: 1.2%

### Deep Binder Issue: app-lam test ✅

The app-lam arena test has ~4000 nested lambdas with `wrap2` applications at each level.
Each level applies `wrap2 lam_next lam_next` where `lam_next` is DAG-shared.

**Bug**: `restore_depth` (used by `def_eq_binder_aux`) was too aggressive — it removed
`infer_open_cache` entries at the depth being restored TO (`d < depth`), not just entries
ABOVE it. When `def_eq_binder_aux` compared Pi types with different binder names (e.g.
`Pi(y3, Nat, Nat)` vs `Pi(n, Nat, Nat)`), it would:
1. Push a local (depth 3 → 4)
2. Compare bodies (Nat == Nat, trivial)
3. `restore_depth(3)` → removed entries with `d >= 3`, including the just-computed
   `infer_open_cache[(lam_3, 3)]` entry
4. Second DAG-shared arg of `wrap2` had to re-infer from scratch → exponential blowup

**Fix**: Changed `retain(d < depth16)` to `retain(d <= depth16)` in `restore_depth`.
Note: `pop_local` already used the correct condition (`d < popped_depth` where
`popped_depth = old_len`, equivalent to `d <= new_len`).

**Result**: app-lam N=4000 completes in 10ms (original nanoda: 8.3s).
With unique binder names, N=2000 also completes instantly (was timing out before).

## Open Questions

- **Metadata cost vs benefit**: The canonical hash infrastructure costs ~3s on init export
  but only saves ~1s from shift hits. Needs larger workloads (mathlib) to determine if the
  ratio improves. The 0 verify failures suggest the hash is well-discriminating.
- **app-lam deep binder test**: ✅ Fixed — was `restore_depth` off-by-one in cache eviction.
- **Ghost bit clearing**: ✅ Switched to `(mask & !1).rotate_right(1)` — clears bound
  variable's bit before rotating. Makes canonMask exactly shift-invariant for binder
  depth < 64 (proved for binder-free fragment in Theory.lean). At depth ≥ 64, clearing
  incorrectly removes aliased free vars, but this only causes collisions caught by verify.
  Perf result: 324.0B vs 324.7B instructions (clearing wins slightly), 64k vs 59k shift hits.
- **Let-bindings**: Substitute eagerly (avoids shifting let-values, which can be large)
  or delay via `Shift`? Needs benchmarking.
- **DefEq cache shift-invariance**: The union-find defEq cache doesn't easily support
  canonical hash keys. Could switch to a HashMap with canonical hash keys + relative
  offset delta.
- **Mathlib benchmark**: Requires building mathlib export via
  `cd lean-kernel-arena && python3 lka.py build-test mathlib`. Not yet done.

## References

- [Lean Kernel Arena](https://arena.lean-lang.org/) — benchmarks and test cases
- [Arena results](https://leanprover.github.io/lean-kernel-arena/)
- [Kernel implementation analysis](https://gist.github.com/nomeata/b0d8da6857cd2fd4c4a22c03ca404164)
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/title_page.html)
- [Lean Type Theory](https://github.com/digama0/lean-type-theory)
