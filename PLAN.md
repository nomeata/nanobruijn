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

- `mk_shift`: creates wrappers, collapses `Shift(Shift(e, j), k) → Shift(e, j+k)`, elides on closed
- `force_shift_aux`: full traversal when needed (pattern matching, substitution under binders)
- All pattern-matching sites (whnf, infer, def_eq, inductive) handle Shift peeling
- whnf iteratively peels nested Shifts before reducing

**Constraint**: Shift nodes only wrap top-level expressions (e.g. `lookup_var` results),
never inside expression trees. Pattern-matching on Pi/Lambda/etc. breaks otherwise.

### Shift-homomorphic canonical hash (current, bitmask-based)

Each expression stores `struct_hash: u64` (bvar indices replaced by constant, with
per-child `(bvar_lb_delta, bvar_ub_delta)` mixed in) and `bvar_mask: u64` (bit `i%64` set
iff `bvar(j)` with `j ≡ i mod 64` occurs).

- Canonical hash = `(struct_hash, bvar_mask.rotate_right(bvar_ub % 64))`
- `unbind(mask) = (mask & !1).rotate_right(1)` — clears bound var's ghost bit
- WHNF cache keyed by canonical hash; on hit, verify with `shift_eq` (non-allocating traversal)
- 64k shift hits, 0 verify failures on init export

**Problem**: 64-bit mask aliases at binder depth ≥ 64 — causes false negatives.

### Proposed: delta-encoded free variable lists

Replace `bvar_mask` with exact delta-encoded sorted set of free bvar indices.
E.g. `{0, 3, 7}` encoded as `[0, 2, 3]` (head = lb, subsequent entries = gaps - 1).

- `shift k`: increment head → O(1)
- `unbind`: decrement head (or pop if 0) → O(1)
- `normalize`: set head to 0 → O(1), shift-invariant canonical form
- `union`: merge two delta lists → O(n+m), but shared tails give O(1) common case
- **No false negatives at any depth** (proved in Theory.lean)

### Infrastructure

- `stacker` crate for dynamic stack growth (deep recursion on mathlib)
- 256 MB worker thread stack in `main.rs`
- Iterative `whnf_no_unfolding_aux` (was recursive, caused stack overflow)

## Results

### Correctness
- Passes all 89 arena good tests + 45 bad tests (correctly rejected)

### Performance

| Benchmark | nanoda (locally nameless) | lean-slop-kernel |
|-----------|--------------------------|------------------|
| Init (54k decls, 310MB) | 21s | ~24.5s (+17%) |
| app-lam N=4000 | 8.3s | 10ms (830x faster) |
| grind-ring-5 (2.4k decls) | ~3s | 1.0s |
| Mathlib (630k decls, 4.9GB) | works (<9GB) | OOM-killed at ~120k decls |

The Init overhead (~17%) comes from expression metadata (struct_hash, bvar_mask, per-child
deltas) and hash-consing. The shift-invariant cache saves ~1s from 64k shift hits but the
metadata costs ~3s.

Profile (init export): `mk_app` 20%, IndexMap (hash-consing) 14%, `mk_let` 8%,
`inst_aux` 1.7%, `whnf_no_unfolding_aux` 1.2%.

### Mathlib status
OOM-killed around 120k/630k declarations due to 50 GB cgroup memory limit. Vanilla nanoda
uses <9 GB. The DAG and caches grow unboundedly; need to investigate which declarations
or data structures cause memory blowup.

## TODO

- **Implement delta-encoded FVarList** in Rust (replace `bvar_mask: u64`) — no false
  negatives, exact shift-invariant cache keys at any depth
- **Fix mathlib OOM**: instrument memory per-declaration, find what's blowing up; consider
  periodic cache eviction or more compact expression representation
- **Extend shift-invariant caching to infer and def_eq caches** (currently only whnf)
- **DefEq cache with canonical keys**: current union-find doesn't support shift-invariant
  lookup; switch to HashMap with canonical keys + delta
- **Let-binding strategy**: eager substitution (current) vs delay via Shift — benchmark
- **Hash-cons the FVarList nodes** for O(1) equality and use pointer as hash component
- **Remove dead locally-nameless code** (Local variant, FVarId, abstr, etc.)
- **Fill in Theory.lean sorry's**: `decode_shift`, `fvars_shift_zero`

## Lessons learned (things that didn't work)

- **Bitmask shift-invariance breaks at depth ≥ 64**: `bvar(0)` and `bvar(64)` alias to
  the same bit. The `unbind` clearing trick (`mask & !1`) removes both, causing false
  negatives for shift-equivalent expressions. In practice binder depth > 64 is rare
  (0 on init) but this fundamentally limits the approach.

- **struct_hash without per-child deltas had too many collisions**: all single-bvar
  expressions got `norm_mask = 1<<63`, so `app(bvar 0, bvar 1)` and `app(bvar 0, bvar 0)`
  had the same canonical hash. Mixing `(bvar_lb_delta, bvar_ub_delta)` between siblings
  into struct_hash fixed this (0 verify failures).

- **`restore_depth` off-by-one caused exponential blowup**: the cache eviction in
  `def_eq_binder_aux` used `d < depth` instead of `d <= depth`, discarding valid entries
  at the current depth. This made app-lam O(2^n) instead of O(n). Subtle because
  `pop_local` already had the correct condition.

- **Shift nodes inside expression trees break pattern matching**: code expects
  `Pi(name, ty, body)` but gets `Shift(Pi(...), k)`. Solution: Shift nodes only wrap
  top-level expressions; `force_shift_aux` is used when building subexpressions.

- **Metadata cost dominates on small workloads**: computing struct_hash + bvar_mask + deltas
  for every expression adds ~3s on init, but shift hits only save ~1s. The break-even
  point needs larger workloads (mathlib) where shift hits accumulate.

## References

- [Lean Kernel Arena](https://arena.lean-lang.org/) — benchmarks and test cases
- [Arena results](https://leanprover.github.io/lean-kernel-arena/)
- [Kernel implementation analysis](https://gist.github.com/nomeata/b0d8da6857cd2fd4c4a22c03ca404164)
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/title_page.html)
- [Lean Type Theory](https://github.com/digama0/lean-type-theory)
