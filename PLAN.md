# nanobruijn

Forked from [nanoda_lib](https://github.com/ammkrn/nanoda_lib) (Rust Lean 4 type checker).

**Goal**: Replace locally-nameless binding with pure de Bruijn indices + shift-homomorphic
caching. Avoid the expensive substitution on binder entry while retaining cross-depth
cache hits via shift-invariant keys.

## Design (changes from vanilla nanoda)

### Pure de Bruijn (no locally nameless)

Vanilla nanoda substitutes `bvar(0)` with a fresh fvar on binder entry (full traversal).
We use a local context array with `push_local`/`pop_local` (zero allocation).

- `inst` split into `inst` (no shift-down) and `inst_beta` (shift-down for beta/let/Pi)
- `inst_aux` shifts substitution values under binders via `mk_shift(val, offset)`
- `lookup_var` retrieves types from `local_ctx[depth - 1 - idx]` and shifts to current depth
- `inductive.rs`/`quot.rs` still use old Local approach (works correctly)

### Shift nodes (delayed shifting)

`Shift { inner, amount: i16, cutoff }` expression variant wraps expressions for O(1) shifting.
Semantics: free Var indices in `inner` with index >= `cutoff` are shifted by `amount`
(positive = up, negative = down). Negative amounts are valid when shifted-away vars are unused.

- `mk_shift` (cutoff=0): creates wrappers, collapses nested same-cutoff Shifts, elides on
  closed expressions, eagerly forces `Var` (O(1))
- `mk_shift_cutoff`: general version with cutoff parameter. Deduplicates via
  `(ExprPtr, amount, cutoff) → ExprPtr` table for pointer identity preservation.
- `push_shift(e, amount, cutoff)`: pushes shift one level into constructor.
  App → recurses into `fun` only, lazily Shift-wraps `arg`. Ensures App spine nodes are
  real constructors (not Shift wrappers) while deferring arg work.
  Lambda/Pi → `Lambda(Shift(ty, k, c), Shift(body, k, c+1))` — fully lazy, no traversal.
- `view_expr(e)`: view function that transparently handles Shift nodes via `push_shift`.
  Never returns `Shift` variant; children may be Shift-wrapped. Used throughout the system
  wherever expressions are pattern-matched.
- `force_shift_aux` has been deleted. All shifting uses `mk_shift` or `push_shift`.

**Shift composition in inst_aux**: When `inst_aux` carries pending shift `(sh_amt, sh_cut)`
and encounters `Shift(inner, amount, cutoff)`, it composes the shifts directly when
`cutoff < sh_cut && amount >= (sh_cut - cutoff)`, avoiding intermediate Shift creation.
This captures ~100% of first-level binder mismatches and repeats at every binder depth.

### sem_eq (replaces pointer equality)

`sem_eq(a, b)` = `shift_eq_aux(a, b, 0, 0)` — structural walk that transparently handles
Shift wrappers by accumulating deltas. No allocation, no new node creation. Replaces all
pointer equality (`==`) comparisons throughout the system.

`shift_eq_aux(a, b, delta, cutoff)` checks whether `a` equals `shift(b, delta)`:
- Increments `cutoff` under binders (bound vars compare without delta)
- Absorbs Shift nodes when their cutoff matches the comparison cutoff (additive amounts)
- **Mismatched cutoff fast path**: When `fvar_lb(inner) >= max(sc, cutoff)`, absorbs into delta
- **General path** (`shift_eq_pending`): BiShift representation for two-layer shifts per side.
  Conservative false only when three distinct cutoff levels would be needed (extremely rare).
- Direct-mapped caches (1M entries for shift_eq_aux, 256K for shift_eq_pending) prevent
  DAG→tree explosion. Generation-counted (`GenCache`) for O(1) cross-declaration reuse.

### Lazy zeta in whnf Let case

`whnf_no_unfolding_aux` handles `Let { val, body, .. }` lazily: pushes the let-binding
onto `local_ctx`, reduces the body in the extended context, pops, then `inst_beta(result, [val])`
on the much smaller whnf result. This avoids unbounded inst_beta growth on deeply nested lets.

When whnf encounters `Var(k)` pointing to a let-binding (`lookup_var_value`), it performs
zeta reduction: unfolds to the shifted let value and continues reducing.

`infer_let` uses eager `inst_beta(body, [val])` — always-let-in-context in infer diverges
on 8/54086 Init declarations because `inst_beta(result, [val])` after pop creates
structurally different expressions (not shift-variants), unlike nanoda where fvar-based
zeta returns the original `val` pointer.

### Shift-invariant hashing and caching

Each expression stores `struct_hash: u64` — purely structural hash (tag + children's
struct_hashes + binder_name/style). Bvar indices are replaced by a constant (VAR_HASH),
so shifted expressions share the same struct_hash.

**FVarList** (delta-encoded free variable set): Stores the sorted set of free bvar indices
as a delta-encoded linked list. O(1) shift/unbind/normalize, O(n+m) union with shared-tail
optimization. No false negatives at any depth (proved in Theory.lean).

Canonical hash = single u64, mixing struct_hash with normalized FVarList hash via golden
ratio multiply.

**All caches use fvar_lb-based bucketing**: `bucket_idx = depth - fvar_lb`. Expressions at
different depths land in the same bucket only if they reference the same context range.
Cross-depth hits use `shift_eq(stored, query, depth_delta)` and return shifted results.

**ChainMap (key-increment chaining)**: All caches use a unified `ChainMap<K, V>` that
chains collisions via key-increment (K, K+1, K+2) in a single FxHashMap. Replaces the
previous primary+overflow 2-HashMap pattern. `ChainKey` trait provides `chain_next()`
for key types (u64 wrapping_add, (u64,u64) increment on second component).

**Cache hit promotion**: After a successful **same-depth** cache hit, replace the primary
slot with the query for future pointer-equality fast-path. **Critical: never promote
above-depth hits** — this would evict the low-depth canonical entry, causing cascading misses.

**WHNF cache**: Keyed by canonical hash → `(input, result, stored_depth)`. Prefers lower
stored_depth (more reusable). Above-depth hits return `push_shift(result, delta, 0)`.
Below-depth whnf hits use `push_shift_down(result, abs_delta)` — full eager traversal
that concretely resolves all Var indices to valid indices at the target depth. Guarded by
`result_fvar_lb >= abs_delta` (ensures no negative indices). 17K hits on Init with zero
measurable overhead (traversal cost offset by avoided whnf recomputation).

**whnf_no_unfolding cache**: Same pattern as whnf cache. Uses inline 2-slot entries.
Also peels top-level Shifts (shift-equivariance) before cache lookup. Identity caching:
stores `e→e` at all break paths (Sort, Const, Lambda, Pi, etc.) unconditionally.

**Infer cache**: Unified stack of maps. Bucket 0 holds closed expressions (never evicted).
`checked=true` entries serve both Check and InferOnly queries. Below-depth hits supported
(infer results are typically small enough for `push_shift_down`).

**DefEq cache (closed)**: Canonical hash pair key, `sem_eq` verification. Pointer-based
`UnionFind<ExprPtr>` provides transitive equality in O(α(n)). Shift-aware UF: when both
sides are Shift nodes with matching amounts, also union inner expressions.

**DefEq cache (open)**: Stack-of-maps like infer cache. Separate positive/negative stacks.
`bucket_idx = depth - min(fvar_lb(x), fvar_lb(y))`.

### Speculative app congruence in def_eq

Before expensive whnf/delta work in `def_eq_inner`, speculatively try structural App
congruence using only O(1) `cheap_eq` checks on each arg and the head.

`cheap_eq(x, y)`: combines `sem_eq`, `eq_cache_contains`, UF check, and `defeq_open_lookup`.
Never recurses — O(1). This is "almost-cached equality": the whole expression may not be
cached, but all sub-components are.

Applied twice: once before whnf (spec_app), once after whnf_cheap_proj (spec_app2, guarded
by `x_n != x || y_n != y`). Also skip redundant second `quick_check` when whnf_cheap_proj
was a no-op.

6.3% hit rate, but each hit avoids expensive whnf + delta unfolding. **-16.7% on full Mathlib.**

### Shift-down-only optimization in inst_aux

When inst_aux detects all free bvars are past the substitution range
(`fvar_lb >= offset + n_substs`), delegates to persistently-cached
`push_shift_down_cutoff(e, n_substs, offset)` instead of traversing. Guard:
`n_substs >= 4` (lower thresholds regress due to HashMap overhead outweighing savings).
Fixed worst outliers: #298261 from 11.5s to 830ms, #357120 from 2.3s to 85ms.

### Infrastructure

- `stacker` crate for dynamic stack growth (deep recursion on mathlib)
- 256 MB worker thread stack in `main.rs`
- Iterative `whnf_no_unfolding_aux` (was recursive, caused stack overflow)
- `GenCache`: generation-counted direct-mapped caches, pre-allocated once, reused across
  declarations via O(1) generation bump. Eliminated 13.6% Init overhead from per-declaration
  memset of shift_eq caches.
- mk_var Vec cache (O(1) lookup by index) and 2-way set-associative mk_app cache (64K entries/1MB,
  lazily allocated after 10K misses). On hit in way-1, promote to way-0 (MRU). On miss,
  evict way-1, move way-0→way-1, insert in way-0. Eliminated billions of hash table lookups
  on pathological declarations. Originally 1M entries (16MB) but reduced to 64K — the 16MB
  cache exceeded L3, causing every access to miss. **14% improvement on Init from right-sizing.**
- `alloc_expr_tc`: When any child has `DagMarker::TcCtx`, the expression cannot exist in the
  export_file dag (PartialEq compares pointer fields, and export_file contains only ExportFile
  pointers). Skips the export_file IndexSet lookup entirely — avoids ~100M L3-miss-inducing
  probes per Init run. Used in mk_app, mk_lambda, mk_pi, mk_let, mk_proj (conditional on
  children), and mk_shift_cutoff (unconditional — Shift nodes never exist in export_file).
  **19.4% improvement on Init, ~20% on Mathlib 10K.**
- Pre-sized per-declaration dag: `LeanDag::with_capacity(16384)` eliminates hashbrown rehash
  overhead (was 2.3% of runtime from repeated doublings during declaration checking).
- `ReusableDag`: Reuses the per-declaration dag's allocated IndexSet memory across declarations
  via `clear_for_reuse()` (clears entries but preserves capacity). Uses `ManuallyDrop` +
  pointer cast to rebind `LeanDag<'static>` to the local TcCtx lifetime (sound because all
  types use PhantomData for lifetimes with identical layout). Eliminates per-declaration
  allocation/deallocation of ~2MB IndexSets. **~20% improvement on Init.**

## Results

### Correctness
- Passes all arena tests: app-lam, dag-app-binder, init (accept);
  constlevels, level-imax-leq, level-imax-normalization (correctly rejected)
- Full Mathlib (630K declarations): 0 errors, 0 timeouts

### Performance

| Benchmark | nanoda | nanobruijn | Ratio |
|-----------|--------|------------|-------|
| Init (54k decls, 310MB) | 26s | 20s | 0.77x |
| app-lam N=4000 | 8.3s | 10ms | 0.001x |
| Mathlib 100K (100k decls) | - | 128s | - |
| Mathlib (630k decls, 4.9GB) | 978s | 1025s | **1.05x** |

### Gap analysis

84% of the gap (501s / 598s) is in the 1-3x ratio band — uniform constant-factor overhead,
not outliers. We save time on 22 declarations (ratio < 0.5) involving tensor products and
categorical diagrams where cross-depth caching avoids recomputation.

**Root cause of the remaining 1.35x gap**: inst shift_down creates new Var nodes. Nanoda's
inst returns `e` UNCHANGED for free variables past the substitution range (Locals are absolute
level refs). Our inst creates `mk_var(k - n_substs)` — a new node that propagates up to
create new App/Pi/Lambda parents, breaking pointer identity for all downstream caches.
The cascade: Shift wrappers → pointer identity divergence → lower cache hit rates →
more whnf/infer calls → more inst calls → more mk_app/mk_var calls.

Per-operation cost is ~2.2x nanoda's, from shift_eq calls, extra expression nodes from
Shift infrastructure, and fvar_union/fvar_shift_cutoff on every mk_app/pi/lambda.

Profile hotspots (Mathlib 100K): mk_app 9.85%, insert_full 7.76%, inst_aux 6.71%,
parsing ~18%, reserve_rehash 3.36%, subst_aux 3.27%, alloc_expr ~3%, whnf_no_unfolding ~3%,
infer_inner ~2.8%, view_expr ~2.6%, shift_eq_aux ~2.4%. inst_cache now uses 4K-entry
direct-mapped Vec with generation counter (eliminated HashMap::insert overhead).

## Paths not taken

These approaches were tried and found counterproductive or unsound:

- **Eager shift resolution** (push_shift in lookup_var, in inst_aux vals): Creates different
  expression identities that cascade poorly through caches. Up to 9x slower.
- **Lazy beta reduction** (push args as let-locals, whnf at higher depth): Changing evaluation
  depth causes catastrophic whnf/wnu cache miss rates (4.2x regression).
- **Negative shifts for below-depth whnf cache hits**: Wrapping stored results in
  `Shift(result, -delta)` or `push_shift(result, -delta, 0)` to lazily defer the shift.
  Crashes: negative Shift wrappers on sub-expressions leak their inner (high-index) Var
  nodes through caches, unfold_apps, and pattern matching. Even `push_shift` (one level)
  fails because it creates `mk_shift_cutoff(child, -delta, 0)` wrappers on children which
  then propagate. Only `push_shift_down` (full eager traversal) works correctly — all Var
  indices are concretely resolved to valid indices at the target depth. The eager approach
  has zero measurable overhead on Init (17K hits, cost offset by avoided recomputation).
  Now implemented: `push_shift_down(stored_result, abs_delta)` with guard
  `result_fvar_lb >= abs_delta`. Lazy negative Shift wrappers are fundamentally incompatible
  with a system where expressions flow through multiple code paths that may read sub-expressions
  directly (via read_expr, unfold_apps, cache lookup) without first resolving Shift wrappers.
- **Negative def_eq caching**: Unsound — def_eq results can change due to side effects from
  intervening comparisons (which may prove sub-expressions equal).
- **Persistent inst_cache across inst_beta calls** (fingerprint-based key): Soundness issues
  from hash collisions (panics with 64-bit fingerprint). Verified cache impractical for
  stack-allocated subst slices.
- **Persistent shift-down for n_substs < 4**: HashMap overhead and eager node creation
  outweigh savings for small substitutions.
- **Canonicalization** (eagerly resolving all Shift nodes): Far too expensive per inst_beta
  result. Also causes infinite recursion when used as a shift cache key (the operation
  preserves structural identity, so lookups find the same entry forever).
- **Depth-sensitive canonical hash** (mixing shift amount into hash): Eliminates cross-depth
  verify-fails but loses 11% of valuable cross-depth cache hits. Net regression.
- **inst_cache DM cache (64K, generation-counted)**: Replacing per-call HashMap with a
  direct-mapped cache at 64K entries (1.3MB). 1.8% slower — the DM cache is in L2/L3
  territory while the per-call HashMap is small and stays in L1. At 4K entries (96KB),
  however, the DM cache with generation counter gives ~3.6% improvement on Init and ~2.7%
  on Mathlib 100K — the O(1) clear (generation bump vs HashMap::clear) and direct slot
  access outweigh the occasional collisions. Now adopted as the inst_cache implementation.
- **Lowering shift-down-only threshold to n_substs >= 1**: 0.4% slower due to HashMap overhead.
- **Various micro-optimizations**: Identity checks in subst_aux/push_shift (branch overhead),
  struct_hash early rejection in shift_eq (most calls are positive matches), mk_app DM cache
  doubling (L2/L3 cache pressure).
- **Speculative Pi/Lambda congruence**: push_local overhead is negligible (0.007% of runtime);
  sem_eq on bodies already tried in quick_check.
- **ExprCache reuse across declarations**: Reusing FxHashMaps across declarations. 2x regression
  because large-declaration HashMap capacity creates L1/L2 cache pressure for small declarations.
- **jemalloc**: 45% regression on Init (35.4s vs 24.5s). glibc's allocator works better for
  this workload's allocation pattern (many small allocations in tight loops).
- **Custom PartialEq for Expr** (only comparing payload fields, not hash/struct_hash/fvar_list):
  17% regression. The compiler optimizes the derived PartialEq into efficient memcmp; the
  match-based custom version has more branching overhead.
- **Wider mk_app DM cache entries** (storing fun+arg+result to avoid read_expr verification):
  No improvement at 64K entries (2MB, L2 pressure offset savings). Neutral at 32K (1MB).
- **whnf_no_unfolding `cur` return shortcut**: Returning `cur` instead of `foldl_apps(e_fun, args)`
  in no-reduction paths. 35% regression — `unfold_apps` normalizes Shift wrappers on args,
  so `cur` still has unnormalized Shift wrappers while `foldl_apps` creates properly normalized
  expressions.
- **shift_eq GenCache reduction** (64K entries): 2x regression on Mathlib. 256K was marginal,
  1M is required for heavy declarations.
- **PGO (Profile-Guided Optimization)**: <1% improvement on Init. Not worth the build complexity.
- **ExprCache reuse across declarations** (with shrink_to cap): 8% regression on Mathlib 100K.
  Same root cause as ExprCache reuse without cap — HashMap capacity from previous declarations
  creates L1/L2 cache pressure even after shrinking. The allocation cost of fresh ExprCache
  per declaration is cheaper than the cache pressure from reused capacity.
- **Precomputed canonical_hash in parallel Vec<u64>**: Store canonical_hash alongside DAG
  expressions for O(1) lookup. No measurable improvement — the saved read_expr calls are
  already cache-hot, and the Vec overhead (compute + push + memory) cancels the savings.
- **subst_cache DM cache** (4K entries, generation-counted): 10% regression. Unlike inst_cache,
  the subst_cache is traversal-based (walks entire subexpression DAG within one call). DM cache
  collisions evict entries needed later in the same traversal, causing subtree re-traversal.
  The per-call HashMap stays in L1 and has zero evictions.
- **alloc_fvar_node DM cache** (1K entries): 20% regression. FVarList nodes have high reuse
  within a declaration; DM cache collisions cause expensive re-traversals in fvar_merge.
- **fvar_list TcCtx check in mk_app/mk_lambda/mk_pi/mk_let**: Skipping export_file probe when
  fvar_list has TcCtx dag_marker. No improvement — when all child pointers are ExportFile,
  fvar_union almost always produces ExportFile results, so the check is rarely true.

## TODO

- **Remove remaining dead code**: thread_local profiling counters, dead locally-nameless
  code (Local variant, FVarId, abstr, etc.)
- **Fill in Theory.lean sorry's**: `decode_shift`, `fvars_shift_zero`

## References

- [Lean Kernel Arena](https://arena.lean-lang.org/) — benchmarks and test cases
- [Arena results](https://leanprover.github.io/lean-kernel-arena/)
- [Kernel implementation analysis](https://gist.github.com/nomeata/b0d8da6857cd2fd4c4a22c03ca404164)
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/title_page.html)
- [Lean Type Theory](https://github.com/digama0/lean-type-theory)
