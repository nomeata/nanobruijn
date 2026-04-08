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

**FVarBloom** (bloom filter for free variable discrimination): Each expression stores a
32-bit bloom filter (`fvar_bloom: u32`) where bit `min(idx, 31)` is set for each free
bvar index `idx`, plus an exact lower bound (`fvar_lb: u16`). All operations are O(1)
bitwise: union = OR, unbind = right-shift by 1, shift = left/right-shift. Replaced the
previous delta-encoded FVarList linked list which required O(n+m) recursive merge with
hash-consed node allocation (was 20% of Mathlib runtime including IndexSet overhead).

Canonical hash = single u64, mixing struct_hash with normalized fvar_bloom via golden
ratio multiply. Normalization: `bloom >> fvar_lb` (shift-invariant).

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
- `expr_nlbv: Vec<u16>` parallel array alongside `IndexSet<Expr>` in both export-file and
  per-declaration dags. `num_loose_bvars(ptr)` reads from this 2-byte Vec instead of the
  full 48-byte Expr. Most impactful for inst_aux's 48.7M early exits (nlbv=0 check) and
  mk_shift's closed-expression elision. **~2% improvement on Init, ~1.2% on Mathlib 100K.**
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
| Init (54k decls, 310MB) | 24.2s | 20.1s | **0.83x** |
| app-lam N=4000 | 8.3s | 10ms | 0.001x |
| Mathlib 100K (100k decls) | - | 128s | - |
| Mathlib (310k decls, 4.9GB) | 898s | ~957s* | **~1.07x*** |

*Estimated from 100K scaling; full Mathlib benchmark pending.

### Gap analysis

On Init we're 18% faster than nanoda, driven by the mk_app DM cache (59% hit rate,
avoids IndexMap lookups). On full Mathlib we're 9% slower.

The shift approach is roughly break-even on heavy declarations: ~11% shift overhead
(view_expr 3.2%, canonical_hash 2.7%, shift_eq_aux 2.4%, mk_shift_cutoff 1.8%,
push_shift 1.0%) is offset by ~11% savings from the mk_app DM cache (IndexMap
get_index_of drops from 13.3% in nanoda to 2.3% in nanobruijn).

The 9% Mathlib gap appears structural — the flat profile (nothing above 15%) means
no single function can be optimized to close the gap. The top hotspot declarations
(AlgebraicGeometry.Scheme, 40s each) have 99.99% DM cache hit rates, so the DM cache
is already maximally effective there. The gap comes from aggregate shift overhead across
~310K declarations.

Profile hotspots (Mathlib last 210K): mk_app 14.7%, inst_aux 10.3%, insert_full 7.6%,
subst_aux 4.4%, whnf_no_unfolding 4.2%, unfold_apps 3.2%, view_expr 3.2%,
canonical_hash 2.7%, shift_eq_aux 2.4%, infer_inner 2.4%, alloc_expr 2.3%,
get_index_of 2.3%, HashMap::insert 2.1%, mk_shift_cutoff 1.8%.

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
- **fvar_lb parallel Vec<u16>**: Store fvar_lb alongside DAG expressions for O(1) lookup,
  avoiding read_expr + read_fvar_node for cache bucketing. 2% regression — same root cause
  as canonical_hash Vec: the push overhead exceeds the read savings.
- **subst_cache DM cache** (4K entries, generation-counted): 10% regression. Unlike inst_cache,
  the subst_cache is traversal-based (walks entire subexpression DAG within one call). DM cache
  collisions evict entries needed later in the same traversal, causing subtree re-traversal.
  The per-call HashMap stays in L1 and has zero evictions.
- **alloc_fvar_node DM cache** (1K entries): 20% regression. FVarList nodes have high reuse
  within a declaration; DM cache collisions cause expensive re-traversals in fvar_merge.
- **fvar_list TcCtx check in mk_app/mk_lambda/mk_pi/mk_let**: Skipping export_file probe when
  fvar_list has TcCtx dag_marker. No improvement — when all child pointers are ExportFile,
  fvar_union almost always produces ExportFile results, so the check is rarely true.
- **Replacing fvar_list with fvar_lb parallel Vec (no bloom)**: Removed delta-encoded FVarList
  linked list from Expr, replaced with O(1) fvar_lb computation from children. Eliminated
  fvar_union (6.33% on Init). But canonical_hash degraded to struct_hash alone (no
  fvar_normalize_hash), causing 15% regression on Mathlib 100K from cache collision increase.
  **Superseded**: the fvar_bloom approach (32-bit bloom filter) provides sufficient discrimination
  for canonical_hash without the linked list overhead. Now adopted as `fvar_bloom: u32` +
  `fvar_lb: u16` in every Expr variant, replacing FVarList entirely.
  **~2.3% improvement on Mathlib 100K** (fvar_union went from 6.33%+14% children = 20% to 0%).

- **Cached constant ExprPtrs** (Bool.true/false, Nat.zero/succ, Nat, String): Cache the
  ExprPtrs for common constants used in nat/bool/string reduction to avoid repeated
  `alloc_levels_slice(&[]) + mk_const` hash table lookups. No measurable improvement —
  these constants are the first entries in their hash tables, so lookups are already O(1).
  The 2.48% `bool_to_expr` profile cost is dominated by inlined surrounding code, not lookups.
- **Lower mk_app DM threshold** (100 misses instead of 1000): Allocating the 1MB DM cache
  earlier to benefit more declarations. Slightly worse — the 1MB allocation for lightweight
  declarations creates L2/L3 cache pressure without enough mk_app calls to amortize it.
- **view_expr #[inline]**: 10% regression on Init from instruction cache pressure.
  The compiler's default inlining decisions are already optimal.
- **target-cpu=native**: Regression. Generic x86-64 code performs better, likely because
  the wider AVX-512 instructions cause frequency throttling on this CPU.
- **Trace counter removal**: Commenting out all 116 `self.trace.xxx += 1` increments.
  15% regression — the compiler uses trace field accesses for register allocation and
  code layout decisions; removing them changes the instruction sequence for the worse.
- **canonical_hash fast-path for closed expressions**: Skip `fvar_normalize_hash` when
  `fvar_list.is_none()`. No measurable improvement — the compiler already optimizes
  `fvar_normalize_hash(None)` to return 0 quickly.

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
