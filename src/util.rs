use crate::env::{DeclarMap, Env, NotationMap, EnvLimit};
use crate::expr::{BinderStyle, Expr, FVarId};
use crate::level::Level;
use crate::name::Name;
use crate::pretty_printer::{PpOptions, PrettyPrinter};
use crate::tc::TypeChecker;
use crate::union_find::UnionFind;
use crate::unique_hasher::UniqueHasher;
use indexmap::{IndexMap, IndexSet};
use num_bigint::BigUint;
use num_traits::{ Pow, identities::Zero };
use num_integer::Integer;
use rustc_hash::FxHasher;
use std::borrow::Cow;
use smallvec::SmallVec;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fs::OpenOptions;
use std::hash::BuildHasherDefault;
use std::io::BufReader;
use std::io::BufWriter;
use std::io::Write;
use std::marker::PhantomData;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use serde::Deserialize;

pub(crate) const fn default_true() -> bool { true }

pub(crate) type UniqueIndexSet<A> = IndexSet<A, BuildHasherDefault<UniqueHasher>>;
pub(crate) type FxIndexSet<A> = IndexSet<A, BuildHasherDefault<FxHasher>>;
pub(crate) type FxIndexMap<K, V> = IndexMap<K, V, BuildHasherDefault<FxHasher>>;
pub(crate) type FxHashMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;
pub(crate) type FxHashSet<K> = HashSet<K, BuildHasherDefault<FxHasher>>;
pub(crate) type UniqueHashMap<K, V> = HashMap<K, V, BuildHasherDefault<UniqueHasher>>;

/// An integer pointer to a kernel item, which can be in either the export file's
/// persistent dag, or the type checking context's temporary dag. The integer pointer
/// is currently 32 bits, which comfortably accommodates mathlib.
///
/// Bit 31 encodes the DagMarker (0 = ExportFile, 1 = TcCtx).
/// Bits 0-30 hold the index into the appropriate dag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ptr<A> {
    raw: u32,
    ph: PhantomData<A>,
}

/// Bit 31 set indicates TcCtx; cleared indicates ExportFile.
const TC_BIT: u32 = 1 << 31;
/// Mask for the 31-bit index stored in bits 0-30.
const IDX_MASK: u32 = !TC_BIT;

impl<A> Ptr<A> {
    pub(crate) fn from(dag_marker: DagMarker, idx: usize) -> Self {
        let idx_u32 = u32::try_from(idx).unwrap();
        assert!(idx_u32 & TC_BIT == 0, "index {idx} exceeds 31-bit capacity");
        let tag = match dag_marker {
            DagMarker::ExportFile => 0,
            DagMarker::TcCtx => TC_BIT,
        };
        Self { raw: tag | idx_u32, ph: PhantomData }
    }

    pub(crate) fn idx(&self) -> usize { (self.raw & IDX_MASK) as usize }

    pub(crate) fn dag_marker(&self) -> DagMarker {
        if self.raw & TC_BIT == 0 { DagMarker::ExportFile } else { DagMarker::TcCtx }
    }

    pub(crate) fn get_hash(&self) -> u64 { self.raw as u64 }
}

impl<A> std::hash::Hash for Ptr<A> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.raw as u64) }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DagMarker {
    ExportFile,
    TcCtx,
}

pub(crate) type CowStr<'a> = Cow<'a, str>;
pub type StringPtr<'a> = Ptr<&'a CowStr<'a>>;
pub type LevelsPtr<'a> = Ptr<&'a Arc<[LevelPtr<'a>]>>;
pub type NamePtr<'a> = Ptr<&'a Name<'a>>;
pub type LevelPtr<'a> = Ptr<&'a Level<'a>>;
pub type ExprPtr<'a> = Ptr<&'a Expr<'a>>;
pub type BigUintPtr<'a> = Ptr<&'a BigUint>;
pub type AppArgs<'a> = SmallVec<[ExprPtr<'a>; 8]>;

pub(crate) fn new_fx_index_map<K, V>() -> FxIndexMap<K, V> { FxIndexMap::with_hasher(Default::default()) }

pub(crate) fn new_fx_hash_map<K, V>() -> FxHashMap<K, V> { FxHashMap::with_hasher(Default::default()) }

pub(crate) fn new_fx_hash_set<K>() -> FxHashSet<K> { FxHashSet::with_hasher(Default::default()) }

pub(crate) fn new_fx_index_set<K>() -> FxIndexSet<K> { FxIndexSet::with_hasher(Default::default()) }
pub(crate) fn new_unique_index_set<K>() -> UniqueIndexSet<K> { UniqueIndexSet::with_hasher(Default::default()) }

pub(crate) fn new_unique_hash_map<K, V>() -> UniqueHashMap<K, V> { UniqueHashMap::with_hasher(Default::default()) }

/// A lazily-allocated hash map: 8 bytes (one null pointer) when empty,
/// only heap-allocates on first insert.
pub(crate) struct LazyMap<K, V>(Option<Box<FxHashMap<K, V>>>);

impl<K, V> LazyMap<K, V> {
    pub(crate) fn new() -> Self { LazyMap(None) }

    pub(crate) fn is_allocated(&self) -> bool { self.0.is_some() }
}

impl<K: Eq + std::hash::Hash, V> LazyMap<K, V> {
    pub(crate) fn get(&self, key: &K) -> Option<&V> {
        self.0.as_ref()?.get(key)
    }

    pub(crate) fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        self.0.as_mut()?.get_mut(key)
    }

    pub(crate) fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.0.get_or_insert_with(|| Box::new(new_fx_hash_map())).insert(key, value)
    }
}

/// A single depth frame: one local context entry plus all per-depth caches.
/// Caches are keyed by ExprPtr (pointer identity, enabled by hash-consing).
pub(crate) struct DepthFrame<'t> {
    /// The local binding: (type, optional value for let-bindings).
    pub(crate) local: (ExprPtr<'t>, Option<ExprPtr<'t>>),
    /// Per-depth whnf cache: ExprPtr → result.
    pub(crate) whnf_cache: LazyMap<ExprPtr<'t>, ExprPtr<'t>>,
    /// Per-depth whnf_no_unfolding cache.
    pub(crate) whnf_no_unfolding_cache: LazyMap<ExprPtr<'t>, ExprPtr<'t>>,
    /// Per-depth infer cache (check mode): ExprPtr → result.
    pub(crate) infer_cache_check: LazyMap<ExprPtr<'t>, ExprPtr<'t>>,
    /// Per-depth infer cache (no-check mode): ExprPtr → result.
    pub(crate) infer_cache_no_check: LazyMap<ExprPtr<'t>, ExprPtr<'t>>,
    /// Per-depth positive def_eq cache for open expressions.
    pub(crate) defeq_pos_open: LazyMap<(ExprPtr<'t>, ExprPtr<'t>), (ExprPtr<'t>, ExprPtr<'t>, u16)>,
    /// Per-depth negative def_eq cache for open expressions.
    pub(crate) defeq_neg_open: LazyMap<(ExprPtr<'t>, ExprPtr<'t>), (ExprPtr<'t>, ExprPtr<'t>, u16)>,
}

impl<'t> DepthFrame<'t> {
    pub(crate) fn new(ty: ExprPtr<'t>, val: Option<ExprPtr<'t>>) -> Self {
        DepthFrame {
            local: (ty, val),
            whnf_cache: LazyMap::new(),
            whnf_no_unfolding_cache: LazyMap::new(),
            infer_cache_check: LazyMap::new(),
            infer_cache_no_check: LazyMap::new(),
            defeq_pos_open: LazyMap::new(),
            defeq_neg_open: LazyMap::new(),
        }
    }
}

/// Convenience macro for creating a 64 bit hash.
#[macro_export]
macro_rules! hash64 {
    ( $( $x:expr ),* ) => {
        {
            use std::hash::{ Hash, Hasher };
            let mut hasher = rustc_hash::FxHasher::default();
            $(
                ($x).hash(&mut hasher);
            )*
            hasher.finish()
        }
    };
}

/// The implementation of natural number subtraction used in the kernel extension
/// for nat literals.
///
/// This is different from the subtraction defined for `BigUint` in that we saturate
/// at zero if y > x
pub(crate) fn nat_sub(x: BigUint, y: BigUint) -> BigUint {
    if y > x {
        BigUint::zero()
    } else {
        x - y
    }
}

/// The implementation of natural number division used in the kernel extension
/// for nat literals.
///
/// This is different from the division defined for `BigUint` in that division
/// by zero is an error for `BigUint`, but in Lean, it returns 0.
pub(crate) fn nat_div(x: BigUint, y: BigUint) -> BigUint {
    if y.is_zero() {
        BigUint::zero()
    } else {
        x / y
    }
}

/// The implementation of natural number mod used in the kernel extension
/// for nat literals.
pub(crate) fn nat_mod(x: BigUint, y: BigUint) -> BigUint {
    if y.is_zero() {
        x
    } else {
        x % y
    }
}

pub(crate) fn nat_gcd(x: &BigUint, y: &BigUint) -> BigUint {
    x.gcd(y)
}

pub(crate) fn nat_xor(x: &BigUint, y: &BigUint) -> BigUint {
    x ^ y
}

pub(crate) fn nat_shl(x: BigUint, y: BigUint) -> BigUint {
    x * BigUint::from(2u8).pow(y)
}

pub(crate) fn nat_shr(x: BigUint, y: BigUint) -> BigUint {
    x / BigUint::from(2u8).pow(y)
}

pub(crate) fn nat_land(x: BigUint, y: BigUint) -> BigUint {
    x & y
}
pub(crate) fn nat_lor(x: BigUint, y: BigUint) -> BigUint {
    x | y
}

pub struct ExprCache<'t> {
    /// Caches (e, substs_id, params) |-> output for instantiation.
    /// Persistent across inst/inst_beta calls within a declaration — substs identity
    /// is encoded in substs_id (hash of substitution values + shift_down flag).
    /// inst_cache key: (expr, substs_id, offset | sh_amt << 16 | sh_cut << 32) -> result.
    pub(crate) inst_cache: Vec<(u64, u64, ExprPtr<'t>, ExprPtr<'t>)>,  // (substs_id, params, key_expr, result)
    /// Current substs identity for inst_cache. Set at the start of each inst/inst_beta call.
    pub(crate) inst_substs_id: u64,
    /// Caches (e, ks, vs) |-> output for level substitution.
    pub(crate) subst_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), ExprPtr<'t>>,
    pub(crate) dsubst_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), ExprPtr<'t>>,
    /// Caches (e, offset) |-> output for abstraction (re-binding free variables).
    /// This cache is reset before every new call to `inst`, so there's no need to
    /// cache the sequence of free variables.
    pub(crate) abstr_cache: FxHashMap<(ExprPtr<'t>, u16), ExprPtr<'t>>,
    /// Caches (e, amount, cutoff) |-> output for shifting.
    pub(crate) shift_cache: FxHashMap<(ExprPtr<'t>, u16, u16), ExprPtr<'t>>,
    /// Caches (e, amount, cutoff) |-> output for downward shifting (amount subtracted from free vars >= cutoff).
    pub(crate) shift_down_cache: FxHashMap<(ExprPtr<'t>, u16, u16), ExprPtr<'t>>,
    /// Cache for abstr_aux_levels (nanoda TC): (expr, start_pos, num_open_binders) -> expr
    pub(crate) abstr_cache_levels: FxHashMap<(ExprPtr<'t>, u16, u16), ExprPtr<'t>>,
    /// Dedup table for Shift nodes: (inner, amount, cutoff) → ExprPtr.
    /// Ensures mk_shift(a, k) always returns the same ExprPtr,
    /// enabling O(1) pointer equality in cache verification.
    pub(crate) shift_dedup: FxHashMap<(ExprPtr<'t>, u16, u16), ExprPtr<'t>>,
    /// Direct-mapped mk_app cache, lazily allocated after enough misses.
    /// Avoids 16MB alloc for trivial declarations while speeding up heavy ones.
    pub(crate) mk_app_dm_cache: Vec<(u64, ExprPtr<'t>, ExprPtr<'t>, ExprPtr<'t>)>,
    pub(crate) mk_app_miss_count: u32,
    /// Memoization cache for mk_pi: (name, style, type, body) → ExprPtr.
    pub(crate) mk_pi_cache: FxHashMap<(NamePtr<'t>, BinderStyle, ExprPtr<'t>, ExprPtr<'t>), ExprPtr<'t>>,
    /// Memoization cache for mk_lambda: (name, style, type, body) → ExprPtr.
    pub(crate) mk_lambda_cache: FxHashMap<(NamePtr<'t>, BinderStyle, ExprPtr<'t>, ExprPtr<'t>), ExprPtr<'t>>,
    /// Direct-mapped cache for mk_var: index → ExprPtr.
    /// Since dbj_idx is u16, we use a Vec of Option<ExprPtr> for O(1) lookup.
    pub(crate) mk_var_cache: Vec<Option<ExprPtr<'t>>>,
}

impl<'t> ExprCache<'t> {
    fn new() -> Self {
        Self {
            inst_cache: Vec::new(),
            inst_substs_id: 0,
            abstr_cache: new_fx_hash_map(),
            subst_cache: new_fx_hash_map(),
            dsubst_cache: new_fx_hash_map(),
            shift_cache: new_fx_hash_map(),
            shift_down_cache: new_fx_hash_map(),
            abstr_cache_levels: new_fx_hash_map(),
            shift_dedup: new_fx_hash_map(),
            mk_app_dm_cache: Vec::new(),
            mk_app_miss_count: 0,
            mk_pi_cache: new_fx_hash_map(),
            mk_lambda_cache: new_fx_hash_map(),
            mk_var_cache: Vec::new(),
        }
    }

}

/// Type-erased LeanDag for reuse across declarations.
/// The inner LeanDag<'static> is always cleared before being transmuted to the correct lifetime.
pub struct ReusableDag(LeanDag<'static>);

impl ReusableDag {
    pub fn new(config: &Config) -> Self {
        ReusableDag(LeanDag::with_capacity(config, 16384))
    }
}

pub const MK_APP_CACHE_SIZE: usize = 1 << 16; // 64K entries (1MB)
pub const MK_APP_DM_THRESHOLD: u32 = 1_000; // allocate DM cache after this many misses
pub const INST_CACHE_SIZE: usize = 1 << 16; // 64K entries for inst_cache DM

pub struct ExportFile<'p> {
    /// The underlying storage for `Name`, `Level`, and `Expr` items (and Strings).
    pub(crate) dag: LeanDag<'p>,
    /// Declarations from the export file
    pub declars: DeclarMap<'p>,
    /// Notations from the export file
    pub notations: NotationMap<'p>,
    /// Cached names for convenience (`Quot`, `Nat`, etc.)
    pub name_cache: NameCache<'p>,
    pub config: Config,
    // Information used for setting EnvLimit during inductive checking.
    pub mutual_block_sizes: FxHashMap<NamePtr<'p>, (usize, usize)>,
    /// OSNF core map: for each export file expression, the index of its OSNF core in the DAG.
    /// osnf_core[i] = i means no OSNF normalization needed (fvar_lb == 0 or closed).
    /// osnf_core[i] = j (j != i) means expression i has OSNF core at j with fvar_lb shift.
    pub(crate) osnf_core: Option<Vec<u32>>,
}

impl<'p> ExportFile<'p> {
    pub fn new_env(&self, env_limit: EnvLimit<'p>) -> Env<'_, '_> { Env::new(&self.declars, &self.notations, env_limit) }

    pub fn with_ctx<F, A>(&self, f: F) -> A
    where
        F: FnOnce(&mut TcCtx<'_, 'p>) -> A, {
        let mut dag = LeanDag::new(&self.config);
        let mut ctx = TcCtx::new(self, &mut dag);
        f(&mut ctx)
    }

    pub fn with_tc<F, A>(&self, env_limit: EnvLimit, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, '_, 'p>) -> A, {
        let mut dag = LeanDag::new(&self.config);
        let mut ctx = TcCtx::new(self, &mut dag);
        let env = self.new_env(env_limit);
        let mut tc = TypeChecker::new(&mut ctx, &env, None);
        f(&mut tc)
    }

    pub fn with_tc_and_declar<F, A>(&self, d: crate::env::DeclarInfo<'p>, f: F) -> (A, TcTrace)
    where
        F: FnOnce(&mut TypeChecker<'_, '_, 'p>) -> A, {
        self.with_tc_and_declar_reusing(d, ReusableDag::new(&self.config), f).0
    }

    /// Like `with_tc_and_declar`, but reuses pre-allocated dag across declarations.
    /// The dag is passed as `ReusableDag` (type-erased) and rebound to the correct lifetime.
    pub fn with_tc_and_declar_reusing<F, A>(&self, d: crate::env::DeclarInfo<'p>, reusable_dag: ReusableDag, f: F) -> ((A, TcTrace), ReusableDag)
    where
        F: FnOnce(&mut TypeChecker<'_, '_, 'p>) -> A, {
        // SAFETY: ReusableDag wraps LeanDag<'static>. After clear_for_reuse(), the IndexSets
        // are empty (only Anon/Zero sentinels which are 'static). All types use PhantomData
        // for lifetimes — identical layout across all lifetimes.
        let mut dag_storage = std::mem::ManuallyDrop::new(reusable_dag.0);
        let dag_ref: &mut LeanDag<'_> = unsafe { &mut *(&mut *dag_storage as *mut LeanDag<'static>).cast() };
        dag_ref.clear_for_reuse();
        let mut ctx = TcCtx::new(self, dag_ref);
        let env = self.new_env(EnvLimit::ByName(d.name));
        let mut tc = TypeChecker::new(&mut ctx, &env, Some(d));
        let result = f(&mut tc);
        let mut trace = tc.ctx.trace;
        trace.dag_size = tc.ctx.dag.exprs.len() as u64;
        drop(tc);
        drop(ctx);
        // Reclaim ownership and erase lifetime back to 'static.
        let reusable_dag = ReusableDag(std::mem::ManuallyDrop::into_inner(dag_storage));
        ((result, trace), reusable_dag)
    }

    pub fn with_nanoda_tc_and_declar<F, A>(&self, d: crate::env::DeclarInfo<'p>, f: F) -> (A, TcTrace)
    where
        F: FnOnce(&mut crate::nanoda_tc::NanodaTypeChecker<'_, '_, 'p>) -> A, {
        let mut dag = LeanDag::new(&self.config);
        let mut ctx = TcCtx::new(self, &mut dag);
        let env = self.new_env(EnvLimit::ByName(d.name));
        let mut tc = crate::nanoda_tc::NanodaTypeChecker::new(&mut ctx, &env, Some(d));
        let result = f(&mut tc);
        let trace = tc.ctx.trace;
        (result, trace)
    }

    /// Like `with_nanoda_tc_and_declar`, but reuses pre-allocated dag across declarations.
    pub fn with_nanoda_tc_and_declar_reusing<F, A>(&self, d: crate::env::DeclarInfo<'p>, reusable_dag: ReusableDag, f: F) -> ((A, TcTrace), ReusableDag)
    where
        F: FnOnce(&mut crate::nanoda_tc::NanodaTypeChecker<'_, '_, 'p>) -> A, {
        let mut dag_storage = std::mem::ManuallyDrop::new(reusable_dag.0);
        let dag_ref: &mut LeanDag<'_> = unsafe { &mut *(&mut *dag_storage as *mut LeanDag<'static>).cast() };
        dag_ref.clear_for_reuse();
        let mut ctx = TcCtx::new(self, dag_ref);
        let env = self.new_env(EnvLimit::ByName(d.name));
        let mut tc = crate::nanoda_tc::NanodaTypeChecker::new(&mut ctx, &env, Some(d));
        let result = f(&mut tc);
        let trace = tc.ctx.trace;
        drop(tc);
        drop(ctx);
        let reusable_dag = ReusableDag(std::mem::ManuallyDrop::into_inner(dag_storage));
        ((result, trace), reusable_dag)
    }

    pub fn with_pp<F, A>(&self, f: F) -> A
    where
        F: FnOnce(&mut PrettyPrinter<'_, '_, 'p>) -> A, {
        self.with_ctx(|ctx| ctx.with_pp(f))
    }
}

/// A structure representing the memory context used for an individual `TypeChecker`.
pub struct TcCtx<'t, 'p> {
    //anchor: PhantomData<&'t AnchorZst>,
    /// Each type checker's context shares an immutable reference to the structured contents of
    /// the export file, and some additional information taken from the export file.
    pub(crate) export_file: &'t ExportFile<'p>,
    /// The underlying storage for temporary `Name`, `Level`, and `Expr`` items created while
    /// type checking a declaration. These are dropped once the declaration is verified, since
    /// they are no longer needed.
    pub(crate) dag: &'t mut LeanDag<'t>,
    /// Non-monotonic deBruijn level counter (nanoda TC compatibility).
    /// Tracks the current number of open binders.
    pub(crate) dbj_level_counter: u16,
    /// Monotonically increasing counter for unique free variables. Any two free variables created
    /// with the `mk_unique` constructor are unique within their `(ExportFile, TcCtx)` pair.
    pub(crate) unique_counter: u32,
    /// A cache for instantiation, free variable abstraction, and level substitution
    pub(crate) expr_cache: ExprCache<'t>,
    pub(crate) eager_mode: bool,
    /// Heartbeat counter: incremented in hot paths. When a deadline is set,
    /// checked periodically to enforce per-declaration timeouts.
    pub(crate) heartbeat: u64,
    /// Deadline for the current declaration (None = no timeout).
    pub(crate) deadline: Option<std::time::Instant>,
    /// Tracing counters for A/B comparison.
    pub(crate) trace: TcTrace,
}

/// Counters for tracing TC operations (A/B comparison between shift and nanoda TCs).
#[derive(Default, Clone, Copy)]
pub struct TcTrace {
    pub def_eq_calls: u64,
    pub whnf_calls: u64,
    pub infer_calls: u64,
    pub inst_calls: u64,
    pub alloc_expr_calls: u64,
    pub whnf_cache_hits: u64,
    pub eq_cache_hits: u64,
    pub eq_cache_uf_hits: u64,
    pub eq_cache_verify_fail: u64,
    pub fail_cache_verify_fail: u64,
    pub eq_cache_overflow_stores: u64,
    pub eq_cache_overflow_hits: u64,
    pub eq_cache_cross_depth_hits: u64,  // hit where stored_ptr != query_ptr (cross-depth)
    pub fail_cache_overflow_stores: u64,
    pub fail_cache_overflow_hits: u64,
    pub infer_cache_hits: u64,
    pub push_shift_calls: u64,
    pub inst_aux_calls: u64,
    pub inst_aux_cache_hits: u64,
    pub inst_aux_elided: u64,
    pub inst_aux_shift_nodes: u64,
    pub inst_aux_shift_mismatch: u64,
    pub inst_aux_shift_compose: u64,   // shift composition: cutoff < sh_cut but amount >= sh_cut - cutoff
    pub inst_aux_shifted_path: u64,   // calls where sh_amt > 0
    pub inst_aux_shifted_alloc: u64,  // mk_app/mk_pi/etc in sh_amt > 0 path
    pub inst_aux_shifted_var_subst: u64, // var actually substituted in shift path
    pub inst_aux_shifted_var_nosubst: u64, // var NOT substituted in shift path (pure shift)
    pub inst_aux_nonshift_identity: u64, // identity check saved alloc in sh_amt == 0 path
    pub inst_aux_shifted_identity: u64,  // identity check saved alloc in shift path
    pub inst_aux_shift_skip_clean: u64,  // shift-skip optimization: sh_amt == n_substs (no wrapper)
    pub inst_aux_shift_skip_wrap: u64,   // shift-skip optimization: sh_amt > n_substs (creates Shift wrapper)
    pub spec_app_tried: u64,             // speculative app congruence attempts
    pub spec_app_hit: u64,               // speculative app congruence successes
    pub spec_app2_tried: u64,            // spec_app after whnf_cheap_proj attempts
    pub spec_app2_hit: u64,              // spec_app after whnf_cheap_proj successes
    pub push_shift_cache_hits: u64,
    pub infer_cache_hash_hit: u64,
    pub infer_cache_verify_fail: u64,
    pub dag_size: u64,
    pub zeta_reductions: u64,
    pub whnf_let_reductions: u64,
    pub whnf_beta_reductions: u64,
    pub wnu_calls: u64,
    pub wnu_cache_hits: u64,
    pub wnu_shift_peel: u64,
    pub infer_shift_peel: u64,
    pub whnf_shift_peel: u64,
    pub shift_peel_frames_total: u64,
    pub shift_peel_nanos: u64,
    // whnf cache miss breakdown
    pub whnf_cache_no_bucket: u64,
    pub whnf_cache_no_entry: u64,
    pub whnf_cache_verify_fail: u64,
    pub whnf_cache_vf_same: u64,   // same depth, verify fail
    pub whnf_cache_vf_above: u64,  // depth > stored, verify fail
    pub whnf_cache_vf_below: u64,  // depth < stored, verify fail
    pub whnf_cache_vf_sign_would_fix: u64, // sign(ub_f - ub_a) would have discriminated
    pub whnf_cache_vf_evictions: u64,     // times a collision caused eviction of a different expression
    pub whnf_cache_overflow_stores: u64,
    pub whnf_cache_overflow_hits: u64,
    // infer cache verify-fail breakdown
    pub infer_cache_vf_check_flag: u64,   // entry was InferOnly but query is Check
    pub infer_cache_vf_same: u64,         // same depth, verify fail
    pub infer_cache_vf_above: u64,        // depth > stored, verify fail
    pub infer_cache_vf_below: u64,        // depth < stored, not attempted
    pub infer_cache_vf_sign_would_fix: u64, // nlbv_sign would have discriminated
    pub infer_cache_overflow_stores: u64,
    pub infer_cache_overflow_hits: u64,
    // open defeq cache
    pub defeq_open_pos_hits: u64,
    pub defeq_open_neg_hits: u64,
    pub def_eq_inner_calls: u64,
    pub def_eq_deep_calls: u64,  // survived both quick_checks, entering lazy_delta
    pub shift_dedup_hits: u64,
    pub osnf_canon_hits: u64,
    // wnu cache miss breakdown
    pub wnu_cache_no_bucket: u64,
    pub wnu_cache_no_entry: u64,
    pub wnu_cache_verify_fail: u64,
    pub wnu_cache_overflow_stores: u64,
    pub wnu_cache_overflow_hits: u64,
    // below-depth analysis: how many are true shift variants
    pub whnf_vf_below_is_shift: u64,
    pub whnf_below_depth_hits: u64,
    pub infer_vf_below_is_shift: u64,
    // per-function alloc counters (mk_* cache misses that call alloc_expr)
    pub alloc_mk_app: u64,
    pub alloc_mk_pi: u64,
    pub alloc_mk_lambda: u64,
    pub alloc_mk_let: u64,
    pub alloc_mk_var: u64,
    pub alloc_mk_shift: u64,
    pub alloc_mk_proj: u64,
    pub alloc_mk_other: u64,
    pub alloc_mk_app_cache_hit: u64,
    // wnu cache store breakdown
    pub wnu_cache_new_inserts: u64,
    pub wnu_cache_update_lower: u64,
    pub wnu_cache_update_higher: u64,
    pub wnu_cache_update_skip: u64,
}

impl std::fmt::Display for TcTrace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "def_eq={} dei={}/{} whnf={} infer={} inst={} alloc={} | hits: whnf={} eq={}/vf{} uf={} dop={}/{} sd={} infer={} infer_hash={} infer_vfail={} | ps={}/{} | inst_aux={}/{}/{} sh={}/{}/{}",
            self.def_eq_calls, self.def_eq_inner_calls, self.def_eq_deep_calls, self.whnf_calls, self.infer_calls,
            self.inst_calls, self.alloc_expr_calls,
            self.whnf_cache_hits, self.eq_cache_hits, self.eq_cache_verify_fail, self.eq_cache_uf_hits,
            self.defeq_open_pos_hits, self.defeq_open_neg_hits,
            self.shift_dedup_hits,
            self.infer_cache_hits,
            self.infer_cache_hash_hit, self.infer_cache_verify_fail,
            self.push_shift_calls, self.push_shift_cache_hits,
            self.inst_aux_calls, self.inst_aux_cache_hits, self.inst_aux_elided,
            self.inst_aux_shift_nodes, self.inst_aux_shift_mismatch, self.inst_aux_shift_compose)?;
        write!(f, " | sh_path={} sh_alloc={}/{} sh_var={}/{} nsh_id={} skip={}/{}",
            self.inst_aux_shifted_path, self.inst_aux_shifted_alloc, self.inst_aux_shifted_identity,
            self.inst_aux_shifted_var_subst, self.inst_aux_shifted_var_nosubst,
            self.inst_aux_nonshift_identity,
            self.inst_aux_shift_skip_clean, self.inst_aux_shift_skip_wrap)?;
        if self.spec_app_tried > 0 {
            write!(f, " | spec={}/{} spec2={}/{}", self.spec_app_hit, self.spec_app_tried,
                self.spec_app2_hit, self.spec_app2_tried)?;
        }
        if self.zeta_reductions > 0 || self.whnf_let_reductions > 0 || self.wnu_calls > 0 {
            write!(f, " | zeta={} wlet={} wbeta={} dag={} wnu={}/{}/{} wnu_miss={}/{}/{} wnuov={}/{} peel={}/{}/{}/{}f", self.zeta_reductions, self.whnf_let_reductions, self.whnf_beta_reductions, self.dag_size, self.wnu_calls, self.wnu_cache_hits, self.wnu_shift_peel, self.wnu_cache_no_bucket, self.wnu_cache_no_entry, self.wnu_cache_verify_fail, self.wnu_cache_overflow_stores, self.wnu_cache_overflow_hits, self.infer_shift_peel, self.whnf_shift_peel, self.wnu_shift_peel, self.shift_peel_frames_total)?;
        }
        if self.whnf_cache_verify_fail > 0 {
            write!(f, " | wmiss={}/{}/{} vf={}/{}/{} below_shift={}/{} sign_fix={} evict={} ov_store={} ov_hit={}", self.whnf_cache_no_bucket, self.whnf_cache_no_entry, self.whnf_cache_verify_fail, self.whnf_cache_vf_same, self.whnf_cache_vf_above, self.whnf_cache_vf_below, self.whnf_vf_below_is_shift, self.whnf_below_depth_hits, self.whnf_cache_vf_sign_would_fix, self.whnf_cache_vf_evictions, self.whnf_cache_overflow_stores, self.whnf_cache_overflow_hits)?;
        }
        if self.infer_cache_verify_fail > 0 {
            write!(f, " | ivf={}/{}/{}/{} ibelow_shift={} isign_fix={} iov_store={} iov_hit={}", self.infer_cache_vf_check_flag, self.infer_cache_vf_same, self.infer_cache_vf_above, self.infer_cache_vf_below, self.infer_vf_below_is_shift, self.infer_cache_vf_sign_would_fix, self.infer_cache_overflow_stores, self.infer_cache_overflow_hits)?;
        }
        if self.eq_cache_verify_fail > 0 || self.fail_cache_verify_fail > 0 || self.eq_cache_overflow_hits > 0 || self.fail_cache_overflow_hits > 0 {
            write!(f, " | eqvf={}/{} eqov={}/{}/{}/{} eqxd={}",
                self.eq_cache_verify_fail, self.fail_cache_verify_fail,
                self.eq_cache_overflow_stores, self.eq_cache_overflow_hits,
                self.fail_cache_overflow_stores, self.fail_cache_overflow_hits,
                self.eq_cache_cross_depth_hits)?;
        }
        write!(f, " | wnu_st={}/{}/{}/{}", self.wnu_cache_new_inserts, self.wnu_cache_update_lower, self.wnu_cache_update_higher, self.wnu_cache_update_skip)?;
        if self.osnf_canon_hits > 0 { write!(f, " | osnf={}", self.osnf_canon_hits)?; }
        write!(f, " | mka={}/{} mkp={} mkl={} mklt={} mkv={} mks={} mkpr={} mko={}",
            self.alloc_mk_app, self.alloc_mk_app_cache_hit,
            self.alloc_mk_pi, self.alloc_mk_lambda, self.alloc_mk_let,
            self.alloc_mk_var, self.alloc_mk_shift, self.alloc_mk_proj, self.alloc_mk_other)?;
        Ok(())
    }
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    pub fn new(export_file: &'t ExportFile<'p>, tdag: &'t mut LeanDag<'t>) -> Self {
        Self {
            export_file,
            dag: tdag,
            dbj_level_counter: 0u16,
            unique_counter: 0u32,
            expr_cache: ExprCache::new(),
            eager_mode: false,
            heartbeat: 0,
            deadline: if export_file.config.declaration_timeout_secs > 0 {
                Some(std::time::Instant::now() + std::time::Duration::from_secs(export_file.config.declaration_timeout_secs))
            } else {
                None
            },
            trace: TcTrace::default(),
        }
    }

    pub fn with_tc<F, A>(&mut self, env_limit: EnvLimit<'p>, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't, 'p>) -> A, {
        let env = self.export_file.new_env(env_limit);
        let mut tc = TypeChecker::new(self, &env, None);
        f(&mut tc)
    }

    pub fn with_tc_and_env_ext<'x, F, A>(&mut self, env_ext: &'x DeclarMap<'t>, env_limit: EnvLimit<'p>, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, 't, 'p>) -> A, {
        let env = crate::env::Env::new_w_temp_ext(&self.export_file.declars, Some(env_ext), &self.export_file.notations, env_limit);
        let mut tc = TypeChecker::new(self, &env, None);
        f(&mut tc)
    }

    pub fn with_pp<F, A>(&mut self, f: F) -> A
    where
        F: FnOnce(&mut PrettyPrinter<'_, 't, 'p>) -> A, {
        f(&mut PrettyPrinter::new(self))
    }

    pub fn read_name(&self, p: NamePtr<'t>) -> Name<'t> {
        match p.dag_marker() {
            DagMarker::ExportFile => self.export_file.dag.names.get_index(p.idx()).copied().unwrap(),
            DagMarker::TcCtx => self.dag.names.get_index(p.idx()).copied().unwrap(),
        }
    }

    /// Convenience function for reading two items as a tuple.
    pub fn read_name_pr(&self, p: NamePtr<'t>, q: NamePtr<'t>) -> (Name<'t>, Name<'t>) {
        (self.read_name(p), self.read_name(q))
    }

    pub fn read_level(&self, p: LevelPtr<'t>) -> Level<'t> {
        match p.dag_marker() {
            DagMarker::ExportFile => self.export_file.dag.levels.get_index(p.idx()).copied().unwrap(),
            DagMarker::TcCtx => self.dag.levels.get_index(p.idx()).copied().unwrap(),
        }
    }

    /// Convenience function for reading two items as a tuple.
    pub fn read_level_pair(&self, a: LevelPtr<'t>, x: LevelPtr<'t>) -> (Level<'t>, Level<'t>) {
        (self.read_level(a), self.read_level(x))
    }

    pub fn read_expr(&self, p: ExprPtr<'t>) -> Expr<'t> {
        match p.dag_marker() {
            DagMarker::ExportFile => self.export_file.dag.exprs.get_index(p.idx()).copied().unwrap(),
            DagMarker::TcCtx => self.dag.exprs.get_index(p.idx()).copied().unwrap(),
        }
    }

    /// Convenience function for reading two items as a tuple.
    pub fn read_expr_pair(&self, a: ExprPtr<'t>, x: ExprPtr<'t>) -> (Expr<'t>, Expr<'t>) {
        (self.read_expr(a), self.read_expr(x))
    }

    /// Like read_expr_pair but with Shift pushed one level inside.
    pub fn view_expr_pair(&mut self, a: ExprPtr<'t>, x: ExprPtr<'t>) -> (Expr<'t>, Expr<'t>) {
        let va = self.view_expr(a);
        let vx = self.view_expr(x);
        (va, vx)
    }

    pub fn read_string(&self, p: StringPtr<'t>) -> &CowStr<'t> {
        match p.dag_marker() {
            DagMarker::ExportFile => self.export_file.dag.strings.get_index(p.idx()).unwrap(),
            DagMarker::TcCtx => self.dag.strings.get_index(p.idx()).unwrap(),
        }
    }

    pub fn read_bignum(&self, p: BigUintPtr<'t>) -> Option<&BigUint> {
        match p.dag_marker() {
            DagMarker::ExportFile => Some(self.export_file.dag.bignums.as_ref()?.get_index(p.idx()).unwrap()),
            DagMarker::TcCtx => Some(self.dag.bignums.as_ref()?.get_index(p.idx()).unwrap()),
        }
    }

    pub fn read_levels(&self, p: LevelsPtr<'t>) -> Arc<[LevelPtr<'t>]> {
        match p.dag_marker() {
            DagMarker::ExportFile => self.export_file.dag.uparams.get_index(p.idx()).cloned().unwrap(),
            DagMarker::TcCtx => self.dag.uparams.get_index(p.idx()).cloned().unwrap(),
        }
    }

    /// Store a `Name`, getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Checks the longer-lived storage first.
    pub fn alloc_name(&mut self, n: Name<'t>) -> NamePtr<'t> {
        if let Some(idx) = self.export_file.dag.names.get_index_of(&n) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else {
            Ptr::from(DagMarker::TcCtx, self.dag.names.insert_full(n).0)
        }
    }

    /// Store a `Level`, getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Checks the longer-lived storage first.
    pub fn alloc_level(&mut self, l: Level<'t>) -> LevelPtr<'t> {
        if let Some(idx) = self.export_file.dag.levels.get_index_of(&l) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else {
            Ptr::from(DagMarker::TcCtx, self.dag.levels.insert_full(l).0)
        }
    }

    /// Store an `Expr`, getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Checks the longer-lived storage first.
    pub fn alloc_expr(&mut self, e: Expr<'t>) -> ExprPtr<'t> {
        self.trace.alloc_expr_calls += 1;
        if let Some(idx) = self.export_file.dag.exprs.get_index_of(&e) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else {
            let nlbv = e.num_loose_bvars();
            let fvar_lb = e.get_fvar_lb();
            let (idx, inserted) = self.dag.exprs.insert_full(e);
            if inserted { self.dag.expr_nlbv.push(nlbv); self.dag.expr_fvar_lb.push(fvar_lb); }
            Ptr::from(DagMarker::TcCtx, idx)
        }
    }

    /// Store a string (a `CowStr`), getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Checks the longer-lived storage first.
    pub(crate) fn alloc_string(&mut self, s: CowStr<'t>) -> StringPtr<'t> {
        if let Some(idx) = self.export_file.dag.strings.get_index_of(&s) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else {
            Ptr::from(DagMarker::TcCtx, self.dag.strings.insert_full(s).0)
        }
    }

    /// Store a `BigUint` (a bignum), getting back a pointer to the allocated item. If the item was
    /// already stored, forego the allocation and return a pointer to the previously inserted
    /// element. Checks the longer-lived storage first.
    ///
    /// Used for Nat literals.
    pub(crate) fn alloc_bignum(&mut self, n: BigUint) -> Option<BigUintPtr<'t>> {
        if let Some(idx) = self.export_file.dag.bignums.as_ref()?.get_index_of(&n) {
            Some(Ptr::from(DagMarker::ExportFile, idx))
        } else {
            Some(Ptr::from(DagMarker::TcCtx, self.dag.bignums.as_mut()?.insert_full(n).0))
        }
    }

    /// Store a sequence of `Level` items, getting back a pointer to the allocated sequence.
    /// If the sequence was already stored, return a pointer to the previously inserted sequence.
    /// Checks the longer-lived storage first.
    pub fn alloc_levels(&mut self, ls: Arc<[LevelPtr<'t>]>) -> LevelsPtr<'t> {
        if let Some(idx) = self.export_file.dag.uparams.get_index_of(&ls) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else {
            Ptr::from(DagMarker::TcCtx, self.dag.uparams.insert_full(ls).0)
        }
    }

    /// Store a sequence of `Level` items, but check whether the sequence has previously been allocated
    /// first, by probing with a slice.
    pub fn alloc_levels_slice(&mut self, ls: &[LevelPtr<'t>]) -> LevelsPtr<'t> {
        if let Some(idx) = self.export_file.dag.uparams.get_index_of(ls) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else if let Some(idx) = self.dag.uparams.get_index_of(ls) {
            Ptr::from(DagMarker::TcCtx, idx)
        } else {
            Ptr::from(DagMarker::TcCtx, self.dag.uparams.insert_full(Arc::from(ls)).0)
        }
    }

    /// Format a name as a string (for diagnostics).
    pub fn name_to_string(&self, n: NamePtr<'t>) -> String {
        match self.read_name(n) {
            crate::name::Name::Anon => String::new(),
            crate::name::Name::Str(pfx, sfx, _) => {
                let mut out = self.name_to_string(pfx);
                if !out.is_empty() { out.push('.'); }
                out.push_str(self.read_string(sfx).as_ref());
                out
            }
            crate::name::Name::Num(pfx, sfx, _) => {
                let mut out = self.name_to_string(pfx);
                if !out.is_empty() { out.push('.'); }
                out.push_str(&format!("{}", sfx));
                out
            }
        }
    }

    /// Compact expression descriptor for diagnostics: tag + key info.
    /// Returns e.g. "App(Const(Eq),nlbv=3,fvl={2,5})" or "Var(7)"
    pub fn expr_desc(&self, e: ExprPtr<'t>, max_depth: u32) -> String {
        if max_depth == 0 { return "...".to_string(); }
        match self.read_expr(e) {
            Expr::Var { dbj_idx, .. } => format!("V{}", dbj_idx),
            Expr::Sort { .. } => "Sort".to_string(),
            Expr::Const { name, .. } => {
                let n = self.name_to_string(name);
                let short = n.rsplit('.').next().unwrap_or(&n);
                format!("C({})", short)
            }
            Expr::App { fun, arg, fvar_lb, .. } => {
                format!("App({},{},lb={})", self.expr_desc(fun, max_depth - 1), self.expr_desc(arg, max_depth - 1), fvar_lb)
            }
            Expr::Pi { binder_type, body, fvar_lb, .. } => {
                format!("Pi({},{},lb={})", self.expr_desc(binder_type, max_depth - 1), self.expr_desc(body, max_depth - 1), fvar_lb)
            }
            Expr::Lambda { binder_type, body, fvar_lb, .. } => {
                format!("Lam({},{},lb={})", self.expr_desc(binder_type, max_depth - 1), self.expr_desc(body, max_depth - 1), fvar_lb)
            }
            Expr::Let { val, body, fvar_lb, .. } => {
                format!("Let({},{},lb={})", self.expr_desc(val, max_depth - 1), self.expr_desc(body, max_depth - 1), fvar_lb)
            }
            Expr::Proj { ty_name, idx, structure, .. } => {
                let n = self.name_to_string(ty_name);
                let short = n.rsplit('.').next().unwrap_or(&n);
                format!("Proj({}.{},{})", short, idx, self.expr_desc(structure, max_depth - 1))
            }
            Expr::Shift { inner, amount, .. } => {
                format!("Sh({},+{})", self.expr_desc(inner, max_depth - 1), amount)
            }
            Expr::Local { .. } => "Local".to_string(),
            Expr::NatLit { .. } => "Nat".to_string(),
            Expr::StringLit { .. } => "Str".to_string(),
        }
    }

    /// A constructor for the anonymous name.
    pub fn anonymous(&self) -> NamePtr<'t> { self.export_file.dag.anonymous() }

    pub fn str(&mut self, pfx: NamePtr<'t>, sfx: StringPtr<'t>) -> NamePtr<'t> {
        let hash = hash64!(crate::name::STR_HASH, pfx, sfx);
        self.alloc_name(Name::Str(pfx, sfx, hash))
    }

    pub fn str1_owned(&mut self, s: String) -> NamePtr<'t> {
        let anon = self.alloc_name(Name::Anon);
        let s = self.alloc_string(CowStr::Owned(s));
        self.str(anon, s)
    }

    pub fn str1(&mut self, s: &'static str) -> NamePtr<'t> {
        let anon = self.alloc_name(Name::Anon);
        let s = self.alloc_string(CowStr::Borrowed(s));
        self.str(anon, s)
    }

    pub fn str2(&mut self, s1: &'static str, s2: &'static str) -> NamePtr<'t> {
        let s1 = self.alloc_string(CowStr::Borrowed(s1));
        let s2 = self.alloc_string(CowStr::Borrowed(s2));
        let n = self.anonymous();
        let n = self.str(n, s1);
        self.str(n, s2)
    }

    pub fn zero(&self) -> LevelPtr<'t> { self.export_file.dag.zero() }

    pub fn num(&mut self, pfx: NamePtr<'t>, sfx: u64) -> NamePtr<'t> {
        let hash = hash64!(crate::name::NUM_HASH, pfx, sfx);
        self.alloc_name(Name::Num(pfx, sfx, hash))
    }

    pub fn succ(&mut self, l: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(crate::level::SUCC_HASH, l);
        self.alloc_level(Level::Succ(l, hash))
    }

    pub fn max(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(crate::level::MAX_HASH, l, r);
        self.alloc_level(Level::Max(l, r, hash))
    }
    pub fn imax(&mut self, l: LevelPtr<'t>, r: LevelPtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(crate::level::IMAX_HASH, l, r);
        self.alloc_level(Level::IMax(l, r, hash))
    }
    pub fn param(&mut self, n: NamePtr<'t>) -> LevelPtr<'t> {
        let hash = hash64!(crate::level::PARAM_HASH, n);
        self.alloc_level(Level::Param(n, hash))
    }

    pub fn mk_var(&mut self, dbj_idx: u16) -> ExprPtr<'t> {
        self.trace.alloc_mk_var += 1;
        let idx = dbj_idx as usize;
        if idx < self.expr_cache.mk_var_cache.len() {
            if let Some(cached) = self.expr_cache.mk_var_cache[idx] {
                return cached;
            }
        }
        let hash = hash64!(crate::expr::VAR_HASH, dbj_idx);
        let fvar_lb = dbj_idx;
        let result = self.alloc_expr(Expr::Var { dbj_idx, hash, fvar_lb });
        if idx >= self.expr_cache.mk_var_cache.len() {
            self.expr_cache.mk_var_cache.resize(idx + 1, None);
        }
        self.expr_cache.mk_var_cache[idx] = Some(result);
        result
    }

    pub fn mk_sort(&mut self, level: LevelPtr<'t>) -> ExprPtr<'t> {
        self.trace.alloc_mk_other += 1;
        let hash = hash64!(crate::expr::SORT_HASH, level);
        self.alloc_expr(Expr::Sort { level, hash, fvar_lb: 0 })
    }

    pub fn mk_const(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> ExprPtr<'t> {
        self.trace.alloc_mk_other += 1;
        let hash = hash64!(crate::expr::CONST_HASH, name, levels);
        self.alloc_expr(Expr::Const { name, levels, hash, fvar_lb: 0 })
    }

    /// OSNF helper: adjust a child expression by subtracting `amount` from its free variable
    /// lower bound. `cutoff` accounts for binders (0 for non-binder children, 1 for lambda/pi body).
    /// Precondition: child's effective fvar_lb >= amount (after accounting for cutoff).
    /// Only called when amount > 0.
    fn adjust_child_tc(&mut self, child: ExprPtr<'t>, amount: u16, cutoff: u16) -> ExprPtr<'t> {
        let child_expr = self.read_expr(child);
        let nlbv = child_expr.num_loose_bvars();
        if nlbv <= cutoff { return child; }
        match child_expr {
            Expr::Var { dbj_idx, .. } => {
                debug_assert!(dbj_idx >= amount, "adjust_child_tc: bvar {} < amount {}", dbj_idx, amount);
                self.mk_var(dbj_idx - amount)
            }
            Expr::Shift { inner, amount: child_amount, .. } => {
                debug_assert!(child_amount >= amount,
                    "adjust_child_tc: shift amount {} < adjustment {}", child_amount, amount);
                let new_amount = child_amount - amount;
                if new_amount == 0 {
                    inner
                } else {
                    self.mk_shift(inner, new_amount)
                }
            }
            _ => {
                let child_fvar_lb = child_expr.get_fvar_lb();
                if child_fvar_lb == 0 {
                    return child; // Already a core
                }
                // Non-OSNF compound with fvar_lb > 0: recursively OSNF-normalize first,
                // which produces Shift(child_fvar_lb, core). Then adjust the Shift.
                let osnf = self.to_osnf(child);
                self.adjust_child_tc(osnf, amount, cutoff)
            }
        }
    }

    /// Convert an expression to Outermost-Shift Normal Form (OSNF).
    /// If fvar_lb > 0, extracts the core (adjusting children) and wraps in Shift(fvar_lb, core).
    /// Handles non-OSNF children by recursively normalizing them first.
    /// Leaves bvar, Shift, Sort, Const, NatLit, StringLit, Local unchanged.
    pub fn to_osnf(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        let expr = self.read_expr(e);
        let fvar_lb = expr.get_fvar_lb();
        if fvar_lb == 0 || expr.num_loose_bvars() == 0 {
            return e;
        }
        // Only normalize compound expressions (not Var, Shift, or leaf types)
        match expr {
            Expr::Var { .. } | Expr::Shift { .. } | Expr::Sort { .. } | Expr::Const { .. }
            | Expr::NatLit { .. } | Expr::StringLit { .. } | Expr::Local { .. } => e,
            Expr::App { fun, arg, .. } => {
                let cf = self.adjust_child_tc(fun, fvar_lb, 0);
                let ca = self.adjust_child_tc(arg, fvar_lb, 0);
                let core = self.mk_app(cf, ca);
                self.mk_shift(core, fvar_lb)
            }
            Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let ct = self.adjust_child_tc(binder_type, fvar_lb, 0);
                let cb = self.adjust_child_tc(body, fvar_lb, 1);
                let core = self.mk_lambda(binder_name, binder_style, ct, cb);
                self.mk_shift(core, fvar_lb)
            }
            Expr::Pi { binder_name, binder_style, binder_type, body, .. } => {
                let ct = self.adjust_child_tc(binder_type, fvar_lb, 0);
                let cb = self.adjust_child_tc(body, fvar_lb, 1);
                let core = self.mk_pi(binder_name, binder_style, ct, cb);
                self.mk_shift(core, fvar_lb)
            }
            Expr::Let { binder_name, binder_type, val, body, nondep, .. } => {
                let ct = self.adjust_child_tc(binder_type, fvar_lb, 0);
                let cv = self.adjust_child_tc(val, fvar_lb, 0);
                let cb = self.adjust_child_tc(body, fvar_lb, 1);
                let core = self.mk_let(binder_name, ct, cv, cb, nondep);
                self.mk_shift(core, fvar_lb)
            }
            Expr::Proj { ty_name, idx, structure, .. } => {
                let cs = self.adjust_child_tc(structure, fvar_lb, 0);
                let core = self.mk_proj(ty_name, idx, cs);
                self.mk_shift(core, fvar_lb)
            }
        }
    }

    pub fn mk_app(&mut self, fun: ExprPtr<'t>, arg: ExprPtr<'t>) -> ExprPtr<'t> {
        // 2-way set-associative cache keyed by (fun, arg) — stores result directly.
        // Under OSNF, result may be Shift(App(cf, ca), fvar_lb), so we can't read the
        // result to recover fun/arg. Store them explicitly.
        let tag = fun.get_hash().wrapping_mul(0x9e3779b97f4a7c15) ^ arg.get_hash();
        let dm_len = self.expr_cache.mk_app_dm_cache.len();
        if dm_len > 0 {
            let set = (tag as usize) & ((dm_len >> 1) - 1);
            let slot0 = set << 1;
            let slot1 = slot0 | 1;
            let (tag0, cf0, ca0, result0) = self.expr_cache.mk_app_dm_cache[slot0];
            if tag0 == tag && cf0 == fun && ca0 == arg {
                self.trace.alloc_mk_app_cache_hit += 1;
                return result0;
            }
            let (tag1, cf1, ca1, result1) = self.expr_cache.mk_app_dm_cache[slot1];
            if tag1 == tag && cf1 == fun && ca1 == arg {
                self.trace.alloc_mk_app_cache_hit += 1;
                // Promote to slot0 (MRU)
                self.expr_cache.mk_app_dm_cache[slot0] = (tag1, cf1, ca1, result1);
                self.expr_cache.mk_app_dm_cache[slot1] = (tag0, cf0, ca0, result0);
                return result1;
            }
        }
        self.trace.alloc_mk_app += 1;
        let hash = hash64!(crate::expr::APP_HASH, fun, arg);
        let fun_e = self.read_expr(fun);
        let arg_e = self.read_expr(arg);
        let num_loose_bvars = fun_e.num_loose_bvars().max(arg_e.num_loose_bvars());
        let has_fvars = fun_e.has_fvars() || arg_e.has_fvars();
        let fvar_lb = if num_loose_bvars == 0 { 0 } else {
            let f_nlbv = fun_e.num_loose_bvars();
            let a_nlbv = arg_e.num_loose_bvars();
            if f_nlbv == 0 { arg_e.get_fvar_lb() }
            else if a_nlbv == 0 { fun_e.get_fvar_lb() }
            else { fun_e.get_fvar_lb().min(arg_e.get_fvar_lb()) }
        };
        // OSNF: if fvar_lb > 0, build core (fvar_lb=0) and wrap in Shift
        if fvar_lb > 0 {
            let cf = self.adjust_child_tc(fun, fvar_lb, 0);
            let ca = self.adjust_child_tc(arg, fvar_lb, 0);
            let core = self.mk_app(cf, ca);
            let result = self.mk_shift(core, fvar_lb);
            // Cache the OSNF result keyed by original (fun, arg)
            if dm_len > 0 {
                let set = (tag as usize) & ((dm_len >> 1) - 1);
                let slot0 = set << 1;
                self.expr_cache.mk_app_dm_cache[slot0 | 1] = self.expr_cache.mk_app_dm_cache[slot0];
                self.expr_cache.mk_app_dm_cache[slot0] = (tag, fun, arg, result);
            }
            return result;
        }
        let app_expr = Expr::App { fun, arg, num_loose_bvars, has_fvars, hash, fvar_lb };
        let result = self.alloc_expr(app_expr);
        // Lazily allocate DM cache after enough misses to justify the memory
        if dm_len == 0 {
            self.expr_cache.mk_app_miss_count += 1;
            if self.expr_cache.mk_app_miss_count >= MK_APP_DM_THRESHOLD {
                let dummy: ExprPtr<'t> = Ptr::from(DagMarker::ExportFile, 0);
                self.expr_cache.mk_app_dm_cache.resize(MK_APP_CACHE_SIZE, (0, dummy, dummy, dummy));
                let set = (tag as usize) & ((MK_APP_CACHE_SIZE >> 1) - 1);
                self.expr_cache.mk_app_dm_cache[set << 1] = (tag, fun, arg, result);
            }
        } else {
            let set = (tag as usize) & ((MK_APP_CACHE_SIZE >> 1) - 1);
            let slot0 = set << 1;
            // Evict slot1, move slot0 → slot1, put new in slot0
            self.expr_cache.mk_app_dm_cache[slot0 | 1] = self.expr_cache.mk_app_dm_cache[slot0];
            self.expr_cache.mk_app_dm_cache[slot0] = (tag, fun, arg, result);
        }
        result
    }

    pub fn mk_lambda(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let key = (binder_name, binder_style, binder_type, body);
        if let Some(&cached) = self.expr_cache.mk_lambda_cache.get(&key) {
            return cached;
        }
        self.trace.alloc_mk_lambda += 1;
        let hash = hash64!(crate::expr::LAMBDA_HASH, binder_name, binder_style, binder_type, body);
        let ty_e = self.read_expr(binder_type);
        let body_e = self.read_expr(body);
        let num_loose_bvars = ty_e.num_loose_bvars().max(body_e.num_loose_bvars().saturating_sub(1));
        let has_fvars = ty_e.has_fvars() || body_e.has_fvars();
        let fvar_lb = if num_loose_bvars == 0 { 0 } else {
            let t_nlbv = ty_e.num_loose_bvars();
            let b_nlbv = body_e.num_loose_bvars();
            let b_lb = body_e.get_fvar_lb().saturating_sub(1);
            if t_nlbv == 0 && b_nlbv <= 1 { 0 }
            else if t_nlbv == 0 { b_lb }
            else if b_nlbv <= 1 { ty_e.get_fvar_lb() }
            else { ty_e.get_fvar_lb().min(b_lb) }
        };
        // OSNF: if fvar_lb > 0, build core and wrap in Shift
        if fvar_lb > 0 {
            let ct = self.adjust_child_tc(binder_type, fvar_lb, 0);
            let cb = self.adjust_child_tc(body, fvar_lb, 1);
            let core = self.mk_lambda(binder_name, binder_style, ct, cb);
            let result = self.mk_shift(core, fvar_lb);
            self.expr_cache.mk_lambda_cache.insert(key, result);
            return result;
        }
        let lambda_expr = Expr::Lambda { binder_name, binder_style, binder_type, body, num_loose_bvars, has_fvars, hash, fvar_lb };
        let result = self.alloc_expr(lambda_expr);
        self.expr_cache.mk_lambda_cache.insert(key, result);
        result
    }

    pub fn mk_pi(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let key = (binder_name, binder_style, binder_type, body);
        if let Some(&cached) = self.expr_cache.mk_pi_cache.get(&key) {
            return cached;
        }
        self.trace.alloc_mk_pi += 1;
        let hash = hash64!(crate::expr::PI_HASH, binder_name, binder_style, binder_type, body);
        let ty_e = self.read_expr(binder_type);
        let body_e = self.read_expr(body);
        let num_loose_bvars = ty_e.num_loose_bvars().max(body_e.num_loose_bvars().saturating_sub(1));
        let has_fvars = ty_e.has_fvars() || body_e.has_fvars();
        let fvar_lb = if num_loose_bvars == 0 { 0 } else {
            let t_nlbv = ty_e.num_loose_bvars();
            let b_nlbv = body_e.num_loose_bvars();
            let b_lb = body_e.get_fvar_lb().saturating_sub(1);
            if t_nlbv == 0 && b_nlbv <= 1 { 0 }
            else if t_nlbv == 0 { b_lb }
            else if b_nlbv <= 1 { ty_e.get_fvar_lb() }
            else { ty_e.get_fvar_lb().min(b_lb) }
        };
        // OSNF: if fvar_lb > 0, build core and wrap in Shift
        if fvar_lb > 0 {
            let ct = self.adjust_child_tc(binder_type, fvar_lb, 0);
            let cb = self.adjust_child_tc(body, fvar_lb, 1);
            let core = self.mk_pi(binder_name, binder_style, ct, cb);
            let result = self.mk_shift(core, fvar_lb);
            self.expr_cache.mk_pi_cache.insert(key, result);
            return result;
        }
        let pi_expr = Expr::Pi { binder_name, binder_style, binder_type, body, num_loose_bvars, has_fvars, hash, fvar_lb };
        let result = self.alloc_expr(pi_expr);
        self.expr_cache.mk_pi_cache.insert(key, result);
        result
    }

    pub fn mk_let(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_type: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
        nondep: bool
    ) -> ExprPtr<'t> {
        self.trace.alloc_mk_let += 1;
        let hash = hash64!(crate::expr::LET_HASH, binder_name, binder_type, val, body, nondep);
        let ty_e = self.read_expr(binder_type);
        let val_e = self.read_expr(val);
        let body_e = self.read_expr(body);
        let ty_ub = ty_e.num_loose_bvars();
        let val_ub = val_e.num_loose_bvars();
        let body_ub = body_e.num_loose_bvars();
        let num_loose_bvars = ty_ub.max(val_ub.max(body_ub.saturating_sub(1)));
        let has_fvars = ty_e.has_fvars() || val_e.has_fvars() || body_e.has_fvars();
        let fvar_lb = if num_loose_bvars == 0 { 0 } else {
            let t_nlbv = ty_ub;
            let v_nlbv = val_ub;
            let b_nlbv = body_ub;
            let b_lb = body_e.get_fvar_lb().saturating_sub(1);
            let mut lb = u16::MAX;
            if t_nlbv > 0 { lb = lb.min(ty_e.get_fvar_lb()); }
            if v_nlbv > 0 { lb = lb.min(val_e.get_fvar_lb()); }
            if b_nlbv > 1 || (b_nlbv == 1 && body_e.get_fvar_lb() > 0) { lb = lb.min(b_lb); }
            if lb == u16::MAX { 0 } else { lb }
        };
        // OSNF: if fvar_lb > 0, build core and wrap in Shift
        if fvar_lb > 0 {
            let ct = self.adjust_child_tc(binder_type, fvar_lb, 0);
            let cv = self.adjust_child_tc(val, fvar_lb, 0);
            let cb = self.adjust_child_tc(body, fvar_lb, 1);
            let core = self.mk_let(binder_name, ct, cv, cb, nondep);
            return self.mk_shift(core, fvar_lb);
        }
        let let_expr = Expr::Let { binder_name, binder_type, val, body, num_loose_bvars, has_fvars, hash, nondep, fvar_lb };
        self.alloc_expr(let_expr)
    }

    pub fn mk_proj(&mut self, ty_name: NamePtr<'t>, idx: u32, structure: ExprPtr<'t>) -> ExprPtr<'t> {
        self.trace.alloc_mk_proj += 1;
        let hash = hash64!(crate::expr::PROJ_HASH, ty_name, idx, structure);
        let s_e = self.read_expr(structure);
        let num_loose_bvars = s_e.num_loose_bvars();
        let has_fvars = s_e.has_fvars();
        let fvar_lb = s_e.get_fvar_lb();
        // OSNF: if fvar_lb > 0, build core and wrap in Shift
        if fvar_lb > 0 {
            let cs = self.adjust_child_tc(structure, fvar_lb, 0);
            let core = self.mk_proj(ty_name, idx, cs);
            return self.mk_shift(core, fvar_lb);
        }
        let proj_expr = Expr::Proj { ty_name, idx, structure, num_loose_bvars, has_fvars, hash, fvar_lb };
        self.alloc_expr(proj_expr)
    }

    pub fn mk_string_lit(&mut self, string_ptr: StringPtr<'t>) -> Option<ExprPtr<'t>> {
        if !self.export_file.config.string_extension {
            return None
        }
        let hash = hash64!(crate::expr::STRING_LIT_HASH, string_ptr);
        Some(self.alloc_expr(Expr::StringLit { ptr: string_ptr, hash, fvar_lb: 0 }))
    }

    pub fn mk_string_lit_quick(&mut self, s: CowStr<'t>) -> Option<ExprPtr<'t>> {
        if !self.export_file.config.string_extension {
            return None
        }
        let string_ptr = self.alloc_string(s);
        self.mk_string_lit(string_ptr)
    }

    pub fn mk_nat_lit(&mut self, num_ptr: BigUintPtr<'t>) -> Option<ExprPtr<'t>> {
        if !self.export_file.config.nat_extension {
            return None
        }
        let hash = hash64!(crate::expr::NAT_LIT_HASH, num_ptr);
        Some(self.alloc_expr(Expr::NatLit { ptr: num_ptr, hash, fvar_lb: 0 }))
    }

    /// Shortcut to make an `Expr::NatLit` directly from a `BigUint`, rather than
    /// going `alloc_bignum` and `mk_nat_lit`
    pub fn mk_nat_lit_quick(&mut self, n: BigUint) -> Option<ExprPtr<'t>> {
        let num_ptr = self.alloc_bignum(n)?;
        self.mk_nat_lit(num_ptr)
    }

    /// Construct a free variable with a unique ID, incrementing the monotonic counter
    /// for unique free variable identifiers.
    pub fn mk_unique(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let unique_id = self.unique_counter;
        self.unique_counter += 1;
        let id = FVarId::Unique(unique_id);
        let hash = hash64!(crate::expr::LOCAL_HASH, binder_name, binder_style, binder_type, id);
        self.alloc_expr(Expr::Local { binder_name, binder_style, binder_type, id, hash, fvar_lb: 0 })
    }

    /// Construct a free variable representing a deBruijn level, incrementing the counter.
    /// Used by nanoda's locally-nameless TC approach.
    pub fn mk_dbj_level(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let level = self.dbj_level_counter;
        self.dbj_level_counter += 1;
        let id = FVarId::DbjLevel(level);
        let hash = hash64!(crate::expr::LOCAL_HASH, binder_name, binder_style, binder_type, id);
        self.alloc_expr(Expr::Local { binder_name, binder_style, binder_type, id, hash, fvar_lb: 0 })
    }

    /// Construct a free variable representing a deBruijn level, reusing a particular level
    /// counter, without incrementing the counter.
    pub fn remake_dbj_level(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        level: u16,
    ) -> ExprPtr<'t> {
        let id = FVarId::DbjLevel(level);
        let hash = hash64!(crate::expr::LOCAL_HASH, binder_name, binder_style, binder_type, id);
        self.alloc_expr(Expr::Local { binder_name, binder_style, binder_type, id, hash, fvar_lb: 0 })
    }

    /// Decrement the deBruijn level counter when closing a binder.
    pub(crate) fn replace_dbj_level(&mut self, e: ExprPtr<'t>) {
        match self.read_expr(e) {
            Expr::Local { id: FVarId::DbjLevel(level), .. } => {
                debug_assert_eq!(level + 1, self.dbj_level_counter);
                self.dbj_level_counter -= 1;
            }
            _ => panic!("replace_dbj_level didn't get a DbjLevel Local"),
        }
    }

    /// Convert a deBruijn level to a deBruijn index (bound variable).
    pub(crate) fn fvar_to_bvar(&mut self, num_open_binders: u16, dbj_level: u16) -> ExprPtr<'t> {
        self.mk_var((num_open_binders - dbj_level) - 1)
    }

    /// Create a delayed shift node: Shift(inner, amount) means all free Var indices
    /// in `inner` are shifted up by `amount`. O(1) — no traversal.
    /// OSNF invariant: inner.fvar_lb == 0, amount > 0. Collapses nested shifts.
    pub fn mk_shift(&mut self, inner: ExprPtr<'t>, amount: u16) -> ExprPtr<'t> {
        if amount == 0 {
            return inner;
        }
        let inner_expr = self.read_expr(inner);
        let nlbv = inner_expr.num_loose_bvars();
        if nlbv == 0 {
            return inner;
        }
        // Collapse nested shifts: Shift(Shift(e, j), k) -> Shift(e, j+k)
        if let Expr::Shift { inner: inner2, amount: prev, .. } = inner_expr {
            return self.mk_shift(inner2, prev + amount);
        }
        // Eagerly force Var (O(1))
        if let Expr::Var { dbj_idx, .. } = inner_expr {
            return self.mk_var(dbj_idx + amount);
        }
        // OSNF enforcement: if inner has fvar_lb > 0, it's not a proper core.
        // Extract core first, then shift core by fvar_lb + amount.
        let inner_lb = inner_expr.get_fvar_lb();
        if inner_lb > 0 {
            let core_inner = self.to_osnf(inner);
            // to_osnf returns Shift(inner_lb, core) or inner unchanged
            return self.mk_shift(core_inner, amount);
        }
        // Dedup: return existing Shift node if we've created this exact (inner, amount) before.
        let dedup_key = (inner, amount, 0u16);
        if let Some(&existing) = self.expr_cache.shift_dedup.get(&dedup_key) {
            self.trace.shift_dedup_hits += 1;
            return existing;
        }
        self.trace.alloc_mk_shift += 1;
        let has_fvars = inner_expr.has_fvars();
        let hash = hash64!(crate::expr::SHIFT_HASH, inner, amount, 0u16);
        let new_nlbv = nlbv + amount;
        let fvar_lb = amount; // inner.fvar_lb == 0, so Shift fvar_lb = amount
        let shift_expr = Expr::Shift { hash, fvar_lb, inner, amount, num_loose_bvars: new_nlbv, has_fvars };
        let result = self.alloc_expr(shift_expr);
        self.expr_cache.shift_dedup.insert(dedup_key, result);
        result
    }

    /// Push Shift(n, core) one level into core's constructor (cutoff=0).
    /// Under OSNF, view_expr(Shift(n, core)) calls this.
    /// Non-binder children: mk_shift(child, amount) — O(1).
    /// Binder bodies: shift_expr(body, amount, 1) — traversal, cached.
    pub fn push_shift_up(&mut self, e: ExprPtr<'t>, amount: u16) -> ExprPtr<'t> {
        self.trace.push_shift_calls += 1;
        if amount == 0 {
            return e;
        }
        let expr = self.read_expr(e);
        if expr.num_loose_bvars() == 0 {
            return e;
        }
        let cache_key = (e, amount, 0u16);
        if let Some(&result) = self.expr_cache.shift_cache.get(&cache_key) {
            self.trace.push_shift_cache_hits += 1;
            return result;
        }
        let result = stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.push_shift_up_inner(e, amount));
        self.expr_cache.shift_cache.insert(cache_key, result);
        result
    }

    fn push_shift_up_inner(&mut self, e: ExprPtr<'t>, amount: u16) -> ExprPtr<'t> {
        let expr = self.read_expr(e);
        if expr.num_loose_bvars() == 0 {
            return e;
        }
        match expr {
            Expr::Shift { inner, amount: prev, .. } => {
                // Collapse: Shift(Shift(inner, prev), amount) → push_shift_up(inner, prev+amount)
                self.push_shift_up(inner, prev + amount)
            }
            Expr::Var { dbj_idx, .. } => {
                self.mk_var(dbj_idx + amount)
            }
            Expr::App { fun, arg, has_fvars, .. } => {
                let fun = self.push_shift_up(fun, amount);
                let arg = self.mk_shift(arg, amount);
                let fun_e = self.read_expr(fun);
                let arg_e = self.read_expr(arg);
                let num_loose_bvars = fun_e.num_loose_bvars().max(arg_e.num_loose_bvars());
                let fvar_lb = if num_loose_bvars == 0 { 0 } else {
                    let f_nlbv = fun_e.num_loose_bvars();
                    let a_nlbv = arg_e.num_loose_bvars();
                    if f_nlbv == 0 { arg_e.get_fvar_lb() }
                    else if a_nlbv == 0 { fun_e.get_fvar_lb() }
                    else { fun_e.get_fvar_lb().min(arg_e.get_fvar_lb()) }
                };
                if fvar_lb > 0 {
                    // OSNF: extract core by adjusting children down, then Shift-wrap.
                    // Inlined from mk_app to avoid DM cache + recursive mk_app overhead.
                    let cf = self.adjust_child_tc(fun, fvar_lb, 0);
                    let ca = self.adjust_child_tc(arg, fvar_lb, 0);
                    let core_hash = hash64!(crate::expr::APP_HASH, cf, ca);
                    let core = self.alloc_expr(Expr::App {
                        fun: cf, arg: ca, num_loose_bvars: num_loose_bvars - fvar_lb,
                        has_fvars, hash: core_hash, fvar_lb: 0
                    });
                    self.mk_shift(core, fvar_lb)
                } else {
                    let hash = hash64!(crate::expr::APP_HASH, fun, arg);
                    self.alloc_expr(Expr::App { fun, arg, num_loose_bvars, has_fvars, hash, fvar_lb })
                }
            }
            Expr::Pi { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.mk_shift(binder_type, amount);
                let body = self.shift_expr(body, amount, 1);
                self.mk_pi(binder_name, binder_style, binder_type, body)
            }
            Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.mk_shift(binder_type, amount);
                let body = self.shift_expr(body, amount, 1);
                self.mk_lambda(binder_name, binder_style, binder_type, body)
            }
            Expr::Let { binder_name, binder_type, val, body, nondep, .. } => {
                let binder_type = self.mk_shift(binder_type, amount);
                let val = self.mk_shift(val, amount);
                let body = self.shift_expr(body, amount, 1);
                self.mk_let(binder_name, binder_type, val, body, nondep)
            }
            Expr::Proj { ty_name, idx, structure, has_fvars, .. } => {
                let structure = self.mk_shift(structure, amount);
                let s_e = self.read_expr(structure);
                let fvar_lb = s_e.get_fvar_lb();
                if fvar_lb > 0 {
                    let cs = self.adjust_child_tc(structure, fvar_lb, 0);
                    let core_hash = hash64!(crate::expr::PROJ_HASH, ty_name, idx, cs);
                    let core = self.alloc_expr(Expr::Proj {
                        ty_name, idx, structure: cs, num_loose_bvars: s_e.num_loose_bvars() - fvar_lb,
                        has_fvars, hash: core_hash, fvar_lb: 0
                    });
                    self.mk_shift(core, fvar_lb)
                } else {
                    let num_loose_bvars = s_e.num_loose_bvars();
                    let hash = hash64!(crate::expr::PROJ_HASH, ty_name, idx, structure);
                    self.alloc_expr(Expr::Proj { ty_name, idx, structure, num_loose_bvars, has_fvars, hash, fvar_lb })
                }
            }
            Expr::Sort { .. } | Expr::Const { .. } | Expr::Local { .. } | Expr::StringLit { .. } | Expr::NatLit { .. } => {
                panic!("push_shift_up on closed expression")
            }
        }
    }

    /// Shift DOWN: subtract `amount` from all free variable indices.
    /// Precondition: fvar_lb(e) >= amount (no variable goes negative).
    /// Only supports cutoff=0 — all free vars are shifted down.
    pub fn push_shift_down(&mut self, e: ExprPtr<'t>, amount: u16) -> ExprPtr<'t> {
        self.push_shift_down_cutoff(e, amount, 0)
    }

    /// Shift down free variable indices >= cutoff by `amount`. Cached persistently
    /// across inst_beta calls. Used by inst_aux to avoid re-traversing subtrees
    /// that only need shift_down (no substitution).
    pub fn push_shift_down_cutoff(&mut self, e: ExprPtr<'t>, amount: u16, cutoff: u16) -> ExprPtr<'t> {
        if amount == 0 {
            return e;
        }
        let expr = self.read_expr(e);
        if expr.num_loose_bvars() <= cutoff {
            return e;
        }
        // If all free bvars are >= cutoff, the cutoff is irrelevant — use O(1) cutoff=0 path.
        if cutoff > 0 && expr.get_fvar_lb() >= cutoff {
            return self.push_shift_down_cutoff(e, amount, 0);
        }
        let cache_key = (e, amount, cutoff);
        if let Some(&result) = self.expr_cache.shift_down_cache.get(&cache_key) {
            return result;
        }
        let result = stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.push_shift_down_inner(e, amount, cutoff));
        self.expr_cache.shift_down_cache.insert(cache_key, result);
        result
    }

    fn push_shift_down_inner(&mut self, e: ExprPtr<'t>, amount: u16, cutoff: u16) -> ExprPtr<'t> {
        let expr = self.read_expr(e);
        if expr.num_loose_bvars() <= cutoff {
            return e;
        }
        match expr {
            Expr::Shift { inner, amount: prev, .. } => {
                // OSNF: Shift always has cutoff=0.
                if cutoff == 0 {
                    // O(1): Shift(inner, prev) shift_down(amount, 0) = Shift(inner, prev - amount) or inner
                    debug_assert!(prev >= amount, "push_shift_down: Shift amount {} < shift_down {}", prev, amount);
                    if prev > amount {
                        self.mk_shift(inner, prev - amount)
                    } else {
                        inner
                    }
                } else {
                    // cutoff > 0: force the Shift, then shift down
                    let forced = self.push_shift_up(inner, prev);
                    self.push_shift_down_cutoff(forced, amount, cutoff)
                }
            }
            Expr::Var { dbj_idx, .. } => {
                if dbj_idx >= cutoff {
                    debug_assert!(dbj_idx >= amount, "push_shift_down: Var({}) - {} would go negative", dbj_idx, amount);
                    self.mk_var(dbj_idx - amount)
                } else {
                    e
                }
            }
            Expr::App { fun, arg, .. } => {
                let fun = self.push_shift_down_cutoff(fun, amount, cutoff);
                let arg = self.push_shift_down_cutoff(arg, amount, cutoff);
                self.mk_app(fun, arg)
            }
            Expr::Pi { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.push_shift_down_cutoff(binder_type, amount, cutoff);
                let body = self.push_shift_down_cutoff(body, amount, cutoff + 1);
                self.mk_pi(binder_name, binder_style, binder_type, body)
            }
            Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.push_shift_down_cutoff(binder_type, amount, cutoff);
                let body = self.push_shift_down_cutoff(body, amount, cutoff + 1);
                self.mk_lambda(binder_name, binder_style, binder_type, body)
            }
            Expr::Let { binder_name, binder_type, val, body, nondep, .. } => {
                let binder_type = self.push_shift_down_cutoff(binder_type, amount, cutoff);
                let val = self.push_shift_down_cutoff(val, amount, cutoff);
                let body = self.push_shift_down_cutoff(body, amount, cutoff + 1);
                self.mk_let(binder_name, binder_type, val, body, nondep)
            }
            Expr::Proj { ty_name, idx, structure, .. } => {
                let structure = self.push_shift_down_cutoff(structure, amount, cutoff);
                self.mk_proj(ty_name, idx, structure)
            }
            Expr::Sort { .. } | Expr::Const { .. } | Expr::Local { .. } | Expr::StringLit { .. } | Expr::NatLit { .. } => {
                e // closed, no shift needed
            }
        }
    }


    /// View an expression with Shift pushed one level inside.
    /// Never returns `Expr::Shift` — children may be Shift-wrapped.
    /// Under OSNF, we synthesize the Expr value directly with mk_shift-wrapped children,
    /// without allocating through mk_app/mk_pi/etc (which would re-OSNF-normalize).
    pub fn view_expr(&mut self, e: ExprPtr<'t>) -> Expr<'t> {
        let expr = self.read_expr(e);
        match expr {
            Expr::Shift { inner, amount, .. } => {
                self.view_expr_shifted(inner, amount)
            }
            other => other
        }
    }

    /// Synthesize an Expr view of `inner` shifted up by `amount` (cutoff=0).
    /// Returns the Expr struct directly — does NOT allocate through OSNF-enforcing mk_*.
    /// Children are Shift-wrapped via mk_shift (O(1)).
    /// Binder bodies use shift_expr(body, amount, 1) which traverses and rebuilds.
    fn view_expr_shifted(&mut self, inner: ExprPtr<'t>, amount: u16) -> Expr<'t> {
        let expr = self.read_expr(inner);
        match expr {
            Expr::Shift { inner: inner2, amount: prev, .. } => {
                // Nested shift: compose and retry
                self.view_expr_shifted(inner2, prev + amount)
            }
            Expr::Var { dbj_idx, .. } => {
                let new_idx = dbj_idx + amount;
                let hash = hash64!(crate::expr::VAR_HASH, new_idx);
                Expr::Var { dbj_idx: new_idx, hash, fvar_lb: new_idx }
            }
            Expr::App { fun, arg, has_fvars, .. } => {
                let fun = self.mk_shift(fun, amount);
                let arg = self.mk_shift(arg, amount);
                let fun_e = self.read_expr(fun);
                let arg_e = self.read_expr(arg);
                let num_loose_bvars = fun_e.num_loose_bvars().max(arg_e.num_loose_bvars());
                let hash = hash64!(crate::expr::APP_HASH, fun, arg);
                let fvar_lb = if num_loose_bvars == 0 { 0 } else {
                    let f_nlbv = fun_e.num_loose_bvars();
                    let a_nlbv = arg_e.num_loose_bvars();
                    if f_nlbv == 0 { arg_e.get_fvar_lb() }
                    else if a_nlbv == 0 { fun_e.get_fvar_lb() }
                    else { fun_e.get_fvar_lb().min(arg_e.get_fvar_lb()) }
                };
                Expr::App { fun, arg, num_loose_bvars, has_fvars, hash, fvar_lb }
            }
            Expr::Pi { binder_name, binder_style, binder_type, body, has_fvars, .. } => {
                let binder_type = self.mk_shift(binder_type, amount);
                let body = self.shift_expr(body, amount, 1);
                let ty_e = self.read_expr(binder_type);
                let body_e = self.read_expr(body);
                let num_loose_bvars = ty_e.num_loose_bvars().max(body_e.num_loose_bvars().saturating_sub(1));
                let hash = hash64!(crate::expr::PI_HASH, binder_name, binder_style, binder_type, body);
                let fvar_lb = if num_loose_bvars == 0 { 0 } else {
                    let t_nlbv = ty_e.num_loose_bvars();
                    let b_nlbv = body_e.num_loose_bvars();
                    let b_lb = body_e.get_fvar_lb().saturating_sub(1);
                    if t_nlbv == 0 && b_nlbv <= 1 { 0 }
                    else if t_nlbv == 0 { b_lb }
                    else if b_nlbv <= 1 { ty_e.get_fvar_lb() }
                    else { ty_e.get_fvar_lb().min(b_lb) }
                };
                Expr::Pi { binder_name, binder_style, binder_type, body, num_loose_bvars, has_fvars, hash, fvar_lb }
            }
            Expr::Lambda { binder_name, binder_style, binder_type, body, has_fvars, .. } => {
                let binder_type = self.mk_shift(binder_type, amount);
                let body = self.shift_expr(body, amount, 1);
                let ty_e = self.read_expr(binder_type);
                let body_e = self.read_expr(body);
                let num_loose_bvars = ty_e.num_loose_bvars().max(body_e.num_loose_bvars().saturating_sub(1));
                let hash = hash64!(crate::expr::LAMBDA_HASH, binder_name, binder_style, binder_type, body);
                let fvar_lb = if num_loose_bvars == 0 { 0 } else {
                    let t_nlbv = ty_e.num_loose_bvars();
                    let b_nlbv = body_e.num_loose_bvars();
                    let b_lb = body_e.get_fvar_lb().saturating_sub(1);
                    if t_nlbv == 0 && b_nlbv <= 1 { 0 }
                    else if t_nlbv == 0 { b_lb }
                    else if b_nlbv <= 1 { ty_e.get_fvar_lb() }
                    else { ty_e.get_fvar_lb().min(b_lb) }
                };
                Expr::Lambda { binder_name, binder_style, binder_type, body, num_loose_bvars, has_fvars, hash, fvar_lb }
            }
            Expr::Let { binder_name, binder_type, val, body, nondep, has_fvars, .. } => {
                let binder_type = self.mk_shift(binder_type, amount);
                let val = self.mk_shift(val, amount);
                let body = self.shift_expr(body, amount, 1);
                let ty_e = self.read_expr(binder_type);
                let val_e = self.read_expr(val);
                let body_e = self.read_expr(body);
                let ty_ub = ty_e.num_loose_bvars();
                let val_ub = val_e.num_loose_bvars();
                let body_ub = body_e.num_loose_bvars();
                let num_loose_bvars = ty_ub.max(val_ub.max(body_ub.saturating_sub(1)));
                let hash = hash64!(crate::expr::LET_HASH, binder_name, binder_type, val, body, nondep);
                let fvar_lb = if num_loose_bvars == 0 { 0 } else {
                    let mut lb = u16::MAX;
                    if ty_ub > 0 { lb = lb.min(ty_e.get_fvar_lb()); }
                    if val_ub > 0 { lb = lb.min(val_e.get_fvar_lb()); }
                    if body_ub > 1 || (body_ub == 1 && body_e.get_fvar_lb() > 0) { lb = lb.min(body_e.get_fvar_lb().saturating_sub(1)); }
                    if lb == u16::MAX { 0 } else { lb }
                };
                Expr::Let { binder_name, binder_type, val, body, num_loose_bvars, has_fvars, hash, nondep, fvar_lb }
            }
            Expr::Proj { ty_name, idx, structure, has_fvars, .. } => {
                let structure = self.mk_shift(structure, amount);
                let s_e = self.read_expr(structure);
                let num_loose_bvars = s_e.num_loose_bvars();
                let hash = hash64!(crate::expr::PROJ_HASH, ty_name, idx, structure);
                let fvar_lb = s_e.get_fvar_lb();
                Expr::Proj { ty_name, idx, structure, num_loose_bvars, has_fvars, hash, fvar_lb }
            }
            Expr::Sort { .. } | Expr::Const { .. } | Expr::Local { .. }
            | Expr::StringLit { .. } | Expr::NatLit { .. } => {
                expr // closed, shift is no-op
            }
        }
    }

    /// Peel off top-level Shift wrappers only (non-recursive).
    /// Ensures pattern matching on the expression head works.
    /// Check the heartbeat counter and panic if the deadline has passed.
    /// Called from hot paths (whnf, def_eq).
    #[inline]
    pub fn check_heartbeat(&mut self) {
        self.heartbeat += 1;
        if self.heartbeat % 10_000 == 0 {
            if let Some(deadline) = self.deadline {
                if std::time::Instant::now() > deadline {
                    eprintln!("  [timeout] heartbeat={} dag={} | {}", self.heartbeat, self.dag.exprs.len(), self.trace);
                    panic!("declaration timeout exceeded");
                }
            }
            if self.heartbeat % 100_000 == 0 {
                if let Some(deadline) = self.deadline {
                    let remaining = deadline.saturating_duration_since(std::time::Instant::now());
                    eprintln!("  [hb] {} rem={:.1}s dag={} | {}", self.heartbeat, remaining.as_secs_f32(), self.dag.exprs.len(), self.trace);
                }
            }
        }
    }

}

#[derive(Debug)]
pub struct LeanDag<'a> {
    pub names: UniqueIndexSet<Name<'a>>,
    pub levels: UniqueIndexSet<Level<'a>>,
    pub exprs: UniqueIndexSet<Expr<'a>>,
    /// Parallel array: expr_nlbv[i] = exprs[i].num_loose_bvars().
    /// Allows O(1) nlbv lookup without reading the full 48-byte Expr.
    pub expr_nlbv: Vec<u16>,
    /// Parallel array: expr_fvar_lb[i] = exprs[i].get_fvar_lb().
    /// Allows O(1) fvar_lb lookup for OSNF dead-substitution checks.
    pub expr_fvar_lb: Vec<u16>,
    pub uparams: FxIndexSet<Arc<[LevelPtr<'a>]>>,
    pub strings: FxIndexSet<CowStr<'a>>,
    pub bignums: Option<FxIndexSet<BigUint>>,
}

impl<'a> LeanDag<'a> {
    /// The export file format does not output the anonymous name and level zero, but the export
    /// program back-references them as though they were the 0th element of their kind; the exporter
    /// implicitly assumes that whatever you're using for storage knows about this convention.
    ///
    /// So when creating a new parser, we need to begin by placing `Anon` and `Zero` in the 0th position
    /// of their backing storage, satisfying the exporter's assumption.
    pub fn new(config: &Config) -> Self {
        Self::with_capacity(config, 0)
    }

    /// Clear all storage for reuse across declarations, preserving allocated capacity.
    pub fn clear_for_reuse(&mut self) {
        self.names.clear();
        self.levels.clear();
        self.exprs.clear();
        self.expr_nlbv.clear();
        self.expr_fvar_lb.clear();
        self.uparams.clear();
        self.strings.clear();
        if let Some(ref mut bignums) = self.bignums {
            bignums.clear();
        }
        // Re-insert sentinel values (Anon at index 0, Zero at index 0).
        let _ = self.names.insert(Name::Anon);
        let _ = self.levels.insert(Level::Zero);
    }

    pub fn with_capacity(config: &Config, expr_capacity: usize) -> Self {
        let mut out = Self {
            names: if expr_capacity > 0 {
                IndexSet::with_capacity_and_hasher(expr_capacity / 20, Default::default())
            } else {
                new_unique_index_set()
            },
            levels: new_unique_index_set(),
            exprs: if expr_capacity > 0 {
                IndexSet::with_capacity_and_hasher(expr_capacity, Default::default())
            } else {
                new_unique_index_set()
            },
            expr_nlbv: if expr_capacity > 0 {
                Vec::with_capacity(expr_capacity)
            } else {
                Vec::new()
            },
            expr_fvar_lb: if expr_capacity > 0 {
                Vec::with_capacity(expr_capacity)
            } else {
                Vec::new()
            },
            uparams: new_fx_index_set(),
            strings: new_fx_index_set(),
            bignums: if config.nat_extension { Some(new_fx_index_set()) } else { None },
        };

        let _ = out.names.insert(Name::Anon);
        let _ = out.levels.insert(Level::Zero);
        out
    }

    /// Used for constructing the name cache;
    pub(crate) fn anonymous(&self) -> NamePtr<'a> {
        debug_assert_eq!(self.names.get_index(0).copied().unwrap(), Name::Anon);
        Ptr::from(DagMarker::ExportFile, 0)
    }

    /// Used for constructing the name cache;
    pub(crate) fn zero(&self) -> LevelPtr<'a> {
        debug_assert_eq!(self.levels.get_index(0).copied().unwrap(), Level::Zero);
        Ptr::from(DagMarker::ExportFile, 0)
    }

    /// Used for constructing the name cache;
    fn get_string_ptr(&self, s: &str) -> Option<StringPtr<'a>> {
        self.strings.get_index_of(s).map(|idx| Ptr::from(DagMarker::ExportFile, idx))
    }

    // Find e.g. `Quot.lift` from "Quot.lift"
    fn find_name(&self, dot_separated_name: &str) -> Option<NamePtr<'a>> {
        let mut pfx = self.anonymous();
        for s in dot_separated_name.split('.') {
            if let Ok(num) = s.parse::<u64>() {
                let hash = hash64!(crate::name::NUM_HASH, pfx, num);
                if let Some(idx) = self.names.get_index_of(&Name::Num(pfx, num, hash)) {
                    pfx = Ptr::from(DagMarker::ExportFile, idx);
                    continue
                }
            } else if let Some(sfx) = self.get_string_ptr(s) {
                let hash = hash64!(crate::name::STR_HASH, pfx, sfx);
                if let Some(idx) = self.names.get_index_of(&Name::Str(pfx, sfx, hash)) {
                    pfx = Ptr::from(DagMarker::ExportFile, idx);
                    continue
                }
            }
            return None
        }
        Some(pfx)
    }

    /// If these names are present in the export file, we want to cache
    /// them since we need to retrieve them quite frequently.
    pub(crate) fn mk_name_cache(&self) -> NameCache<'a> {
        NameCache {
            eager_reduce: self.find_name("eagerReduce"),
            quot: self.find_name("Quot"),
            quot_mk: self.find_name("Quot.mk"),
            quot_lift: self.find_name("Quot.lift"),
            quot_ind: self.find_name("Quot.ind"),
            string: self.find_name("String"),
            string_of_list: self.find_name("String.ofList"),
            nat: self.find_name("Nat"),
            nat_zero: self.find_name("Nat.zero"),
            nat_succ: self.find_name("Nat.succ"),
            nat_add: self.find_name("Nat.add"),
            nat_sub: self.find_name("Nat.sub"),
            nat_mul: self.find_name("Nat.mul"),
            nat_pow: self.find_name("Nat.pow"),
            nat_mod: self.find_name("Nat.mod"),
            nat_div: self.find_name("Nat.div"),
            nat_beq: self.find_name("Nat.beq"),
            nat_ble: self.find_name("Nat.ble"),
            nat_gcd: self.find_name("Nat.gcd"),
            nat_xor: self.find_name("Nat.xor"),
            nat_land: self.find_name("Nat.land"),
            nat_lor: self.find_name("Nat.lor"),
            nat_shl: self.find_name("Nat.shiftLeft"),
            nat_shr: self.find_name("Nat.shiftRight"),
            bool_true: self.find_name("Bool.true"),
            bool_false: self.find_name("Bool.false"),
            char: self.find_name("Char"),
            char_of_nat: self.find_name("Char.ofNat"),
            list: self.find_name("List"),
            list_nil: self.find_name("List.nil"),
            list_cons: self.find_name("List.cons"),
        }
    }
}

/// This just caches common names; the values are `Some(x)` if the name
/// is present in the export file, otherwise they're `None`.
#[derive(Debug, Clone, Copy)]
pub struct NameCache<'p> {
    pub(crate) eager_reduce: Option<NamePtr<'p>>,
    pub(crate) quot: Option<NamePtr<'p>>,
    pub(crate) quot_mk: Option<NamePtr<'p>>,
    pub(crate) quot_lift: Option<NamePtr<'p>>,
    pub(crate) quot_ind: Option<NamePtr<'p>>,
    pub(crate) nat: Option<NamePtr<'p>>,
    pub(crate) nat_zero: Option<NamePtr<'p>>,
    pub(crate) nat_succ: Option<NamePtr<'p>>,
    pub(crate) nat_add: Option<NamePtr<'p>>,
    pub(crate) nat_sub: Option<NamePtr<'p>>,
    pub(crate) nat_mul: Option<NamePtr<'p>>,
    pub(crate) nat_pow: Option<NamePtr<'p>>,
    pub(crate) nat_mod: Option<NamePtr<'p>>,
    pub(crate) nat_div: Option<NamePtr<'p>>,
    pub(crate) nat_beq: Option<NamePtr<'p>>,
    pub(crate) nat_ble: Option<NamePtr<'p>>,
    pub(crate) nat_gcd: Option<NamePtr<'p>>,
    pub(crate) nat_xor: Option<NamePtr<'p>>,
    pub(crate) nat_land: Option<NamePtr<'p>>,
    pub(crate) nat_lor: Option<NamePtr<'p>>,
    pub(crate) nat_shr: Option<NamePtr<'p>>,
    pub(crate) nat_shl: Option<NamePtr<'p>>,
    pub(crate) string: Option<NamePtr<'p>>,
    pub(crate) string_of_list: Option<NamePtr<'p>>,
    pub(crate) bool_false: Option<NamePtr<'p>>,
    pub(crate) bool_true: Option<NamePtr<'p>>,
    pub(crate) char: Option<NamePtr<'p>>,
    pub(crate) char_of_nat: Option<NamePtr<'p>>,
    #[allow(dead_code)]
    pub(crate) list: Option<NamePtr<'p>>,
    pub(crate) list_nil: Option<NamePtr<'p>>,
    pub(crate) list_cons: Option<NamePtr<'p>>,
}

pub(crate) struct TcCache<'t> {
    // === Base buckets (bucket 0): closed expressions, never evicted ===
    /// WHNF cache for closed expressions: ExprPtr → result.
    pub(crate) whnf_cache_base: FxHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    /// whnf_no_unfolding cache for closed expressions.
    pub(crate) wnu_cache_base: FxHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    /// Infer cache (check mode) for closed expressions: ExprPtr → result.
    pub(crate) infer_cache_check_base: FxHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    /// Infer cache (no-check mode) for closed expressions: ExprPtr → result.
    pub(crate) infer_cache_no_check_base: FxHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    // === Flat caches (not depth-stacked) ===
    /// Positive def_eq cache for closed expressions (pointer-keyed set).
    pub(crate) eq_cache: FxHashSet<(ExprPtr<'t>, ExprPtr<'t>)>,
    /// Negative def_eq cache for closed expressions (pointer-keyed set).
    pub(crate) failure_cache: FxHashSet<(ExprPtr<'t>, ExprPtr<'t>)>,
    /// Strong reduction cache (library/inspection feature).
    pub(crate) strong_cache: UniqueHashMap<(ExprPtr<'t>, bool, bool), ExprPtr<'t>>,
    /// Pointer-based UnionFind for transitive def_eq caching.
    pub(crate) eq_cache_uf: UnionFind<ExprPtr<'t>>,
    // === Per-depth frames: local context + open-expression caches ===
    /// Stack of depth frames. Frame at index i corresponds to binder depth i+1.
    /// For caches with a base bucket (whnf, infer): bucket_idx k > 0 maps to frame[k-1].
    /// For caches without base bucket (defeq): bucket_idx k maps to frame[k].
    pub(crate) frames: Vec<DepthFrame<'t>>,
}

impl<'t> TcCache<'t> {
    pub(crate) fn new() -> Self {
        Self {
            whnf_cache_base: new_fx_hash_map(),
            wnu_cache_base: new_fx_hash_map(),
            infer_cache_check_base: new_fx_hash_map(),
            infer_cache_no_check_base: new_fx_hash_map(),
            eq_cache: new_fx_hash_set(),
            failure_cache: new_fx_hash_set(),
            strong_cache: new_unique_hash_map(),
            eq_cache_uf: UnionFind::new(),
            frames: Vec::new(),
        }
    }

    pub(crate) fn clear(&mut self) {
        self.whnf_cache_base.clear();
        self.wnu_cache_base.clear();
        self.infer_cache_check_base.clear();
        self.infer_cache_no_check_base.clear();
        self.eq_cache.clear();
        self.failure_cache.clear();
        self.strong_cache.clear();
        self.eq_cache_uf.clear();
        self.frames.clear();
    }

    /// Current binding depth (number of binders entered).
    pub(crate) fn depth(&self) -> usize { self.frames.len() }

    /// Push a lambda/pi binder.
    pub(crate) fn push_local(&mut self, ty: ExprPtr<'t>) {
        self.frames.push(DepthFrame::new(ty, None));
    }

    /// Push a let-binding.
    pub(crate) fn push_local_let(&mut self, ty: ExprPtr<'t>, val: ExprPtr<'t>) {
        self.frames.push(DepthFrame::new(ty, Some(val)));
    }

    /// Pop the most recent binder.
    pub(crate) fn pop_local(&mut self) {
        self.frames.pop().expect("pop_local: empty context");
    }

    /// Restore to a previous depth, discarding deeper frames.
    pub(crate) fn restore_depth(&mut self, depth: usize) {
        self.frames.truncate(depth);
    }

    /// Temporarily split off frames above `new_depth`, returning them.
    pub(crate) fn split_off(&mut self, new_depth: usize) -> Vec<DepthFrame<'t>> {
        self.frames.split_off(new_depth)
    }

    /// Restore previously split-off frames.
    pub(crate) fn extend(&mut self, saved: Vec<DepthFrame<'t>>) {
        self.frames.extend(saved);
    }

    /// Look up a local binding by de Bruijn index (0 = most recent).
    pub(crate) fn local_type(&self, dbj_idx: u16) -> ExprPtr<'t> {
        let depth = self.frames.len();
        assert!(dbj_idx < depth as u16, "local_type: dbj_idx={} >= depth={} (free var reached type lookup)", dbj_idx, depth);
        self.frames[depth - 1 - dbj_idx as usize].local.0
    }

    /// Look up the value of a let-bound variable by de Bruijn index.
    pub(crate) fn local_value(&self, dbj_idx: u16) -> Option<ExprPtr<'t>> {
        let depth = self.frames.len();
        if dbj_idx >= depth as u16 {
            return None; // Free variable — not in local context
        }
        self.frames[depth - 1 - dbj_idx as usize].local.1
    }

    // === Pointer-based cache accessors (nanoda approach) ===
    // Hash-consing guarantees: same expression = same pointer = same cache key.
    // For whnf/infer/wnu caches: bucket 0 = base, bucket k>0 = frames[k-1].
    // For defeq caches: bucket k = frames[k] (no base bucket).

    pub(crate) fn whnf_cache_get(&self, bucket_idx: usize, key: &ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if bucket_idx == 0 { self.whnf_cache_base.get(key).copied() }
        else { self.frames.get(bucket_idx - 1)?.whnf_cache.get(key).copied() }
    }

    pub(crate) fn whnf_cache_insert(&mut self, bucket_idx: usize, key: ExprPtr<'t>, val: ExprPtr<'t>) {
        if bucket_idx == 0 { self.whnf_cache_base.insert(key, val); }
        else if let Some(f) = self.frames.get_mut(bucket_idx - 1) { f.whnf_cache.insert(key, val); }
    }

    pub(crate) fn wnu_cache_get(&self, bucket_idx: usize, key: &ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if bucket_idx == 0 { self.wnu_cache_base.get(key).copied() }
        else { self.frames.get(bucket_idx - 1)?.whnf_no_unfolding_cache.get(key).copied() }
    }

    pub(crate) fn wnu_cache_insert(&mut self, bucket_idx: usize, key: ExprPtr<'t>, val: ExprPtr<'t>) {
        if bucket_idx == 0 { self.wnu_cache_base.insert(key, val); }
        else if let Some(f) = self.frames.get_mut(bucket_idx - 1) { f.whnf_no_unfolding_cache.insert(key, val); }
    }

    pub(crate) fn infer_cache_get(&self, bucket_idx: usize, key: &ExprPtr<'t>, is_check: bool) -> Option<ExprPtr<'t>> {
        if bucket_idx == 0 {
            if is_check { self.infer_cache_check_base.get(key).copied() }
            else { self.infer_cache_no_check_base.get(key).copied() }
        } else {
            let f = self.frames.get(bucket_idx - 1)?;
            if is_check { f.infer_cache_check.get(key).copied() }
            else { f.infer_cache_no_check.get(key).copied() }
        }
    }

    pub(crate) fn infer_cache_insert(&mut self, bucket_idx: usize, key: ExprPtr<'t>, val: ExprPtr<'t>, is_check: bool) {
        if bucket_idx == 0 {
            if is_check { self.infer_cache_check_base.insert(key, val); }
            else { self.infer_cache_no_check_base.insert(key, val); }
        } else if let Some(f) = self.frames.get_mut(bucket_idx - 1) {
            if is_check { f.infer_cache_check.insert(key, val); }
            else { f.infer_cache_no_check.insert(key, val); }
        }
    }

    pub(crate) fn defeq_open_get(&self, is_pos: bool, bucket_idx: usize, key: &(ExprPtr<'t>, ExprPtr<'t>)) -> Option<&(ExprPtr<'t>, ExprPtr<'t>, u16)> {
        let frame = self.frames.get(bucket_idx)?;
        if is_pos { frame.defeq_pos_open.get(key) } else { frame.defeq_neg_open.get(key) }
    }

    pub(crate) fn defeq_open_insert(&mut self, is_pos: bool, bucket_idx: usize, key: (ExprPtr<'t>, ExprPtr<'t>), val: (ExprPtr<'t>, ExprPtr<'t>, u16)) {
        if let Some(frame) = self.frames.get_mut(bucket_idx) {
            if is_pos { frame.defeq_pos_open.insert(key, val); }
            else { frame.defeq_neg_open.insert(key, val); }
        }
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct Config {
    /// The path to the export file to be checked (if `none`, users must specify `use_stdin: true`)
    pub export_file_path: Option<PathBuf>,

    /// A value indicating whether the type checker should look to stdin to receive the export file.
    #[serde(default)]
    pub use_stdin: bool,

    /// A list of the whitelisted axioms the user wants to allow.
    pub permitted_axioms: Option<Vec<String>>,

    /// A boolean indicating what behavior the typechecker should exhibit when encountering
    /// an axiom in an export file which has not explicitly been named in `permitted_axioms`.
    /// if `unpermitted_axiom_hard_error: true`, the typechecker will fail with a hard error.
    /// if `unpermitted_axiom_hard_error: false`, the typechecker will NOT add the axiom to the environment,
    /// and will continue typechecking in an environment that does not contain the disallowed axiom.
    #[serde(default = "default_true")]
    pub unpermitted_axiom_hard_error: bool,

    /// Number of threads to use for type checking.
    #[serde(default)]
    pub num_threads: usize,

    #[serde(default)] 
    pub nat_extension: bool,
    #[serde(default)] 
    pub string_extension: bool,

    /// A list of declaration names the user wants to be pretty-printed back to them on termination.
    pub pp_declars: Option<Vec<String>>,

    /// Indicates what the typechecker should do when it's been asked to pretty-print a declaration
    /// that is not actually in the environment. We give this option because that scenario is 
    /// strongly indicative of a mismatch between what the user thinks is in the export file and
    /// what is actually in the export file.
    /// If `true`, the typechecker will fail with a hard error. 
    /// If `false`, the typechecker will not fail just because of this.
    #[serde(default = "default_true")]
    pub unknown_pp_declar_hard_error: bool,

    #[serde(default)]
    pub pp_options: PpOptions,

    /// Optionally, a path to write the pretty-printer output to.
    pub pp_output_path: Option<PathBuf>,

    #[serde(default)]
    pub pp_to_stdout: bool,

    #[serde(default)]
    pub print_success_message: bool,

    /// If `true`, the typechecker will print the axioms actually admitted to the environment
    /// when typechecking is finished. 
    #[serde(default = "default_true")]
    pub print_axioms: bool,

    /// If set to `true`, will allow all axioms to be admitted to the environment.
    #[serde(default)]
    pub unsafe_permit_all_axioms: bool,

    /// Maximum number of declarations to check (0 = unlimited). For debugging.
    #[serde(default)]
    pub max_declarations: usize,

    /// Number of declarations to skip at the start. For debugging.
    #[serde(default)]
    pub skip_declarations: usize,

    /// Per-declaration timeout in seconds (0 = unlimited). Declarations exceeding
    /// this timeout are skipped with a warning.
    #[serde(default)]
    pub declaration_timeout_secs: u64,

    /// Use nanoda's original locally-nameless type checker instead of the shift-based one.
    #[serde(default)]
    pub use_nanoda_tc: bool,
}

impl TryFrom<&Path> for Config {
    type Error = Box<dyn Error>;
    fn try_from(p: &Path) -> Result<Config, Self::Error> {
        match OpenOptions::new().read(true).truncate(false).open(p) {
            Err(e) => Err(Box::from(format!("failed to open configuration file: {:?}", e))),
            Ok(config_file) => {
                let config = serde_json::from_reader::<_, Config>(BufReader::new(config_file)).unwrap();
                if config.export_file_path.is_none() && !config.use_stdin {
                    return Err(Box::from(format!("incompatible config options: must specify a path to an export file OR set `use_stdin: true`")))
                }
                if config.export_file_path.is_some() && config.use_stdin {
                    return Err(Box::from(format!("incompatible config options: if an export file path is given, `use_stdin` cannot be `true`")))
                }
                if config.unsafe_permit_all_axioms {
                    if config.unpermitted_axiom_hard_error {
                        return Err(Box::from(format!("incompatible config options: unsafe_permit_all_axioms && unpermitted_axioms_hard_error")))
                    }
                    if config.permitted_axioms.is_some() {
                        return Err(Box::from(format!("incompatible config options: unsafe_permit_all_axioms && nonempty permitted_axioms list")))
                    }
                }
                Ok(config)
            }
        }
    }
}

pub enum PpDestination {
    File(BufWriter<std::fs::File>),
    Stdout(BufWriter<std::io::Stdout>),
}

impl PpDestination {
    pub(crate) fn stdout() -> Self { Self::Stdout(BufWriter::new(std::io::stdout())) }
    pub(crate) fn write_line(&mut self, s: String, sep: &str) -> Result<usize, Box<dyn Error>> {
        match self {
            PpDestination::File(f) => f.write(s.as_bytes()).and_then(|_| f.write(sep.as_bytes())).map_err(Box::from),
            PpDestination::Stdout(f) => f.write(s.as_bytes()).and_then(|_| f.write(sep.as_bytes())).map_err(Box::from),
        }
    }
}

impl Config {
    pub fn get_pp_destination(&self) -> Result<Option<PpDestination>, Box<dyn Error>> {
        if let Some(pathbuf) = self.pp_output_path.as_ref() {
            match OpenOptions::new().write(true).truncate(false).open(pathbuf) {
                Ok(file) => Ok(Some(PpDestination::File(BufWriter::new(file)))),
                Err(e) => Err(Box::from(format!("Failed to open pretty printer destination file: {:?}", e))),
            }
        } else if self.pp_to_stdout {
            Ok(Some(PpDestination::stdout()))
        } else {
            Ok(None)
        }
    }

    // Returns the export file, and a list of strings representing the names of "skipped" axioms
    // (axioms which were in the export file, but not allowed by the execution config).
    pub fn to_export_file<'a>(self) -> Result<(ExportFile<'a>, Vec<String>), Box<dyn Error>> {
        if let Some(pathbuf) = self.export_file_path.as_ref() {
            match OpenOptions::new().read(true).truncate(false).open(pathbuf) {
                Ok(file) => {
                    // Estimate expression count from file size to pre-allocate DAG.
                    // Average line is ~55 bytes, ~95% of lines are expressions.
                    let estimated_exprs = file.metadata()
                        .map(|m| (m.len() / 58) as usize)
                        .unwrap_or(0);
                    crate::parser::parse_export_file(BufReader::new(file), self, estimated_exprs)
                }
                Err(e) => Err(Box::from(format!("Failed to open export file: {:?}", e))),
            }
        } else if self.use_stdin {
            let reader = BufReader::new(std::io::stdin());
            crate::parser::parse_export_file(reader, self, 0)
        } else {
            panic!("Configuration file must specify en export file path or \"use_stdin\": true")
        }
    }
}

// The intent is to use this for reporting exit status/error info
// when we go back and get rid of all of the `panic!` invocations
// and use more involved error handling.
#[allow(dead_code)]
#[derive(Debug, Clone)]
struct ExitStatus {
    tc_err: Option<String>,
    pp_err: Option<String>
}

