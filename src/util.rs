use crate::env::{DeclarMap, Env, NotationMap, EnvLimit};
use crate::expr::{BinderStyle, Expr, FVarId, FVarList, FVarListPtr, FVarNode, FVAR_HASH};
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(packed)]
pub struct Ptr<A> {
    /// The index in the appropriate dag at which this element sits.
    pub(crate) idx: u32,
    /// The dag this pointer points to; the persistent dag in the export file,
    /// or the temporary dag in the type checker context.
    pub(crate) dag_marker: DagMarker,
    pub(crate) ph: PhantomData<A>,
}

const HIGH_MASK: u64 = 1 << 63;

impl<A> Ptr<A> {
    pub(crate) fn from(dag_marker: DagMarker, idx: usize) -> Self {
        Self { idx: u32::try_from(idx).unwrap(), dag_marker, ph: PhantomData }
    }

    pub(crate) fn idx(&self) -> usize { self.idx as usize }

    pub(crate) fn dag_marker(&self) -> DagMarker { self.dag_marker }

    pub(crate) fn get_hash(&self) -> u64 {
        if self.dag_marker == DagMarker::ExportFile {
            self.idx as u64
        } else {
            HIGH_MASK | (self.idx as u64)
        }
    }
}

impl<A> std::hash::Hash for Ptr<A> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
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

pub(crate) fn new_fx_index_map<K, V>() -> FxIndexMap<K, V> { FxIndexMap::with_hasher(Default::default()) }

pub(crate) fn new_fx_hash_map<K, V>() -> FxHashMap<K, V> { FxHashMap::with_hasher(Default::default()) }

pub(crate) fn new_fx_hash_set<K>() -> FxHashSet<K> { FxHashSet::with_hasher(Default::default()) }

pub(crate) fn new_fx_index_set<K>() -> FxIndexSet<K> { FxIndexSet::with_hasher(Default::default()) }
pub(crate) fn new_unique_index_set<K>() -> UniqueIndexSet<K> { UniqueIndexSet::with_hasher(Default::default()) }

pub(crate) fn new_unique_hash_map<K, V>() -> UniqueHashMap<K, V> { UniqueHashMap::with_hasher(Default::default()) }

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
    /// Caches (e, offset) |-> output for instantiation. This cache is reset
    /// before every new call to `inst`, so there's no need to cache the sequence
    /// of substitutions.
    pub(crate) inst_cache: FxHashMap<(ExprPtr<'t>, u16), ExprPtr<'t>>,
    /// Caches (e, ks, vs) |-> output for level substitution.
    pub(crate) subst_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), ExprPtr<'t>>,
    pub(crate) dsubst_cache: FxHashMap<(ExprPtr<'t>, LevelsPtr<'t>, LevelsPtr<'t>), ExprPtr<'t>>,
    /// Caches (e, offset) |-> output for abstraction (re-binding free variables).
    /// This cache is reset before every new call to `inst`, so there's no need to
    /// cache the sequence of free variables.
    pub(crate) abstr_cache: FxHashMap<(ExprPtr<'t>, u16), ExprPtr<'t>>,
    /// Caches (e, amount, cutoff) |-> output for shifting.
    pub(crate) shift_cache: FxHashMap<(ExprPtr<'t>, u16, u16), ExprPtr<'t>>,
}

impl<'t> ExprCache<'t> {
    fn new() -> Self {
        Self {
            inst_cache: new_fx_hash_map(),
            abstr_cache: new_fx_hash_map(),
            subst_cache: new_fx_hash_map(),
            dsubst_cache: new_fx_hash_map(),
            shift_cache: new_fx_hash_map(),
        }
    }
}

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
    pub mutual_block_sizes: FxHashMap<NamePtr<'p>, (usize, usize)>
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

    pub fn with_tc_and_declar<F, A>(&self, d: crate::env::DeclarInfo<'p>, f: F) -> A
    where
        F: FnOnce(&mut TypeChecker<'_, '_, 'p>) -> A, {
        let mut dag = LeanDag::new(&self.config);
        let mut ctx = TcCtx::new(self, &mut dag);
        let env = self.new_env(EnvLimit::ByName(d.name));
        let mut tc = TypeChecker::new(&mut ctx, &env, Some(d));
        f(&mut tc)
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
    /// Monotonically increasing counter for unique free variables. Any two free variables created
    /// with the `mk_unique` constructor are unique within their `(ExportFile, TcCtx)` pair.
    pub(crate) unique_counter: u32,
    /// A cache for instantiation, free variable abstraction, and level substitution
    pub(crate) expr_cache: ExprCache<'t>,
    pub(crate) eager_mode: bool
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    pub fn new(export_file: &'t ExportFile<'p>, tdag: &'t mut LeanDag<'t>) -> Self {
        Self {
            export_file,
            dag: tdag,
            unique_counter: 0u32,
            expr_cache: ExprCache::new(),
            eager_mode: false
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
        if let Some(idx) = self.export_file.dag.exprs.get_index_of(&e) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else {
            Ptr::from(DagMarker::TcCtx, self.dag.exprs.insert_full(e).0)
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

    // --- FVarList operations ---

    pub(crate) fn read_fvar_node(&self, ptr: FVarListPtr<'t>) -> FVarNode<'t> {
        match ptr.dag_marker() {
            DagMarker::ExportFile => *self.export_file.dag.fvarlists.get_index(ptr.idx()).unwrap(),
            DagMarker::TcCtx => *self.dag.fvarlists.get_index(ptr.idx()).unwrap(),
        }
    }

    pub(crate) fn alloc_fvar_node(&mut self, delta: u16, tail: FVarList<'t>) -> FVarListPtr<'t> {
        let tail_hash = tail.map(|t| self.read_fvar_node(t).get_hash()).unwrap_or(0);
        let hash = hash64!(FVAR_HASH, delta as u64, tail_hash);
        let node = FVarNode { hash, delta, tail };
        if let Some(idx) = self.export_file.dag.fvarlists.get_index_of(&node) {
            Ptr::from(DagMarker::ExportFile, idx)
        } else {
            Ptr::from(DagMarker::TcCtx, self.dag.fvarlists.insert_full(node).0)
        }
    }

    /// Singleton fvar list for bvar(i)
    pub(crate) fn fvar_singleton(&mut self, idx: u16) -> FVarList<'t> {
        Some(self.alloc_fvar_node(idx, None))
    }

    /// Shift: increment head delta by k. O(1).
    pub(crate) fn fvar_shift(&mut self, fvl: FVarList<'t>, k: u16) -> FVarList<'t> {
        match fvl {
            None => None,
            Some(ptr) => {
                let node = self.read_fvar_node(ptr);
                Some(self.alloc_fvar_node(node.delta + k, node.tail))
            }
        }
    }

    /// Shift free var indices >= cutoff by k in the FVarList.
    /// Walk the delta-encoded list to find the first entry >= cutoff,
    /// add k to its delta, share the tail. O(position of cutoff in list).
    pub(crate) fn fvar_shift_cutoff(&mut self, fvl: FVarList<'t>, k: u16, cutoff: u16) -> FVarList<'t> {
        if cutoff == 0 {
            return self.fvar_shift(fvl, k);
        }
        self.fvar_shift_cutoff_aux(fvl, k, cutoff, 0)
    }

    fn fvar_shift_cutoff_aux(&mut self, fvl: FVarList<'t>, k: u16, cutoff: u16, abs_pos: u16) -> FVarList<'t> {
        match fvl {
            None => None,
            Some(ptr) => {
                let node = self.read_fvar_node(ptr);
                // Current absolute index: first element has abs = delta, subsequent have abs = prev_abs + 1 + delta
                let cur_abs = abs_pos + node.delta;
                if cur_abs >= cutoff {
                    // This entry and all after get shifted by k
                    Some(self.alloc_fvar_node(node.delta + k, node.tail))
                } else {
                    // This entry stays, recurse on tail
                    let new_tail = self.fvar_shift_cutoff_aux(node.tail, k, cutoff, cur_abs + 1);
                    Some(self.alloc_fvar_node(node.delta, new_tail))
                }
            }
        }
    }

    /// Unbind: remove bvar(0), decrement others. O(1).
    pub(crate) fn fvar_unbind(&mut self, fvl: FVarList<'t>) -> FVarList<'t> {
        match fvl {
            None => None,
            Some(ptr) => {
                let node = self.read_fvar_node(ptr);
                if node.delta == 0 {
                    node.tail  // pop: bound var was free
                } else {
                    Some(self.alloc_fvar_node(node.delta - 1, node.tail))
                }
            }
        }
    }

    /// Union: merge two delta-encoded sorted sets.
    pub(crate) fn fvar_union(&mut self, a: FVarList<'t>, b: FVarList<'t>) -> FVarList<'t> {
        match (a, b) {
            (None, _) => b,
            (_, None) => a,
            (Some(ap), Some(bp)) => {
                if ap == bp { return a; }  // ptr-eq shortcut
                let an = self.read_fvar_node(ap);
                let bn = self.read_fvar_node(bp);
                self.fvar_merge(an.delta, an.tail, bn.delta, bn.tail)
            }
        }
    }

    /// Core merge: two "virtual" heads (a_d, a_tail) and (b_d, b_tail).
    /// Both deltas are relative to the same base.
    fn fvar_merge(&mut self, a_d: u16, a_tail: FVarList<'t>, b_d: u16, b_tail: FVarList<'t>) -> FVarList<'t> {
        if a_d < b_d {
            // Emit a_d. b's head relative to (a_d+1): b_d - a_d - 1.
            // a's tail is already relative to (a_d+1).
            let rest = self.fvar_merge_into(a_tail, b_d - a_d - 1, b_tail);
            Some(self.alloc_fvar_node(a_d, rest))
        } else if a_d == b_d {
            // Same element. Merge tails (both relative to a_d+1). ptr-eq works here.
            let rest = self.fvar_union(a_tail, b_tail);
            Some(self.alloc_fvar_node(a_d, rest))
        } else {
            // Emit b_d. Symmetric.
            let rest = self.fvar_merge_into(b_tail, a_d - b_d - 1, a_tail);
            Some(self.alloc_fvar_node(b_d, rest))
        }
    }

    /// Merge a FVarList with a virtual head (vd, vtail). vd is relative to the list's base.
    fn fvar_merge_into(&mut self, list: FVarList<'t>, vd: u16, vtail: FVarList<'t>) -> FVarList<'t> {
        match list {
            None => Some(self.alloc_fvar_node(vd, vtail)),
            Some(lp) => {
                let ln = self.read_fvar_node(lp);
                self.fvar_merge(ln.delta, ln.tail, vd, vtail)
            }
        }
    }

    /// Hash of the normalized fvar_list (shift-invariant). For canonical cache keys.
    pub(crate) fn fvar_normalize_hash(&self, fvl: FVarList<'t>) -> u64 {
        match fvl {
            None => 0,
            Some(ptr) => {
                let node = self.read_fvar_node(ptr);
                if node.delta == 0 {
                    node.get_hash()
                } else {
                    let tail_hash = node.tail.map(|t| self.read_fvar_node(t).get_hash()).unwrap_or(0);
                    hash64!(FVAR_HASH, 0u64, tail_hash)
                }
            }
        }
    }

    /// Lower bound (smallest free bvar index), or 0 if closed.
    pub(crate) fn fvar_lb(&self, fvl: FVarList<'t>) -> u16 {
        match fvl {
            None => 0,
            Some(ptr) => self.read_fvar_node(ptr).delta,
        }
    }

    /// Canonical hash for cache keys: (struct_hash, normalized_fvar_hash).
    pub(crate) fn canonical_hash(&self, e: ExprPtr<'t>) -> (u64, u64) {
        let expr = self.read_expr(e);
        (expr.get_struct_hash(), self.fvar_normalize_hash(expr.get_fvar_list()))
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
        let hash = hash64!(crate::expr::VAR_HASH, dbj_idx);
        let struct_hash = crate::expr::VAR_HASH;
        let fvar_list = self.fvar_singleton(dbj_idx);
        self.alloc_expr(Expr::Var { dbj_idx, hash, struct_hash, fvar_list })
    }

    pub fn mk_sort(&mut self, level: LevelPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::SORT_HASH, level);
        let struct_hash = hash;
        let fvar_list = None;
        self.alloc_expr(Expr::Sort { level, hash, struct_hash, fvar_list })
    }

    pub fn mk_const(&mut self, name: NamePtr<'t>, levels: LevelsPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::CONST_HASH, name, levels);
        let struct_hash = hash;
        let fvar_list = None;
        self.alloc_expr(Expr::Const { name, levels, hash, struct_hash, fvar_list })
    }

    pub fn mk_app(&mut self, fun: ExprPtr<'t>, arg: ExprPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::APP_HASH, fun, arg);
        let fun_e = self.read_expr(fun);
        let arg_e = self.read_expr(arg);
        let num_loose_bvars = fun_e.num_loose_bvars().max(arg_e.num_loose_bvars());
        let has_fvars = fun_e.has_fvars() || arg_e.has_fvars();
        let struct_hash = hash64!(crate::expr::APP_HASH, fun_e.get_struct_hash(), arg_e.get_struct_hash());
        let fvar_list = self.fvar_union(fun_e.get_fvar_list(), arg_e.get_fvar_list());
        self.alloc_expr(Expr::App { fun, arg, num_loose_bvars, has_fvars, hash, struct_hash, fvar_list })
    }

    pub fn mk_lambda(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::LAMBDA_HASH, binder_name, binder_style, binder_type, body);
        let ty_e = self.read_expr(binder_type);
        let body_e = self.read_expr(body);
        let num_loose_bvars = ty_e.num_loose_bvars().max(body_e.num_loose_bvars().saturating_sub(1));
        let has_fvars = ty_e.has_fvars() || body_e.has_fvars();
        let struct_hash = hash64!(crate::expr::LAMBDA_HASH, binder_name, binder_style, ty_e.get_struct_hash(), body_e.get_struct_hash());
        let body_free_fvl = self.fvar_unbind(body_e.get_fvar_list());
        let fvar_list = self.fvar_union(ty_e.get_fvar_list(), body_free_fvl);
        self.alloc_expr(Expr::Lambda { binder_name, binder_style, binder_type, body, num_loose_bvars, has_fvars, hash, struct_hash, fvar_list })
    }

    pub fn mk_pi(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'t>,
        body: ExprPtr<'t>,
    ) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::PI_HASH, binder_name, binder_style, binder_type, body);
        let ty_e = self.read_expr(binder_type);
        let body_e = self.read_expr(body);
        let num_loose_bvars = ty_e.num_loose_bvars().max(body_e.num_loose_bvars().saturating_sub(1));
        let has_fvars = ty_e.has_fvars() || body_e.has_fvars();
        let struct_hash = hash64!(crate::expr::PI_HASH, binder_name, binder_style, ty_e.get_struct_hash(), body_e.get_struct_hash());
        let body_free_fvl = self.fvar_unbind(body_e.get_fvar_list());
        let fvar_list = self.fvar_union(ty_e.get_fvar_list(), body_free_fvl);
        self.alloc_expr(Expr::Pi { binder_name, binder_style, binder_type, body, num_loose_bvars, has_fvars, hash, struct_hash, fvar_list })
    }

    pub fn mk_let(
        &mut self,
        binder_name: NamePtr<'t>,
        binder_type: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
        nondep: bool
    ) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::LET_HASH, binder_name, binder_type, val, body, nondep);
        let ty_e = self.read_expr(binder_type);
        let val_e = self.read_expr(val);
        let body_e = self.read_expr(body);
        let ty_ub = ty_e.num_loose_bvars();
        let val_ub = val_e.num_loose_bvars();
        let body_ub = body_e.num_loose_bvars();
        let num_loose_bvars = ty_ub.max(val_ub.max(body_ub.saturating_sub(1)));
        let has_fvars = ty_e.has_fvars() || val_e.has_fvars() || body_e.has_fvars();
        let struct_hash = hash64!(crate::expr::LET_HASH, binder_name, ty_e.get_struct_hash(), val_e.get_struct_hash(), body_e.get_struct_hash(), nondep);
        let ty_fvl = ty_e.get_fvar_list();
        let val_fvl = val_e.get_fvar_list();
        let body_free_fvl = self.fvar_unbind(body_e.get_fvar_list());
        let tv_fvl = self.fvar_union(ty_fvl, val_fvl);
        let fvar_list = self.fvar_union(tv_fvl, body_free_fvl);
        self.alloc_expr(Expr::Let { binder_name, binder_type, val, body, num_loose_bvars, has_fvars, hash, nondep, struct_hash, fvar_list })
    }

    pub fn mk_proj(&mut self, ty_name: NamePtr<'t>, idx: u32, structure: ExprPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(crate::expr::PROJ_HASH, ty_name, idx, structure);
        let s_e = self.read_expr(structure);
        let num_loose_bvars = s_e.num_loose_bvars();
        let has_fvars = s_e.has_fvars();
        let struct_hash = hash64!(crate::expr::PROJ_HASH, ty_name, idx, s_e.get_struct_hash());
        let fvar_list = s_e.get_fvar_list();
        self.alloc_expr(Expr::Proj { ty_name, idx, structure, num_loose_bvars, has_fvars, hash, struct_hash, fvar_list })
    }

    pub fn mk_string_lit(&mut self, string_ptr: StringPtr<'t>) -> Option<ExprPtr<'t>> {
        if !self.export_file.config.string_extension {
            return None
        }
        let hash = hash64!(crate::expr::STRING_LIT_HASH, string_ptr);
        let struct_hash = hash;
        let fvar_list = None;
        Some(self.alloc_expr(Expr::StringLit { ptr: string_ptr, hash, struct_hash, fvar_list }))
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
        let struct_hash = hash;
        let fvar_list = None;
        Some(self.alloc_expr(Expr::NatLit { ptr: num_ptr, hash, struct_hash, fvar_list }))
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
        let struct_hash = hash;
        let fvar_list = None;
        self.alloc_expr(Expr::Local { binder_name, binder_style, binder_type, id, hash, struct_hash, fvar_list })
    }

    /// Create a delayed shift node: Shift(inner, amount) means all free Var indices
    /// in `inner` are shifted up by `amount`. O(1) — no traversal.
    /// Collapses nested shifts and elides shifts on closed expressions.
    pub fn mk_shift(&mut self, inner: ExprPtr<'t>, amount: u16) -> ExprPtr<'t> {
        // Lazy shifts: create Shift wrapper nodes instead of traversing.
        // Combined with shift-invariant WHNF cache (canonical hash + shift_eq verification).
        self.mk_shift_lazy(inner, amount)
    }

    pub fn mk_shift_lazy(&mut self, inner: ExprPtr<'t>, amount: u16) -> ExprPtr<'t> {
        self.mk_shift_cutoff(inner, amount, 0)
    }

    /// Create a delayed shift node: Shift(inner, amount, cutoff) means free Var indices
    /// in `inner` with index >= cutoff are shifted up by `amount`. O(1) — no traversal.
    /// Collapses nested shifts when cutoffs match.
    pub fn mk_shift_cutoff(&mut self, inner: ExprPtr<'t>, amount: u16, cutoff: u16) -> ExprPtr<'t> {
        if amount == 0 {
            return inner;
        }
        let inner_expr = self.read_expr(inner);
        let nlbv = inner_expr.num_loose_bvars();
        if nlbv <= cutoff {
            return inner;
        }
        // Collapse nested shifts when cutoffs match: Shift(Shift(e, j, c), k, c) -> Shift(e, j+k, c)
        if let Expr::Shift { inner: inner2, amount: prev, cutoff: prev_cutoff, .. } = inner_expr {
            if prev_cutoff == cutoff {
                return self.mk_shift_cutoff(inner2, prev + amount, cutoff);
            }
        }
        // Eagerly force simple expressions (O(1))
        if cutoff == 0 {
            if let Expr::Var { dbj_idx, .. } = inner_expr {
                return self.mk_var(dbj_idx + amount);
            }
        }
        let has_fvars = inner_expr.has_fvars();
        let hash = hash64!(crate::expr::SHIFT_HASH, inner, amount, cutoff);
        let struct_hash = inner_expr.get_struct_hash();
        let inner_fvl = inner_expr.get_fvar_list();
        let fvar_list = self.fvar_shift_cutoff(inner_fvl, amount, cutoff);
        self.alloc_expr(Expr::Shift { hash, struct_hash, fvar_list, inner, amount, cutoff, num_loose_bvars: nlbv + amount, has_fvars })
    }

    /// Shallow shift: peel one level of constructor, wrapping children in lazy Shift nodes.
    /// `force_shift_shallow(Shift(Pi(ty, body), k))` → `Pi(Shift(ty, k), Shift(body, k))`
    /// O(1) per node vs O(n) for full traversal. Returns e unchanged if no shift needed.
    ///
    /// TODO: Replace force_shift calls in unfold_apps/whnf/def_eq with a "shallowish" force
    /// that pushes Shift just far enough for all consumers:
    ///
    /// All consumers (whnf_no_unfolding, def_eq, infer_app) work via unfold_apps first,
    /// then match on the head. So "far enough" means:
    ///  1. Peel the entire App spine: shift each arg (lazy), shift the head
    ///  2. Force the head one level to expose its constructor tag + immediate fields:
    ///     - Var: eagerly compute shifted index (already done by mk_shift_lazy)
    ///     - Const/Sort/NatLit/StringLit/Local: closed, no shift needed
    ///     - Pi/Lambda: expose binder_type (lazy Shift) and body (shift_expr with cutoff=1)
    ///     - Let: expose binder_type, val (lazy Shift), body (shift_expr cutoff=1)
    ///     - Proj: expose structure (lazy Shift)
    ///  3. Leave everything deeper as Shift nodes
    ///
    /// This is O(n_args) per whnf/def_eq step instead of O(expr_size).
    /// The blocker was def_eq: it calls whnf_no_unfolding_cheap_proj on both sides, which
    /// calls unfold_apps (peeling Shift on the spine), then rebuilds via foldl_apps.
    /// The rebuilt expression has Shift-wrapped args. When def_eq_app recursively compares
    /// args, each arg is a Shift node. The recursive def_eq call peels it via whnf, which
    /// again does unfold_apps + foldl_apps, pushing Shift one level deeper each time.
    /// This SHOULD converge at leaves (Var/Const), but the interaction with def_eq's
    /// eq_cache, failure_cache, and proof_irrel_eq creates subtle bugs where comparisons
    /// that should succeed return false. Needs careful investigation of def_eq's full
    /// control flow with inner Shift nodes.
    /// Shallow shift: peel one level of constructor, wrapping children in lazy Shift nodes.
    /// With cutoff support, binder bodies get `Shift(body, amount, cutoff+1)` — fully lazy.
    pub fn force_shift_shallow(&mut self, e: ExprPtr<'t>, amount: u16, cutoff: u16) -> ExprPtr<'t> {
        if amount == 0 {
            return e;
        }
        let expr = self.read_expr(e);
        if expr.num_loose_bvars() <= cutoff {
            return e;
        }
        match expr {
            Expr::Shift { inner, amount: prev, cutoff: prev_cutoff, .. } => {
                if prev_cutoff == cutoff {
                    // Collapse: Shift(Shift(inner, prev, c), amount, c) → shallow(inner, prev+amount, c)
                    self.force_shift_shallow(inner, prev + amount, cutoff)
                } else {
                    // Different cutoffs — force inner first, then shallow outer
                    let forced = self.force_shift_aux(inner, prev, prev_cutoff);
                    self.force_shift_shallow(forced, amount, cutoff)
                }
            }
            Expr::Var { dbj_idx, .. } => {
                if dbj_idx >= cutoff {
                    self.mk_var(dbj_idx + amount)
                } else {
                    e
                }
            }
            Expr::App { fun, arg, .. } => {
                let fun = self.mk_shift_cutoff(fun, amount, cutoff);
                let arg = self.mk_shift_cutoff(arg, amount, cutoff);
                self.mk_app(fun, arg)
            }
            Expr::Pi { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.mk_shift_cutoff(binder_type, amount, cutoff);
                let body = self.mk_shift_cutoff(body, amount, cutoff + 1);
                self.mk_pi(binder_name, binder_style, binder_type, body)
            }
            Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.mk_shift_cutoff(binder_type, amount, cutoff);
                let body = self.mk_shift_cutoff(body, amount, cutoff + 1);
                self.mk_lambda(binder_name, binder_style, binder_type, body)
            }
            Expr::Let { binder_name, binder_type, val, body, nondep, .. } => {
                let binder_type = self.mk_shift_cutoff(binder_type, amount, cutoff);
                let val = self.mk_shift_cutoff(val, amount, cutoff);
                let body = self.mk_shift_cutoff(body, amount, cutoff + 1);
                self.mk_let(binder_name, binder_type, val, body, nondep)
            }
            Expr::Proj { ty_name, idx, structure, .. } => {
                let structure = self.mk_shift_cutoff(structure, amount, cutoff);
                self.mk_proj(ty_name, idx, structure)
            }
            Expr::Sort { .. } | Expr::Const { .. } | Expr::Local { .. } | Expr::StringLit { .. } | Expr::NatLit { .. } => {
                panic!("force_shift_shallow on closed expression")
            }
        }
    }

    /// Force a Shift node: eagerly apply the shift via full traversal.
    /// If `e` is not a Shift node, returns it unchanged.
    pub fn force_shift(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        match self.read_expr(e) {
            Expr::Shift { inner, amount, cutoff, .. } => {
                self.force_shift_aux(inner, amount, cutoff)
            }
            _ => e
        }
    }

    /// View an expression with Shift pushed one level inside.
    /// Never returns `Expr::Shift` — children may be Shift-wrapped.
    /// Replaces the common `force_shift(e); match read_expr(e)` pattern
    /// with the cheaper `match view_expr(e)` (O(1) per node via force_shift_shallow).
    pub fn view_expr(&mut self, e: ExprPtr<'t>) -> Expr<'t> {
        match self.read_expr(e) {
            Expr::Shift { inner, amount, cutoff, .. } => {
                let shallow = self.force_shift_shallow(inner, amount, cutoff);
                self.read_expr(shallow)
            }
            other => other
        }
    }

    /// Full shift traversal that never creates Shift nodes.
    pub(crate) fn force_shift_aux(&mut self, e: ExprPtr<'t>, amount: u16, cutoff: u16) -> ExprPtr<'t> {
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.force_shift_aux_inner(e, amount, cutoff))
    }

    fn force_shift_aux_inner(&mut self, e: ExprPtr<'t>, amount: u16, cutoff: u16) -> ExprPtr<'t> {
        if amount == 0 || self.num_loose_bvars(e) <= cutoff {
            return e
        }
        if let Some(&cached) = self.expr_cache.shift_cache.get(&(e, amount, cutoff)) {
            return cached;
        }
        let calcd = match self.read_expr(e) {
            Expr::Sort { .. } | Expr::Const { .. } | Expr::Local { .. } | Expr::StringLit { .. } | Expr::NatLit { .. } => panic!(),
            Expr::Shift { inner, amount: prev, cutoff: prev_cutoff, .. } => {
                let forced = self.force_shift_aux(inner, prev, prev_cutoff);
                self.force_shift_aux(forced, amount, cutoff)
            }
            Expr::Var { dbj_idx, .. } => {
                if dbj_idx >= cutoff {
                    self.mk_var(dbj_idx + amount)
                } else {
                    e
                }
            }
            Expr::App { fun, arg, .. } => {
                let fun = self.force_shift_aux(fun, amount, cutoff);
                let arg = self.force_shift_aux(arg, amount, cutoff);
                self.mk_app(fun, arg)
            }
            Expr::Pi { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.force_shift_aux(binder_type, amount, cutoff);
                let body = self.force_shift_aux(body, amount, cutoff + 1);
                self.mk_pi(binder_name, binder_style, binder_type, body)
            }
            Expr::Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.force_shift_aux(binder_type, amount, cutoff);
                let body = self.force_shift_aux(body, amount, cutoff + 1);
                self.mk_lambda(binder_name, binder_style, binder_type, body)
            }
            Expr::Let { binder_name, binder_type, val, body, nondep, .. } => {
                let binder_type = self.force_shift_aux(binder_type, amount, cutoff);
                let val = self.force_shift_aux(val, amount, cutoff);
                let body = self.force_shift_aux(body, amount, cutoff + 1);
                self.mk_let(binder_name, binder_type, val, body, nondep)
            }
            Expr::Proj { ty_name, idx, structure, .. } => {
                let structure = self.force_shift_aux(structure, amount, cutoff);
                self.mk_proj(ty_name, idx, structure)
            }
        };
        self.expr_cache.shift_cache.insert((e, amount, cutoff), calcd);
        calcd
    }
}

#[derive(Debug)]
pub struct LeanDag<'a> {
    pub names: UniqueIndexSet<Name<'a>>,
    pub levels: UniqueIndexSet<Level<'a>>,
    pub exprs: UniqueIndexSet<Expr<'a>>,
    pub uparams: FxIndexSet<Arc<[LevelPtr<'a>]>>,
    pub strings: FxIndexSet<CowStr<'a>>,
    pub bignums: Option<FxIndexSet<BigUint>>,
    pub fvarlists: UniqueIndexSet<FVarNode<'a>>,
}

impl<'a> LeanDag<'a> {
    /// The export file format does not output the anonymous name and level zero, but the export
    /// program back-references them as though they were the 0th element of their kind; the exporter
    /// implicitly assumes that whatever you're using for storage knows about this convention.
    ///
    /// So when creating a new parser, we need to begin by placing `Anon` and `Zero` in the 0th position
    /// of their backing storage, satisfying the exporter's assumption.
    pub fn new(config: &Config) -> Self {
        let mut out = Self {
            names: new_unique_index_set(),
            levels: new_unique_index_set(),
            exprs: new_unique_index_set(),
            uparams: new_fx_index_set(),
            strings: new_fx_index_set(),
            bignums: if config.nat_extension { Some(new_fx_index_set()) } else { None },
            fvarlists: new_unique_index_set(),
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
    pub(crate) infer_cache_check: UniqueHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    pub(crate) infer_cache_no_check: UniqueHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    /// Shift-invariant WHNF cache: keyed by canonical hash (struct_hash, fvar_normalize_hash),
    /// stores (input_expr, result_expr, bvar_ub). On hit, verify with shift_eq, then
    /// force_shift_aux(result, delta) where delta = query_bvar_ub - stored_bvar_ub.
    pub(crate) whnf_cache: FxHashMap<(u64, u64), (ExprPtr<'t>, ExprPtr<'t>, u16)>,
    pub(crate) whnf_no_unfolding_cache: UniqueHashMap<ExprPtr<'t>, ExprPtr<'t>>,
    pub(crate) eq_cache: UnionFind<ExprPtr<'t>>,
    /// A cache of congruence failures during the lazy delta step procedure.
    pub(crate) failure_cache: FxHashSet<(ExprPtr<'t>, ExprPtr<'t>)>,
    /// Strong reduction is not used during type-checking, this is more of a library/inspection feature.
    pub(crate) strong_cache: UniqueHashMap<(ExprPtr<'t>, bool, bool), ExprPtr<'t>>,
    /// Shift-invariant infer cache for open expressions, organized as a stack.
    /// `infer_open_cache[cd-1]` stores entries at canonical depth `cd = depth - fvar_lb`.
    /// Each map keys by canonical hash → (stored_input, stored_result, stored_depth).
    /// On hit, verify with shift_eq and apply delta via mk_shift.
    /// Push/pop follows local_ctx for O(1) eviction.
    pub(crate) infer_open_cache: Vec<FxHashMap<(u64, u64), (ExprPtr<'t>, ExprPtr<'t>, u16)>>,
}

impl<'t> TcCache<'t> {
    pub(crate) fn new() -> Self {
        Self {
            infer_cache_check: new_unique_hash_map(),
            infer_cache_no_check: new_unique_hash_map(),
            whnf_cache: new_fx_hash_map(),
            whnf_no_unfolding_cache: new_unique_hash_map(),
            eq_cache: UnionFind::new(),
            failure_cache: new_fx_hash_set(),
            strong_cache: new_unique_hash_map(),
            infer_open_cache: Vec::new(),
        }
    }

    pub(crate) fn clear(&mut self) {
        self.infer_cache_check.clear();
        self.infer_cache_no_check.clear();
        self.whnf_cache.clear();
        self.whnf_no_unfolding_cache.clear();
        self.eq_cache.clear();
        self.failure_cache.clear();
        self.strong_cache.clear();
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
    /// This is checked so as to be mutually exclusive with any of the axiom allow list/whitelist features.
    #[serde(default)]
    pub unsafe_permit_all_axioms: bool,
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
                Ok(file) => crate::parser::parse_export_file(BufReader::new(file), self),
                Err(e) => Err(Box::from(format!("Failed to open export file: {:?}", e))),
            }
        } else if self.use_stdin {
            let reader = BufReader::new(std::io::stdin());
            crate::parser::parse_export_file(reader, self)
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

