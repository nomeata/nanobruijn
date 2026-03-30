//! Implementation of Lean expressions
use crate::util::{BigUintPtr, ExprPtr, FxHashMap, LevelPtr, LevelsPtr, NamePtr, Ptr, StringPtr, TcCtx};
use num_bigint::BigUint;
use num_traits::identities::Zero;
use Expr::*;
use serde::Deserialize;

pub(crate) const VAR_HASH: u64 = 281;
pub(crate) const SORT_HASH: u64 = 563;
pub(crate) const CONST_HASH: u64 = 1129;
pub(crate) const PROJ_HASH: u64 = 17;
pub(crate) const LAMBDA_HASH: u64 = 431;
pub(crate) const LET_HASH: u64 = 241;
pub(crate) const PI_HASH: u64 = 719;
pub(crate) const APP_HASH: u64 = 233;
pub(crate) const LOCAL_HASH: u64 = 211;
pub(crate) const STRING_LIT_HASH: u64 = 1493;
pub(crate) const NAT_LIT_HASH: u64 = 1583;
pub(crate) const SHIFT_HASH: u64 = 1699;
pub(crate) const FVAR_HASH: u64 = 1871;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expr<'a> {
    /// A string literal with a pointer to a utf-8 string.
    StringLit {
        hash: u64,
        struct_hash: u64,
        fvar_list: FVarList<'a>,
        ptr: StringPtr<'a>,
    },
    /// A nat literal, holds a pointer to an arbitrary precision bignum.
    NatLit {
        hash: u64,
        struct_hash: u64,
        fvar_list: FVarList<'a>,
        ptr: BigUintPtr<'a>,
    },
    Proj {
        hash: u64,
        struct_hash: u64,
        fvar_list: FVarList<'a>,
        /// The name of the structure being projected. E.g. `Prod` if this is
        /// projection 0 of `Prod.mk ..`
        ty_name: NamePtr<'a>,
        /// The 0-based position of the constructor argument, not considering the
        /// parameters. For some struct Foo A B, and a constructor Foo.mk A B p q r s,
        /// `q` will have idx 1.
        idx: u32,
        structure: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    /// A bound variable represented by a deBruijn index.
    Var {
        hash: u64,
        struct_hash: u64,
        fvar_list: FVarList<'a>,
        dbj_idx: u16,
    },
    Sort {
        hash: u64,
        struct_hash: u64,
        fvar_list: FVarList<'a>,
        level: LevelPtr<'a>,
    },
    Const {
        hash: u64,
        struct_hash: u64,
        fvar_list: FVarList<'a>,
        name: NamePtr<'a>,
        levels: LevelsPtr<'a>,
    },
    App {
        hash: u64,
        struct_hash: u64,
        fvar_list: FVarList<'a>,
        fun: ExprPtr<'a>,
        arg: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Pi {
        hash: u64,
        struct_hash: u64,
        fvar_list: FVarList<'a>,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        body: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Lambda {
        hash: u64,
        struct_hash: u64,
        fvar_list: FVarList<'a>,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        body: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Let {
        hash: u64,
        struct_hash: u64,
        fvar_list: FVarList<'a>,
        binder_name: NamePtr<'a>,
        binder_type: ExprPtr<'a>,
        val: ExprPtr<'a>,
        body: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
        nondep: bool
    },
    /// A free variable with binder information and a unique identifier.
    Local {
        hash: u64,
        struct_hash: u64,
        fvar_list: FVarList<'a>,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        id: FVarId,
    },
    /// Delayed shift: free Var indices in `inner` with index >= `cutoff` are shifted up by `amount`.
    /// Created by mk_shift (cutoff=0) or mk_shift_cutoff (cutoff>0).
    /// Collapsed on nesting when cutoffs match: Shift(Shift(e, j, c), k, c) → Shift(e, j+k, c).
    /// Elided when inner has no free bvars above cutoff.
    Shift {
        hash: u64,
        struct_hash: u64,
        fvar_list: FVarList<'a>,
        inner: ExprPtr<'a>,
        amount: u16,
        cutoff: u16,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
}

/// Free variable identifiers using unique IDs from a monotonically increasing counter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FVarId {
    Unique(u32),
}

/// A node in a delta-encoded sorted set of free bvar indices.
/// The set {a0, a1, a2, ...} (sorted) is encoded as [a0, a1-a0-1, a2-a1-1, ...].
/// None = empty set (closed). Some(ptr) = non-empty.
pub type FVarList<'a> = Option<FVarListPtr<'a>>;
pub type FVarListPtr<'a> = Ptr<&'a FVarNode<'a>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FVarNode<'a> {
    /// Hash of this node (delta + tail hash), for hash-consing via UniqueHasher.
    pub(crate) hash: u64,
    /// For the head: the lower bound (smallest free bvar index).
    /// For subsequent nodes: the gap minus 1 to the next free bvar index.
    pub(crate) delta: u16,
    /// The rest of the list.
    pub(crate) tail: FVarList<'a>,
}

impl<'a> FVarNode<'a> {
    pub(crate) fn get_hash(&self) -> u64 { self.hash }
}

impl<'a> std::hash::Hash for FVarNode<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.hash) }
}

impl<'a> Expr<'a> {
    pub(crate) fn get_hash(&self) -> u64 {
        match self {
            Var { hash, .. }
            | Sort { hash, .. }
            | Const { hash, .. }
            | App { hash, .. }
            | Pi { hash, .. }
            | Lambda { hash, .. }
            | Let { hash, .. }
            | Local { hash, .. }
            | StringLit { hash, .. }
            | NatLit { hash, .. }
            | Proj { hash, .. }
            | Shift { hash, .. } => *hash,
        }
    }

    pub(crate) fn get_struct_hash(&self) -> u64 {
        match self {
            Var { struct_hash, .. }
            | Sort { struct_hash, .. }
            | Const { struct_hash, .. }
            | App { struct_hash, .. }
            | Pi { struct_hash, .. }
            | Lambda { struct_hash, .. }
            | Let { struct_hash, .. }
            | Local { struct_hash, .. }
            | StringLit { struct_hash, .. }
            | NatLit { struct_hash, .. }
            | Proj { struct_hash, .. }
            | Shift { struct_hash, .. } => *struct_hash,
        }
    }

    pub(crate) fn get_fvar_list(&self) -> FVarList<'a> {
        match self {
            Var { fvar_list, .. }
            | Sort { fvar_list, .. }
            | Const { fvar_list, .. }
            | App { fvar_list, .. }
            | Pi { fvar_list, .. }
            | Lambda { fvar_list, .. }
            | Let { fvar_list, .. }
            | Local { fvar_list, .. }
            | StringLit { fvar_list, .. }
            | NatLit { fvar_list, .. }
            | Proj { fvar_list, .. }
            | Shift { fvar_list, .. } => *fvar_list,
        }
    }
}
impl<'a> std::hash::Hash for Expr<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
}

/// The style of this binder (in Lean's vernacular, the brackets used to write it).
/// `(_ : _)` for default, `{_ : _}` for implicit, `{{_ : _}}` for strict implicit,
/// and `[_ : _]` for instance implicit.
///
/// These are only used by the pretty printer, and do not change the behavior of
/// type checking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Deserialize)]
pub enum BinderStyle {
    #[serde(rename = "default")]
    Default,
    #[serde(rename = "implicit")]
    Implicit,
    #[serde(rename = "strictImplicit")]
    StrictImplicit,
    #[serde(rename = "instImplicit")]
    InstanceImplicit,
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    pub(crate) fn inst_forall_params(&mut self, mut e: ExprPtr<'t>, n: usize, all_args: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        for _ in 0..n {
            if let Pi { body, .. } = self.view_expr(e) {
                e = body
            } else {
                panic!()
            }
        }
        self.inst_beta(e, &all_args[0..n])
    }

    /// Instantiate `e` with the substitutions in `substs`.
    /// Replaces Var(offset + i) with substs[rev(i)] for i < substs.len().
    /// Vars beyond the substitution range are left unchanged (no shifting).
    /// Used for local-to-local replacement (e.g. replace_params, inductive.rs).
    pub fn inst(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        if substs.is_empty() {
            return e
        }
        self.expr_cache.inst_cache.clear();
        self.inst_aux(e, substs, 0, false)
    }

    /// Like `inst`, but also shifts down Var indices beyond the substitution range.
    /// Used for beta reduction and let-substitution where binders are being removed.
    pub fn inst_beta(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        if substs.is_empty() {
            return e
        }
        self.expr_cache.inst_cache.clear();
        self.inst_aux(e, substs, 0, true)
    }

    fn inst_aux(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>], offset: u16, shift_down: bool) -> ExprPtr<'t> {
        if self.num_loose_bvars(e) <= offset {
            e
        } else if let Some(cached) = self.expr_cache.inst_cache.get(&(e, offset)) {
            *cached
        } else {
            let n_substs = substs.len() as u16;
            let calcd = match self.read_expr(e) {
                // These expressions should be unreachable since they return `n_loose_bvars() == 0`
                Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => panic!(),
                Shift { inner, amount, cutoff, .. } => {
                    // Force the shift, then substitute on the result.
                    let forced = self.force_shift_aux(inner, amount, cutoff);
                    self.inst_aux(forced, substs, offset, shift_down)
                }
                Var { dbj_idx, .. } => {
                    debug_assert!(dbj_idx >= offset);
                    let rel_idx = dbj_idx - offset;
                    if rel_idx < n_substs {
                        // Within substitution range: replace with subst (in reverse order).
                        // Shift the value up by `offset` to account for binders we traversed.
                        // Force any Shift wrappers so inst results are structurally canonical
                        // (avoids cascading Shift wrappers from lazy unfold_apps).
                        let val = self.force_shift(substs[substs.len() - 1 - rel_idx as usize]);
                        if offset > 0 {
                            self.force_shift_aux(val, offset, 0)
                        } else {
                            val
                        }
                    } else if shift_down {
                        // Beyond substitution range: shift down by n_substs (for beta reduction)
                        self.mk_var(dbj_idx - n_substs)
                    } else {
                        // Beyond substitution range: leave unchanged (for type-level substitution)
                        e
                    }
                }
                App { fun, arg, .. } => {
                    let fun = self.inst_aux(fun, substs, offset, shift_down);
                    let arg = self.inst_aux(arg, substs, offset, shift_down);
                    self.mk_app(fun, arg)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.inst_aux(binder_type, substs, offset, shift_down);
                    let body = self.inst_aux(body, substs, offset + 1, shift_down);
                    self.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.inst_aux(binder_type, substs, offset, shift_down);
                    let body = self.inst_aux(body, substs, offset + 1, shift_down);
                    self.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let binder_type = self.inst_aux(binder_type, substs, offset, shift_down);
                    let val = self.inst_aux(val, substs, offset, shift_down);
                    let body = self.inst_aux(body, substs, offset + 1, shift_down);
                    self.mk_let(binder_name, binder_type, val, body, nondep)
                }
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.inst_aux(structure, substs, offset, shift_down);
                    self.mk_proj(ty_name, idx, structure)
                }
            };
            self.expr_cache.inst_cache.insert((e, offset), calcd);
            calcd
        }
    }

    /// Shift all free variables in `e` (those with index >= cutoff) up by `amount`.
    /// For cutoff=0, creates a lazy Shift node (O(1)).
    /// For cutoff>0, traverses and rebuilds.
    pub fn shift_expr(&mut self, e: ExprPtr<'t>, amount: u16, cutoff: u16) -> ExprPtr<'t> {
        if amount == 0 || self.num_loose_bvars(e) <= cutoff {
            return e
        }
        if cutoff == 0 {
            return self.mk_shift(e, amount);
        }
        self.shift_expr_aux(e, amount, cutoff)
    }

    fn shift_expr_aux(&mut self, e: ExprPtr<'t>, amount: u16, cutoff: u16) -> ExprPtr<'t> {
        if self.num_loose_bvars(e) <= cutoff {
            return e
        }
        if let Some(&cached) = self.expr_cache.shift_cache.get(&(e, amount, cutoff)) {
            return cached;
        }
        let calcd = match self.read_expr(e) {
            Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => panic!(),
            Shift { inner, amount: prev, cutoff: prev_cutoff, .. } => {
                // Force the inner shift first, then apply the outer shift.
                let forced = self.force_shift_aux(inner, prev, prev_cutoff);
                self.shift_expr_aux(forced, amount, cutoff)
            }
            Var { dbj_idx, .. } => {
                if dbj_idx >= cutoff {
                    self.mk_var(dbj_idx + amount)
                } else {
                    e
                }
            }
            App { fun, arg, .. } => {
                let fun = self.shift_expr_aux(fun, amount, cutoff);
                let arg = self.shift_expr_aux(arg, amount, cutoff);
                self.mk_app(fun, arg)
            }
            Pi { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.shift_expr_aux(binder_type, amount, cutoff);
                let body = self.shift_expr_aux(body, amount, cutoff + 1);
                self.mk_pi(binder_name, binder_style, binder_type, body)
            }
            Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let binder_type = self.shift_expr_aux(binder_type, amount, cutoff);
                let body = self.shift_expr_aux(body, amount, cutoff + 1);
                self.mk_lambda(binder_name, binder_style, binder_type, body)
            }
            Let { binder_name, binder_type, val, body, nondep, .. } => {
                let binder_type = self.shift_expr_aux(binder_type, amount, cutoff);
                let val = self.shift_expr_aux(val, amount, cutoff);
                let body = self.shift_expr_aux(body, amount, cutoff + 1);
                self.mk_let(binder_name, binder_type, val, body, nondep)
            }
            Proj { ty_name, idx, structure, .. } => {
                let structure = self.shift_expr_aux(structure, amount, cutoff);
                self.mk_proj(ty_name, idx, structure)
            }
        };
        self.expr_cache.shift_cache.insert((e, amount, cutoff), calcd);
        calcd
    }

    /// From `e[x_1..x_n/v_1..v_n]`, abstract and re-inst, creating `e[y_1..y_n/v_1..v_n]`.
    pub(crate) fn replace_params(
        &mut self,
        e: ExprPtr<'t>,
        ingoing: &[ExprPtr<'t>],
        outgoing: &[ExprPtr<'t>],
    ) -> ExprPtr<'t> {
        let e = self.abstr(e, outgoing);
        self.inst(e, ingoing)
    }

    fn abstr_aux(&mut self, e: ExprPtr<'t>, locals: &[ExprPtr<'t>], offset: u16) -> ExprPtr<'t> {
        if !self.has_fvars(e) {
            e
        } else if let Some(cached) = self.expr_cache.abstr_cache.get(&(e, offset)) {
            *cached
        } else {
            let calcd = match self.read_expr(e) {
                Local { .. } =>
                    locals.iter().rev().position(|x| *x == e).map(|pos| self.mk_var(pos as u16 + offset)).unwrap_or(e),
                App { fun, arg, .. } => {
                    let fun = self.abstr_aux(fun, locals, offset);
                    let arg = self.abstr_aux(arg, locals, offset);
                    self.mk_app(fun, arg)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.abstr_aux(binder_type, locals, offset);
                    let body = self.abstr_aux(body, locals, offset + 1);
                    self.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.abstr_aux(binder_type, locals, offset);
                    let body = self.abstr_aux(body, locals, offset + 1);
                    self.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let binder_type = self.abstr_aux(binder_type, locals, offset);
                    let val = self.abstr_aux(val, locals, offset);
                    let body = self.abstr_aux(body, locals, offset + 1);
                    self.mk_let(binder_name, binder_type, val, body, nondep)
                }
                StringLit { .. } | NatLit { .. } => panic!(),
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.abstr_aux(structure, locals, offset);
                    self.mk_proj(ty_name, idx, structure)
                }
                Shift { .. } => {
                    let forced = self.force_shift(e);
                    self.abstr_aux(forced, locals, offset)
                }
                Var { .. } | Sort { .. } | Const { .. } => panic!("should flag as no locals"),
            };

            self.expr_cache.abstr_cache.insert((e, offset), calcd);
            calcd
        }
    }

    /// Abstraction of unique identifiers; replaces free variables with the appropriate
    /// bound variable, if the free variable is in `locals`.
    pub fn abstr(&mut self, e: ExprPtr<'t>, locals: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        self.expr_cache.abstr_cache.clear();
        self.abstr_aux(e, locals, 0u16)
    }

    fn subst_aux(&mut self, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> ExprPtr<'t> {
        if let Some(cached) = self.expr_cache.subst_cache.get(&(e, ks, vs)) {
            *cached
        } else {
            let r = match self.view_expr(e) {
                Var { .. } | NatLit { .. } | StringLit { .. } => e,
                Sort { level, .. } => {
                    let level = self.subst_level(level, ks, vs);
                    self.mk_sort(level)
                }
                Const { name, levels, .. } => {
                    let levels = self.subst_levels(levels, ks, vs);
                    self.mk_const(name, levels)
                }
                App { fun, arg, .. } => {
                    let fun = self.subst_aux(fun, ks, vs);
                    let arg = self.subst_aux(arg, ks, vs);
                    self.mk_app(fun, arg)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.subst_aux(binder_type, ks, vs);
                    let body = self.subst_aux(body, ks, vs);
                    self.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.subst_aux(binder_type, ks, vs);
                    let body = self.subst_aux(body, ks, vs);
                    self.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let binder_type = self.subst_aux(binder_type, ks, vs);
                    let val = self.subst_aux(val, ks, vs);
                    let body = self.subst_aux(body, ks, vs);
                    self.mk_let(binder_name, binder_type, val, body, nondep)
                }
                Local { .. } => panic!("level substitution should not find locals"),
                Shift { .. } => unreachable!("view_expr never returns Shift"),
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.subst_aux(structure, ks, vs);
                    self.mk_proj(ty_name, idx, structure)
                }
            };
            self.expr_cache.subst_cache.insert((e, ks, vs), r);
            r
        }
    }

    pub fn subst_expr_levels(&mut self, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> ExprPtr<'t> {
        if let Some(cached) = self.expr_cache.dsubst_cache.get(&(e, ks, vs)).copied() {
            return cached
        }
        self.expr_cache.subst_cache.clear();
        assert_eq!(self.read_levels(ks).len(), self.read_levels(vs).len());
        let out = self.subst_aux(e, ks, vs);
        self.expr_cache.dsubst_cache.insert((e, ks, vs), out);
        out
    }

    pub(crate) fn subst_declar_info_levels(
        &mut self,
        info: crate::env::DeclarInfo<'t>,
        in_vals: LevelsPtr<'t>,
    ) -> ExprPtr<'t> {
        self.subst_expr_levels(info.ty, info.uparams, in_vals)
    }

    pub fn num_args(&self, e: ExprPtr<'t>) -> usize {
        let (mut cursor, mut num_args) = (e, 0);
        while let App { fun, .. } = self.read_expr(cursor) {
            cursor = fun;
            num_args += 1;
        }
        num_args
    }

    /// From `f a_0 .. a_N`, return `f`
    pub fn unfold_apps_fun(&mut self, mut e: ExprPtr<'t>) -> ExprPtr<'t> {
        loop {
            match self.view_expr(e) {
                App { fun, .. } => e = fun,
                _ => return self.force_shift(e),
            }
        }
    }

    /// From `f a_0 .. a_N`, return `(f, [a_0, ..a_N])`
    /// Accumulates Shift through the App spine; returns lazy (Shift-wrapped) args and fun.
    pub fn unfold_apps(&mut self, mut e: ExprPtr<'t>) -> (ExprPtr<'t>, Vec<ExprPtr<'t>>) {
        let mut args = Vec::new();
        let mut pending_shift: u16 = 0;
        loop {
            match self.read_expr(e) {
                Shift { inner, amount, cutoff: 0, .. } => {
                    pending_shift += amount;
                    e = inner;
                }
                Shift { inner, amount, cutoff, .. } => {
                    // Force the cutoff>0 shift, then apply accumulated pending shift
                    let forced = self.force_shift_aux(inner, amount, cutoff);
                    if pending_shift > 0 {
                        e = self.mk_shift(forced, pending_shift);
                        pending_shift = 0;
                    } else {
                        e = forced;
                    }
                }
                App { fun, arg, .. } => {
                    e = fun;
                    let arg = if pending_shift > 0 {
                        self.mk_shift(arg, pending_shift)
                    } else {
                        arg
                    };
                    args.push(arg);
                },
                _ => {
                    if pending_shift > 0 {
                        e = self.mk_shift(e, pending_shift);
                    }
                    break;
                }
            }
        }
        args.reverse();
        (e, args)
    }

    /// If this is a const application, return (Const {..}, name, levels, args)
    pub fn unfold_const_apps(
        &mut self,
        e: ExprPtr<'t>,
    ) -> Option<(ExprPtr<'t>, NamePtr<'t>, LevelsPtr<'t>, Vec<ExprPtr<'t>>)> {
        let (f, args) = self.unfold_apps(e);
        match self.read_expr(f) {
            Const { name, levels, .. } => Some((f, name, levels, args)),
            _ => None,
        }
    }
    /// If this is an application of `Const(name, levels)`, return `(name, levels)`
    pub fn try_const_info(&self, e: ExprPtr<'t>) -> Option<(NamePtr<'t>, LevelsPtr<'t>)> {
        match self.read_expr(e) {
            Const { name, levels, .. } => Some((name, levels)),
            _ => None,
        }
    }

    pub(crate) fn unfold_apps_stack(&mut self, mut e: ExprPtr<'t>) -> (ExprPtr<'t>, Vec<ExprPtr<'t>>) {
        let mut args = Vec::new();
        loop {
            match self.view_expr(e) {
                App { fun, arg, .. } => {
                    args.push(arg);
                    e = fun;
                }
                _ => {
                    e = self.force_shift(e);
                    break
                }
            }
        }
        (e, args)
    }

    pub fn foldl_apps(&mut self, mut fun: ExprPtr<'t>, args: impl Iterator<Item = ExprPtr<'t>>) -> ExprPtr<'t> {
        for arg in args {
            fun = self.mk_app(fun, arg);
        }
        fun
    }

    pub(crate) fn abstr_pis<I>(&mut self, mut binders: I, mut body: ExprPtr<'t>) -> ExprPtr<'t>
    where
        I: Iterator<Item = ExprPtr<'t>> + DoubleEndedIterator, {
        while let Some(local) = binders.next_back() {
            body = self.abstr_pi(local, body)
        }
        body
    }

    pub(crate) fn abstr_pi(&mut self, binder: ExprPtr<'t>, body: ExprPtr<'t>) -> ExprPtr<'t> {
        match self.read_expr(binder) {
            Local { binder_name, binder_style, binder_type, .. } => {
                let body = self.abstr(body, &[binder]);
                self.mk_pi(binder_name, binder_style, binder_type, body)
            }
            _ => unreachable!("Cannot apply pi with non-local domain type"),
        }
    }

    pub(crate) fn apply_lambda(&mut self, binder: ExprPtr<'t>, body: ExprPtr<'t>) -> ExprPtr<'t> {
        match self.read_expr(binder) {
            Local { binder_name, binder_style, binder_type, .. } => {
                let body = self.abstr(body, &[binder]);
                self.mk_lambda(binder_name, binder_style, binder_type, body)
            }
            _ => unreachable!("Cannot apply lambda with non-local domain type"),
        }
    }
    
    pub(crate) fn is_nat_zero(&mut self, e: ExprPtr<'t>) -> bool {
        match self.read_expr(e) {
            Const { .. } => self.c_nat_zero() == Some(e),
            NatLit { ptr, .. } => self.read_bignum(ptr).map(|n| n.is_zero()).unwrap_or(false),
            _ => false,
        }
    }

    pub(crate) fn pred_of_nat_succ(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        match self.read_expr(e) {
            App { fun, arg, .. } if self.c_nat_succ() == Some(fun) => Some(arg),
            NatLit { ptr, .. } => {
                let n = self.read_bignum(ptr)?;
                if n.is_zero() {
                    None
                } else {
                    self.mk_nat_lit_quick(n - 1u8)
                }
            }
            _ => None,
        }
    }

    /// Used in iota reduction (`reduce_rec`) to turn a bignum
    /// either `Nat.zero`, or `App (Nat.succ) (bignum - 1)`; in order to do iota reduction,
    /// we need to know what constructor the major premise comes from.
    pub(crate) fn nat_lit_to_constructor(&mut self, n: BigUintPtr<'t>) -> Option<ExprPtr<'t>> {
        assert!(self.export_file.config.nat_extension);
        let n = self.read_bignum(n).unwrap();
        if n.is_zero() {
            self.c_nat_zero()
        } else {
            let pred = self.alloc_bignum(core::ops::Sub::sub(n, 1u8)).unwrap();
            let pred = self.mk_nat_lit(pred).unwrap();
            let succ_c = self.c_nat_succ()?;
            Some(self.mk_app(succ_c, pred))
        }
    }
    
    /// Return `true` iff `e` is an application of `@eagerReduce A a`
    pub(crate) fn is_eager_reduce_app(&self, e: ExprPtr<'t>) -> bool {
        if let App {fun, ..} = self.read_expr(e) {
            if let App {fun, ..} = self.read_expr(fun) {
                if let Const {name, ..} = self.read_expr(fun) {
                    return self.export_file.name_cache.eager_reduce == Some(name)
                }
            }
        }
        false
    }

    /// Convert a string literal to `String.ofList <| List.cons (Char.ofNat _) .. List.nil`
    pub(crate) fn str_lit_to_constructor(&mut self, s: StringPtr<'t>) -> Option<ExprPtr<'t>> {
        if (!self.export_file.config.string_extension) || (!self.export_file.config.nat_extension) {
            return None
        }
        let zero = self.zero();
        let empty_levels = self.alloc_levels_slice(&[]);
        let tyzero_levels = self.alloc_levels_slice(&[zero]);
        // Const(Char, [])
        let c_char = self.mk_const(self.export_file.name_cache.char?, empty_levels);
        // Const(Char.ofNat, [])
        let c_char_of_nat = self.mk_const(self.export_file.name_cache.char_of_nat?, empty_levels);
        // @List.nil.{0} Char
        let c_list_nil_char = {
            let f = self.mk_const(self.export_file.name_cache.list_nil?, tyzero_levels);
            self.mk_app(f, c_char)
        };
        // @List.cons.{0} Char
        let c_list_cons_char = {
            let f = self.mk_const(self.export_file.name_cache.list_cons?, tyzero_levels);
            self.mk_app(f, c_char)
        };
        let mut out = c_list_nil_char;
        for c in self.read_string(s).clone().chars().rev() {
            let bignum = self.alloc_bignum(BigUint::from(c as u32)).unwrap();
            let bignum = self.mk_nat_lit(bignum).unwrap();
            // Char.ofNat (c as u32)
            let x = self.mk_app(c_char_of_nat, bignum);
            // List.cons (Char.ofNat u32)
            let y = self.mk_app(c_list_cons_char, x);
            // (List.cons (Char.ofNat u32)) xs
            out = self.mk_app(y, out);
        }
        let string_of_list_const = self.mk_const(self.export_file.name_cache.string_of_list?, empty_levels);
        Some(self.mk_app(string_of_list_const, out))
    }

    /// If `e` is a NatLit, or `Const Nat.zero []`, return the appropriate Bignum.
    pub(crate) fn get_bignum_from_expr(&mut self, e: ExprPtr<'t>) -> Option<BigUint> {
        if let NatLit { ptr, .. } = self.read_expr(e) {
            self.read_bignum(ptr).cloned()
        } else if Some(e) == self.c_nat_zero() {
            Some(BigUint::zero())
        } else {
            None
        }
    }

    pub(crate) fn get_bignum_succ_from_expr(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if let NatLit { ptr, .. } = self.read_expr(e) {
            self.mk_nat_lit_quick(self.read_bignum(ptr)? + 1usize)
        } else if Some(e) == self.c_nat_zero() {
            self.mk_nat_lit_quick(BigUint::zero() + 1usize)
        } else {
            None
        }
    }

    /// Return the expression representing either `true` or `false`
    pub(crate) fn bool_to_expr(&mut self, b: bool) -> Option<ExprPtr<'t>> {
        if b {
            self.c_bool_true()
        } else {
            self.c_bool_false()
        }
    }

    pub(crate) fn c_bool_true(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.bool_true?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    pub(crate) fn c_bool_false(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.bool_false?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    pub(crate) fn c_nat_zero(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.nat_zero?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    pub(crate) fn c_nat_succ(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.nat_succ?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    /// Make `Const("Nat", [])`
    pub(crate) fn nat_type(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.nat?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    /// Make `Const("String", [])`
    pub(crate) fn string_type(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.string?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    /// Abstract `e` with the binders in `binders`, creating a lambda
    /// telescope while backing out.
    ///
    /// `[a, b, c], e` ~> `(fun (a b c) => e)`
    pub(crate) fn abstr_lambda_telescope(&mut self, mut binders: &[ExprPtr<'t>], mut e: ExprPtr<'t>) -> ExprPtr<'t> {
        while let [tl @ .., binder] = binders {
            e = self.apply_lambda(*binder, e);
            binders = tl;
        }
        e
    }

    /// Abstract `e` with the binders in `binders`, creating a lambda
    /// telescope while backing out.
    ///
    /// `[a, b, c], e` ~> `(Pi (a b c) => e)`
    pub(crate) fn abstr_pi_telescope(&mut self, mut binders: &[ExprPtr<'t>], mut e: ExprPtr<'t>) -> ExprPtr<'t> {
        while let [tl @ .., binder] = binders {
            e = self.abstr_pi(*binder, e);
            binders = tl;
        }
        e
    }

    pub(crate) fn find_const<F>(&self, e: ExprPtr<'t>, pred: F) -> bool
    where
        F: FnOnce(NamePtr<'t>) -> bool + Copy, {
        let mut cache = crate::util::new_fx_hash_map();
        self.find_const_aux(e, pred, &mut cache)
    }

    fn find_const_aux<F>(&self, e: ExprPtr<'t>, pred: F, cache: &mut FxHashMap<ExprPtr<'t>, bool>) -> bool
    where
        F: FnOnce(NamePtr<'t>) -> bool + Copy, {
        if let Some(cached) = cache.get(&e) {
            *cached
        } else {
            let r = match self.read_expr(e) {
                Var { .. } | Sort { .. } | NatLit { .. } | StringLit { .. } => false,
                Const { name, .. } => pred(name),
                App { fun, arg, .. } => self.find_const_aux(fun, pred, cache) || self.find_const_aux(arg, pred, cache),
                Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } =>
                    self.find_const_aux(binder_type, pred, cache) || self.find_const_aux(body, pred, cache),
                Let { binder_type, val, body, .. } =>
                    self.find_const_aux(binder_type, pred, cache)
                        || self.find_const_aux(val, pred, cache)
                        || self.find_const_aux(body, pred, cache),
                Local { binder_type, .. } => self.find_const_aux(binder_type, pred, cache),
                Proj { structure, .. } => self.find_const_aux(structure, pred, cache),
                Shift { inner, .. } => self.find_const_aux(inner, pred, cache),
            };
            cache.insert(e, r);
            r
        }
    }

    /// Return the number of leading `Pi` binders on this expression.
    pub(crate) fn pi_telescope_size(&self, mut e: ExprPtr<'t>) -> u16 {
        let mut size = 0u16;
        while let Pi { body, .. } = self.read_expr(e) {
            size += 1;
            e = body;
        }
        size
    }

    /// Is this expression `Sort(Level::Zero)`?
    pub(crate) fn prop(&mut self) -> ExprPtr<'t> { self.mk_sort(self.zero()) }

    pub fn get_nth_pi_binder(&self, mut e: ExprPtr<'t>, n: usize) -> Option<ExprPtr<'t>> {
        for _ in 0.. n {
            match self.read_expr(e) {
                Pi {body, ..} => { e = body; },
                _ => return None
            }
        }
        match self.read_expr(e) {
            Pi {binder_type, ..} => Some(binder_type),
            _ => None
        }
    }

    /// Get the name of the inductive type which is the major premise for this recursor
    /// by finding the correct binder in the recursor's type.
    pub fn get_major_induct(&mut self, rec: &crate::env::RecursorData<'t>) -> Option<NamePtr<'t>> {
        let binder = self.get_nth_pi_binder(rec.info.ty, rec.major_idx());
        match binder.map(|x| { let f = self.unfold_apps_fun(x); self.read_expr(f) }) {
            Some(Const {name, ..}) => Some(name),
            _ => None
        }
    }
    
    /// The number of "loose" bound variables, which is the number of bound variables
    /// in an expression which are boudn by something above it.
    pub(crate) fn num_loose_bvars(&self, e: ExprPtr<'t>) -> u16 { self.read_expr(e).num_loose_bvars() }

    pub(crate) fn has_fvars(&self, e: ExprPtr<'t>) -> bool { self.read_expr(e).has_fvars() }

    pub(crate) fn struct_hash(&self, e: ExprPtr<'t>) -> u64 { self.read_expr(e).get_struct_hash() }

    pub(crate) fn fvar_list_of(&self, e: ExprPtr<'t>) -> FVarList<'t> { self.read_expr(e).get_fvar_list() }

    /// Check if `b` equals `force_shift_aux(a, delta, cutoff)` without allocating.
    /// Used to verify shift-invariant cache hits.
    /// `cutoff` tracks binder depth: Var indices < cutoff are bound and should NOT be shifted.
    pub(crate) fn shift_eq(&self, a: ExprPtr<'t>, b: ExprPtr<'t>, delta: u16) -> bool {
        let result = self.shift_eq_aux(a, b, delta, 0);
        if result {
            // Verify: force_shift_aux(a, delta, 0) should equal b
            // (Can't call force_shift_aux here since we're &self, not &mut self)
        }
        result
    }

    fn shift_eq_aux(&self, a: ExprPtr<'t>, b: ExprPtr<'t>, delta: u16, cutoff: u16) -> bool {
        use crate::expr::Expr::*;
        if delta == 0 { return a == b; }
        if self.num_loose_bvars(a) <= cutoff {
            return a == b;
        }
        // Also check num_loose_bvars(b): b should have indices shifted by delta
        // If b's nlbv is unexpectedly low, something might be wrong
        if self.num_loose_bvars(b) <= cutoff {
            // b has no free vars above cutoff, but a does — they can't be shifts of each other
            return false;
        }
        match (self.read_expr(a), self.read_expr(b)) {
            (Var { dbj_idx: i, .. }, Var { dbj_idx: j, .. }) => {
                if i >= cutoff {
                    j == i + delta
                } else {
                    j == i  // bound var: not shifted
                }
            }
            (App { fun: f1, arg: a1, .. }, App { fun: f2, arg: a2, .. }) =>
                self.shift_eq_aux(f1, f2, delta, cutoff) && self.shift_eq_aux(a1, a2, delta, cutoff),
            (Pi { binder_name: n1, binder_style: s1, binder_type: t1, body: b1, .. },
             Pi { binder_name: n2, binder_style: s2, binder_type: t2, body: b2, .. }) =>
                n1 == n2 && s1 == s2 && self.shift_eq_aux(t1, t2, delta, cutoff)
                && self.shift_eq_aux(b1, b2, delta, cutoff + 1),
            (Lambda { binder_name: n1, binder_style: s1, binder_type: t1, body: b1, .. },
             Lambda { binder_name: n2, binder_style: s2, binder_type: t2, body: b2, .. }) =>
                n1 == n2 && s1 == s2 && self.shift_eq_aux(t1, t2, delta, cutoff)
                && self.shift_eq_aux(b1, b2, delta, cutoff + 1),
            (Let { binder_name: n1, binder_type: t1, val: v1, body: b1, nondep: nd1, .. },
             Let { binder_name: n2, binder_type: t2, val: v2, body: b2, nondep: nd2, .. }) =>
                n1 == n2 && nd1 == nd2 && self.shift_eq_aux(t1, t2, delta, cutoff)
                && self.shift_eq_aux(v1, v2, delta, cutoff) && self.shift_eq_aux(b1, b2, delta, cutoff + 1),
            (Proj { ty_name: tn1, idx: i1, structure: s1, .. },
             Proj { ty_name: tn2, idx: i2, structure: s2, .. }) =>
                tn1 == tn2 && i1 == i2 && self.shift_eq_aux(s1, s2, delta, cutoff),
            (Sort { level: l1, .. }, Sort { level: l2, .. }) => l1 == l2,
            (Const { name: n1, levels: l1, .. }, Const { name: n2, levels: l2, .. }) =>
                n1 == n2 && l1 == l2,
            (NatLit { ptr: p1, .. }, NatLit { ptr: p2, .. }) => p1 == p2,
            (StringLit { ptr: p1, .. }, StringLit { ptr: p2, .. }) => p1 == p2,
            (Shift { inner, amount, cutoff: 0, .. }, _) if cutoff == 0 =>
                self.shift_eq_aux(inner, b, delta + amount, 0),
            (_, Shift { inner, amount, cutoff: 0, .. }) if cutoff == 0 && amount <= delta =>
                self.shift_eq_aux(a, inner, delta - amount, 0),
            _ => false,
        }
    }
}

impl<'t> Expr<'t> {
    /// The number of "loose" bound variables, which is the number of bound variables
    /// in an expression which are boudn by something above it.
    pub(crate) fn num_loose_bvars(&self) -> u16 {
        match self {
            Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => 0,
            Var { dbj_idx, .. } => dbj_idx + 1,
            App { num_loose_bvars, .. }
            | Pi { num_loose_bvars, .. }
            | Lambda { num_loose_bvars, .. }
            | Let { num_loose_bvars, .. }
            | Proj { num_loose_bvars, .. }
            | Shift { num_loose_bvars, .. } => *num_loose_bvars,
        }
    }

    pub(crate) fn has_fvars(&self) -> bool {
        match self {
            Local { .. } => true,
            Var { .. } | Sort { .. } | Const { .. } | NatLit { .. } | StringLit { .. } => false,
            App { has_fvars, .. }
            | Pi { has_fvars, .. }
            | Lambda { has_fvars, .. }
            | Let { has_fvars, .. }
            | Proj { has_fvars, .. }
            | Shift { has_fvars, .. } => *has_fvars,
        }
    }
}

