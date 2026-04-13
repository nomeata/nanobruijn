//! Implementation of Lean expressions
use crate::util::{AppArgs, BigUintPtr, ExprPtr, FxHashMap, LevelPtr, LevelsPtr, NamePtr, StringPtr, TcCtx};
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expr<'a> {
    /// A string literal with a pointer to a utf-8 string.
    StringLit {
        hash: u64,
        fvar_lb: u16,
        ptr: StringPtr<'a>,
    },
    /// A nat literal, holds a pointer to an arbitrary precision bignum.
    NatLit {
        hash: u64,
        fvar_lb: u16,
        ptr: BigUintPtr<'a>,
    },
    Proj {
        hash: u64,
        fvar_lb: u16,
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
        fvar_lb: u16,
        dbj_idx: u16,
    },
    Sort {
        hash: u64,
        fvar_lb: u16,
        level: LevelPtr<'a>,
    },
    Const {
        hash: u64,
        fvar_lb: u16,
        name: NamePtr<'a>,
        levels: LevelsPtr<'a>,
    },
    App {
        hash: u64,
        fvar_lb: u16,
        fun: ExprPtr<'a>,
        arg: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Pi {
        hash: u64,
        fvar_lb: u16,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        body: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Lambda {
        hash: u64,
        fvar_lb: u16,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        body: ExprPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Let {
        hash: u64,
        fvar_lb: u16,
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
        fvar_lb: u16,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        id: FVarId,
    },
    /// Delayed shift: all free Var indices in `inner` are shifted up by `amount`.
    /// Always cutoff=0. `amount > 0` and `inner.fvar_lb == 0` (OSNF invariant).
    /// Nested shifts are impossible (inner can't be Shift since inner.fvar_lb == 0).
    Shift {
        hash: u64,
        fvar_lb: u16,
        inner: ExprPtr<'a>,
        amount: u16,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
}

/// Free variable identifiers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FVarId {
    /// De Bruijn level — used by nanoda's locally-nameless approach.
    DbjLevel(u16),
    /// Unique ID from monotonically increasing counter.
    Unique(u32),
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

    pub(crate) fn get_fvar_lb(&self) -> u16 {
        match self {
            Var { fvar_lb, .. }
            | Sort { fvar_lb, .. }
            | Const { fvar_lb, .. }
            | App { fvar_lb, .. }
            | Pi { fvar_lb, .. }
            | Lambda { fvar_lb, .. }
            | Let { fvar_lb, .. }
            | Local { fvar_lb, .. }
            | StringLit { fvar_lb, .. }
            | NatLit { fvar_lb, .. }
            | Proj { fvar_lb, .. }
            | Shift { fvar_lb, .. } => *fvar_lb,
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
        self.trace.inst_calls += 1;
        if substs.is_empty() {
            return e
        }
        self.expr_cache.inst_cache_gen = self.expr_cache.inst_cache_gen.wrapping_add(1);
        self.inst_aux(e, substs, 0, false, 0, 0)
    }

    /// Like `inst`, but also shifts down Var indices beyond the substitution range.
    /// Used for beta reduction and let-substitution where binders are being removed.
    pub fn inst_beta(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>]) -> ExprPtr<'t> {
        self.trace.inst_calls += 1;
        if substs.is_empty() {
            return e
        }
        self.expr_cache.inst_cache_gen = self.expr_cache.inst_cache_gen.wrapping_add(1);
        self.inst_aux(e, substs, 0, true, 0, 0)
    }

    /// Combined shift+instantiation in one pass.
    /// `sh_amt`/`sh_cut` represent a pending outer Shift that is applied to `e` before
    /// instantiation, without creating intermediate Shift wrapper expressions.
    fn inst_aux(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>], offset: u16, shift_down: bool, sh_amt: i16, sh_cut: u16) -> ExprPtr<'t> {
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.inst_aux_body(e, substs, offset, shift_down, sh_amt, sh_cut))
    }

    fn inst_aux_body(&mut self, e: ExprPtr<'t>, substs: &[ExprPtr<'t>], offset: u16, shift_down: bool, sh_amt: i16, sh_cut: u16) -> ExprPtr<'t> {
        self.trace.inst_aux_calls += 1;
        if sh_amt != 0 { self.trace.inst_aux_shifted_path += 1; }
        self.check_heartbeat();

        // Early exit: check if the (possibly shifted) expression has no loose bvars
        // beyond offset. For shift(sh_amt, sh_cut) applied to e:
        //   effective_nlbv = nlbv(e) if nlbv(e) <= sh_cut, else nlbv(e) + sh_amt
        let nlbv = self.num_loose_bvars(e);
        if sh_amt == 0 {
            if nlbv <= offset {
                self.trace.inst_aux_elided += 1;
                return e;
            }
        } else {
            let effective_nlbv = if nlbv <= sh_cut { nlbv as i16 } else { nlbv as i16 + sh_amt };
            if effective_nlbv <= offset as i16 {
                self.trace.inst_aux_elided += 1;
                // No loose bvars beyond offset after shift — but we still need the shifted form.
                // If nlbv <= sh_cut, shift is a no-op on this expr:
                if nlbv <= sh_cut {
                    return e;
                }
                // Otherwise the shifted form has bvars but all <= offset, return shifted expr
                if sh_cut == 0 {
                    return self.mk_shift(e, sh_amt as u16);
                } else {
                    return self.shift_expr(e, sh_amt as u16, sh_cut);
                }
            }
        }

        let params = (offset as u64) | ((sh_amt as u16 as u64) << 16) | ((sh_cut as u64) << 32);
        let cache_tag = e.get_hash().wrapping_mul(0x517cc1b727220a95) ^ params;
        let gen = self.expr_cache.inst_cache_gen;
        // Lazily allocate the DM cache
        if self.expr_cache.inst_cache.is_empty() {
            let dummy: ExprPtr<'t> = crate::util::Ptr::from(crate::util::DagMarker::ExportFile, 0);
            self.expr_cache.inst_cache.resize(crate::util::INST_CACHE_SIZE, (0, 0, dummy, dummy));
        }
        let slot = (cache_tag as usize) & (crate::util::INST_CACHE_SIZE - 1);
        let (g, p, ke, result) = self.expr_cache.inst_cache[slot];
        if g == gen && p == params && ke == e {
            self.trace.inst_aux_cache_hits += 1;
            return result;
        }

        let n_substs = substs.len() as u16;

        // Key optimization: when the shift pushes all vars past the substitution range,
        // no variable will be substituted. We can return the shift-adjusted result in O(1)
        // instead of traversing the entire subtree.
        //
        // Condition: sh_cut <= offset (unshifted vars can't reach substitution range)
        //        AND sh_amt + sh_cut >= offset + n_substs (shifted vars are past substitution)
        // This implies sh_amt >= n_substs (shift never goes negative with shift_down).
        // When the shift exactly cancels shift_down (sh_amt == n_substs, sh_cut == offset),
        // no variable gets substituted and the result is just `e` — O(1) with no new allocations.
        if sh_amt > 0 && shift_down && sh_amt == n_substs as i16 && sh_cut == offset {
            self.trace.inst_aux_shift_skip_clean += 1;
            self.trace.inst_aux_elided += 1;
            self.expr_cache.inst_cache[slot] = (gen, params, e,e);
            return e;
        }
        // More general case: shift pushes vars past substitution range but sh_amt > n_substs
        // or !shift_down. Creates a Shift wrapper — saves inst_aux traversal at the cost of
        // potentially increasing downstream TC work from Shift wrappers.
        if sh_amt > 0 && sh_cut <= offset && sh_amt as u16 + sh_cut >= offset + n_substs {
            let r = if shift_down {
                let new_amt = sh_amt - n_substs as i16;
                debug_assert!(new_amt > 0);
                self.trace.inst_aux_shift_skip_wrap += 1;
                if sh_cut == 0 {
                    self.mk_shift(e, new_amt as u16)
                } else {
                    self.shift_expr(e, new_amt as u16, sh_cut)
                }
            } else {
                self.trace.inst_aux_shift_skip_wrap += 1;
                if sh_cut == 0 {
                    self.mk_shift(e, sh_amt as u16)
                } else {
                    self.shift_expr(e, sh_amt as u16, sh_cut)
                }
            };
            self.trace.inst_aux_elided += 1;
            self.expr_cache.inst_cache[slot] = (gen, params, e,r);
            return r;
        }

        // Shift-down-only optimization: when all free bvars are past the substitution
        // range, no substitution occurs — only shift_down. Use persistently-cached
        // push_shift_down_cutoff to avoid re-traversing shared subtrees across inst_beta calls.
        // Only for sh_amt == 0 path; the sh_amt > 0 case has complex shift composition.
        // Guard: nlbv > offset + n_substs is a necessary condition (free since nlbv already computed).
        if shift_down && sh_amt == 0 && n_substs >= 4 && nlbv > offset + n_substs {
            let lb = self.read_expr(e).get_fvar_lb();
            if lb >= offset + n_substs {
                let r = self.push_shift_down_cutoff(e, n_substs, offset);
                self.expr_cache.inst_cache[slot] = (gen, params, e,r);
                return r;
            }
        }

        // If there's a pending shift, we need to look through Shift nodes on e as well
        let calcd = if sh_amt > 0 {
            match self.read_expr(e) {
                Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => {
                    // Closed expression, shift is no-op
                    return e;
                }
                Shift { inner, amount, .. } => {
                    self.trace.inst_aux_shift_nodes += 1;
                    // OSNF: Shift always has cutoff=0.
                    if sh_cut == 0 {
                        // Compose: Shift(inner, n) with pending (sh_amt, 0) = (sh_amt + n, 0)
                        let r = self.inst_aux(inner, substs, offset, shift_down, sh_amt + amount as i16, 0);
                        self.expr_cache.inst_cache[slot] = (gen, params, e,r);
                        return r;
                    }
                    // sh_cut > 0: cutoffs don't match. Force via push_shift, then recurse.
                    if amount as i16 >= sh_cut as i16 {
                        // All vars >= 0 become >= amount >= sh_cut, compose uniformly
                        self.trace.inst_aux_shift_compose += 1;
                        let r = self.inst_aux(inner, substs, offset, shift_down, sh_amt + amount as i16, 0);
                        self.expr_cache.inst_cache[slot] = (gen, params, e,r);
                        return r;
                    }
                    self.trace.inst_aux_shift_mismatch += 1;
                    let forced = self.push_shift_up(inner, amount);
                    let r = self.inst_aux(forced, substs, offset, shift_down, sh_amt, sh_cut);
                    self.expr_cache.inst_cache[slot] = (gen, params, e,r);
                    return r;
                }
                Var { dbj_idx, .. } => {
                    // Apply pending shift first
                    let shifted_idx = if dbj_idx >= sh_cut { (dbj_idx as i16 + sh_amt) as u16 } else { dbj_idx };
                    if shifted_idx < offset {
                        self.mk_var(shifted_idx)
                    } else {
                        let rel_idx = shifted_idx - offset;
                        if rel_idx < n_substs {
                            self.trace.inst_aux_shifted_var_subst += 1;
                            let val = substs[substs.len() - 1 - rel_idx as usize];
                            if offset > 0 { self.mk_shift(val, offset) } else { val }
                        } else {
                            self.trace.inst_aux_shifted_var_nosubst += 1;
                            if shift_down {
                                self.mk_var(shifted_idx - n_substs)
                            } else {
                                // Return the shifted var directly
                                if sh_cut == 0 {
                                    self.mk_shift(e, sh_amt as u16)
                                } else {
                                    self.shift_expr(e, sh_amt as u16, sh_cut)
                                }
                            }
                        }
                    }
                }
                App { fun, arg, .. } => {
                    let new_fun = self.inst_aux(fun, substs, offset, shift_down, sh_amt, sh_cut);
                    let new_arg = self.inst_aux(arg, substs, offset, shift_down, sh_amt, sh_cut);
                    if new_fun == fun && new_arg == arg { self.trace.inst_aux_shifted_identity += 1; e } else { self.trace.inst_aux_shifted_alloc += 1; self.mk_app(new_fun, new_arg) }
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let new_type = self.inst_aux(binder_type, substs, offset, shift_down, sh_amt, sh_cut);
                    let new_body = self.inst_aux(body, substs, offset + 1, shift_down, sh_amt, sh_cut + 1);
                    if new_type == binder_type && new_body == body { self.trace.inst_aux_shifted_identity += 1; e } else { self.trace.inst_aux_shifted_alloc += 1; self.mk_pi(binder_name, binder_style, new_type, new_body) }
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let new_type = self.inst_aux(binder_type, substs, offset, shift_down, sh_amt, sh_cut);
                    let new_body = self.inst_aux(body, substs, offset + 1, shift_down, sh_amt, sh_cut + 1);
                    if new_type == binder_type && new_body == body { self.trace.inst_aux_shifted_identity += 1; e } else { self.trace.inst_aux_shifted_alloc += 1; self.mk_lambda(binder_name, binder_style, new_type, new_body) }
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let new_type = self.inst_aux(binder_type, substs, offset, shift_down, sh_amt, sh_cut);
                    let new_val = self.inst_aux(val, substs, offset, shift_down, sh_amt, sh_cut);
                    let new_body = self.inst_aux(body, substs, offset + 1, shift_down, sh_amt, sh_cut + 1);
                    if new_type == binder_type && new_val == val && new_body == body { self.trace.inst_aux_shifted_identity += 1; e } else { self.trace.inst_aux_shifted_alloc += 1; self.mk_let(binder_name, new_type, new_val, new_body, nondep) }
                }
                Proj { ty_name, idx, structure, .. } => {
                    let new_structure = self.inst_aux(structure, substs, offset, shift_down, sh_amt, sh_cut);
                    if new_structure == structure { self.trace.inst_aux_shifted_identity += 1; e } else { self.trace.inst_aux_shifted_alloc += 1; self.mk_proj(ty_name, idx, new_structure) }
                }
            }
        } else {
            // No pending shift — original inst_aux logic
            match self.read_expr(e) {
                Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => panic!(),
                Shift { inner, amount, .. } => {
                    self.trace.inst_aux_shift_nodes += 1;
                    // OSNF: Shift always has cutoff=0. Carry as parameters.
                    let r = self.inst_aux(inner, substs, offset, shift_down, amount as i16, 0);
                    self.expr_cache.inst_cache[slot] = (gen, params, e,r);
                    return r;
                }
                Var { dbj_idx, .. } => {
                    debug_assert!(dbj_idx >= offset);
                    let rel_idx = dbj_idx - offset;
                    if rel_idx < n_substs {
                        let val = substs[substs.len() - 1 - rel_idx as usize];
                        if offset > 0 {
                            self.mk_shift(val, offset)
                        } else {
                            val
                        }
                    } else if shift_down {
                        self.mk_var(dbj_idx - n_substs)
                    } else {
                        e
                    }
                }
                App { fun, arg, .. } => {
                    let new_fun = self.inst_aux(fun, substs, offset, shift_down, 0, 0);
                    let new_arg = self.inst_aux(arg, substs, offset, shift_down, 0, 0);
                    if new_fun == fun && new_arg == arg { self.trace.inst_aux_nonshift_identity += 1; e } else { self.mk_app(new_fun, new_arg) }
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let new_type = self.inst_aux(binder_type, substs, offset, shift_down, 0, 0);
                    let new_body = self.inst_aux(body, substs, offset + 1, shift_down, 0, 0);
                    if new_type == binder_type && new_body == body { self.trace.inst_aux_nonshift_identity += 1; e } else { self.mk_pi(binder_name, binder_style, new_type, new_body) }
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let new_type = self.inst_aux(binder_type, substs, offset, shift_down, 0, 0);
                    let new_body = self.inst_aux(body, substs, offset + 1, shift_down, 0, 0);
                    if new_type == binder_type && new_body == body { self.trace.inst_aux_nonshift_identity += 1; e } else { self.mk_lambda(binder_name, binder_style, new_type, new_body) }
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let new_type = self.inst_aux(binder_type, substs, offset, shift_down, 0, 0);
                    let new_val = self.inst_aux(val, substs, offset, shift_down, 0, 0);
                    let new_body = self.inst_aux(body, substs, offset + 1, shift_down, 0, 0);
                    if new_type == binder_type && new_val == val && new_body == body { self.trace.inst_aux_nonshift_identity += 1; e } else { self.mk_let(binder_name, new_type, new_val, new_body, nondep) }
                }
                Proj { ty_name, idx, structure, .. } => {
                    let new_structure = self.inst_aux(structure, substs, offset, shift_down, 0, 0);
                    if new_structure == structure { self.trace.inst_aux_nonshift_identity += 1; e } else { self.mk_proj(ty_name, idx, new_structure) }
                }
            }
        };
        self.expr_cache.inst_cache[slot] = (gen, params, e,calcd);
        calcd
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
        // If all free bvars are already >= cutoff, the cutoff is irrelevant —
        // this is a uniform shift, so use O(1) mk_shift instead of traversing.
        if self.read_expr(e).get_fvar_lb() >= cutoff {
            return self.mk_shift(e, amount);
        }
        if let Some(&cached) = self.expr_cache.shift_cache.get(&(e, amount, cutoff)) {
            return cached;
        }
        let calcd = match self.view_expr(e) {
            Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => panic!(),
            Shift { .. } => unreachable!("view_expr never returns Shift"),
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
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.abstr_aux_body(e, locals, offset))
    }

    fn abstr_aux_body(&mut self, e: ExprPtr<'t>, locals: &[ExprPtr<'t>], offset: u16) -> ExprPtr<'t> {
        if !self.has_fvars(e) {
            e
        } else if let Some(cached) = self.expr_cache.abstr_cache.get(&(e, offset)) {
            *cached
        } else {
            // Use view_expr to see through Shift nodes transparently.
            // This avoids an infinite loop where push_shift_up(core, n) can produce
            // Shift(n, core) — a fixpoint — causing unbounded recursion.
            let calcd = match self.view_expr(e) {
                Local { .. } => {
                    // Under OSNF, Locals never appear under Shift (nlbv=0),
                    // so `e` is the Local pointer itself.
                    locals.iter().rev().position(|x| *x == e).map(|pos| self.mk_var(u16::try_from(pos).unwrap() + offset)).unwrap_or(e)
                }
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
                Shift { .. } => unreachable!("view_expr never returns Shift"),
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

    /// Abstraction by deBruijn level: converts DbjLevel locals back to Var.
    /// Used by nanoda's locally-nameless TC.
    fn abstr_aux_levels(&mut self, e: ExprPtr<'t>, start_pos: u16, num_open_binders: u16) -> ExprPtr<'t> {
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.abstr_aux_levels_body(e, start_pos, num_open_binders))
    }

    fn abstr_aux_levels_body(&mut self, e: ExprPtr<'t>, start_pos: u16, num_open_binders: u16) -> ExprPtr<'t> {
        if !self.has_fvars(e) {
            e
        } else if let Some(cached) = self.expr_cache.abstr_cache_levels.get(&(e, start_pos, num_open_binders)) {
            *cached
        } else {
            // Use view_expr to see through Shift nodes transparently (same fix as abstr_aux_body).
            let calcd = match self.view_expr(e) {
                Local { id: FVarId::DbjLevel(serial), .. } =>
                    if serial < start_pos {
                        e
                    } else {
                        self.fvar_to_bvar(num_open_binders, serial)
                    },
                Local { id: FVarId::Unique(..), .. } => e,
                App { fun, arg, .. } => {
                    let fun = self.abstr_aux_levels(fun, start_pos, num_open_binders);
                    let arg = self.abstr_aux_levels(arg, start_pos, num_open_binders);
                    self.mk_app(fun, arg)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.abstr_aux_levels(binder_type, start_pos, num_open_binders);
                    let body = self.abstr_aux_levels(body, start_pos, num_open_binders + 1);
                    self.mk_pi(binder_name, binder_style, binder_type, body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let binder_type = self.abstr_aux_levels(binder_type, start_pos, num_open_binders);
                    let body = self.abstr_aux_levels(body, start_pos, num_open_binders + 1);
                    self.mk_lambda(binder_name, binder_style, binder_type, body)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let binder_type = self.abstr_aux_levels(binder_type, start_pos, num_open_binders);
                    let val = self.abstr_aux_levels(val, start_pos, num_open_binders);
                    let body = self.abstr_aux_levels(body, start_pos, num_open_binders + 1);
                    self.mk_let(binder_name, binder_type, val, body, nondep)
                }
                StringLit { .. } | NatLit { .. } => panic!(),
                Proj { ty_name, idx, structure, .. } => {
                    let structure = self.abstr_aux_levels(structure, start_pos, num_open_binders);
                    self.mk_proj(ty_name, idx, structure)
                }
                Shift { .. } => unreachable!("view_expr never returns Shift"),
                Var { .. } | Sort { .. } | Const { .. } => panic!("should flag as no locals"),
            };
            self.expr_cache.abstr_cache_levels.insert((e, start_pos, num_open_binders), calcd);
            calcd
        }
    }

    /// Abstract deBruijn-level free variables back to bound variables.
    /// Used by nanoda's locally-nameless TC.
    pub fn abstr_levels(&mut self, e: ExprPtr<'t>, start_pos: u16) -> ExprPtr<'t> {
        self.expr_cache.abstr_cache_levels.clear();
        self.abstr_aux_levels(e, start_pos, self.dbj_level_counter)
    }

    fn subst_aux(&mut self, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> ExprPtr<'t> {
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.subst_aux_body(e, ks, vs))
    }

    fn subst_aux_body(&mut self, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> ExprPtr<'t> {
        if let Some(cached) = self.expr_cache.subst_cache.get(&(e, ks, vs)) {
            *cached
        } else {
            // Handle Shift directly: level substitution commutes with variable shifting
            // because they operate on independent parts (levels vs. bvar indices).
            // subst(Shift(e, k, c)) = Shift(subst(e), k, c)
            // This avoids expanding Shift via view_expr which creates new pointers
            // that miss the subst_cache, causing quadratic re-traversal.
            let r = match self.read_expr(e) {
                Shift { inner, amount, .. } => {
                    let inner_subst = self.subst_aux(inner, ks, vs);
                    if inner_subst == inner { e } else { self.mk_shift(inner_subst, amount) }
                }
                _ => match self.view_expr(e) {
                    Var { .. } | NatLit { .. } | StringLit { .. } => e,
                    Sort { level, .. } => {
                        let new_level = self.subst_level(level, ks, vs);
                        if new_level == level { e } else { self.mk_sort(new_level) }
                    }
                    Const { name, levels, .. } => {
                        let new_levels = self.subst_levels(levels, ks, vs);
                        if new_levels == levels { e } else { self.mk_const(name, new_levels) }
                    }
                    App { fun, arg, .. } => {
                        let new_fun = self.subst_aux(fun, ks, vs);
                        let new_arg = self.subst_aux(arg, ks, vs);
                        if new_fun == fun && new_arg == arg { e } else { self.mk_app(new_fun, new_arg) }
                    }
                    Pi { binder_name, binder_style, binder_type, body, .. } => {
                        let new_type = self.subst_aux(binder_type, ks, vs);
                        let new_body = self.subst_aux(body, ks, vs);
                        if new_type == binder_type && new_body == body { e } else { self.mk_pi(binder_name, binder_style, new_type, new_body) }
                    }
                    Lambda { binder_name, binder_style, binder_type, body, .. } => {
                        let new_type = self.subst_aux(binder_type, ks, vs);
                        let new_body = self.subst_aux(body, ks, vs);
                        if new_type == binder_type && new_body == body { e } else { self.mk_lambda(binder_name, binder_style, new_type, new_body) }
                    }
                    Let { binder_name, binder_type, val, body, nondep, .. } => {
                        let new_type = self.subst_aux(binder_type, ks, vs);
                        let new_val = self.subst_aux(val, ks, vs);
                        let new_body = self.subst_aux(body, ks, vs);
                        if new_type == binder_type && new_val == val && new_body == body { e } else { self.mk_let(binder_name, new_type, new_val, new_body, nondep) }
                    }
                    Local { .. } => panic!("level substitution should not find locals"),
                    Shift { .. } => unreachable!("view_expr never returns Shift"),
                    Proj { ty_name, idx, structure, .. } => {
                        let new_structure = self.subst_aux(structure, ks, vs);
                        if new_structure == structure { e } else { self.mk_proj(ty_name, idx, new_structure) }
                    }
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
    /// The returned head has any top-level Shift pushed one level inside.
    pub fn unfold_apps_fun(&mut self, mut e: ExprPtr<'t>) -> ExprPtr<'t> {
        loop {
            match self.view_expr(e) {
                App { fun, .. } => e = fun,
                _ => {
                    if let Expr::Shift { inner, amount, .. } = self.read_expr(e) {
                        return self.push_shift_up(inner, amount);
                    }
                    return e;
                }
            }
        }
    }

    /// From `f a_0 .. a_N`, return `(f, [a_0, ..a_N], shifted)`
    /// Accumulates Shift through the App spine; returns lazy (Shift-wrapped) args and fun.
    /// `shifted` is true if any Shift nodes were encountered (args/fun may differ from original).
    pub fn unfold_apps(&mut self, mut e: ExprPtr<'t>) -> (ExprPtr<'t>, AppArgs<'t>, bool) {
        let mut args = AppArgs::new();
        let mut pending_shift: u16 = 0;
        let mut shifted = false;
        loop {
            match self.read_expr(e) {
                Shift { inner, amount, .. } => {
                    pending_shift += amount;
                    shifted = true;
                    e = inner;
                }
                App { fun, arg, .. } => {
                    e = fun;
                    let arg = if pending_shift != 0 {
                        self.mk_shift(arg, pending_shift)
                    } else {
                        arg
                    };
                    args.push(arg);
                },
                _ => {
                    if pending_shift != 0 {
                        e = self.mk_shift(e, pending_shift);
                    }
                    break;
                }
            }
        }
        args.reverse();
        (e, args, shifted)
    }

    /// If this is a const application, return (Const {..}, name, levels, args)
    pub fn unfold_const_apps(
        &mut self,
        e: ExprPtr<'t>,
    ) -> Option<(ExprPtr<'t>, NamePtr<'t>, LevelsPtr<'t>, AppArgs<'t>)> {
        let (f, args, _) = self.unfold_apps(e);
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

    pub(crate) fn unfold_apps_stack(&mut self, mut e: ExprPtr<'t>) -> (ExprPtr<'t>, AppArgs<'t>) {
        let mut args = AppArgs::new();
        loop {
            match self.view_expr(e) {
                App { fun, arg, .. } => {
                    args.push(arg);
                    e = fun;
                }
                _ => {
                    if let Expr::Shift { inner, amount, .. } = self.read_expr(e) {
                        e = self.push_shift_up(inner, amount);
                    }
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
        if let NatLit { ptr, .. } = self.view_expr(e) {
            self.read_bignum(ptr).cloned()
        } else if Some(e) == self.c_nat_zero() {
            Some(BigUint::zero())
        } else {
            None
        }
    }

    pub(crate) fn get_bignum_succ_from_expr(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if let NatLit { ptr, .. } = self.view_expr(e) {
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
    pub(crate) fn pi_telescope_size(&mut self, mut e: ExprPtr<'t>) -> u16 {
        let mut size = 0u16;
        while let Pi { body, .. } = self.view_expr(e) {
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
    /// Fast num_loose_bvars lookup via parallel Vec (avoids reading the full 48-byte Expr).
    #[inline(always)]
    pub(crate) fn num_loose_bvars(&self, e: ExprPtr<'t>) -> u16 {
        match e.dag_marker() {
            crate::util::DagMarker::ExportFile => self.export_file.dag.expr_nlbv[e.idx()],
            crate::util::DagMarker::TcCtx => self.dag.expr_nlbv[e.idx()],
        }
    }

    pub(crate) fn has_fvars(&self, e: ExprPtr<'t>) -> bool { self.read_expr(e).has_fvars() }

    pub(crate) fn fvar_lb(&self, e: ExprPtr<'t>) -> u16 {
        self.read_expr(e).get_fvar_lb()
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


