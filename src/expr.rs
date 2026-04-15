//! Implementation of Lean expressions
use crate::util::{AppArgs, BigUintPtr, ExprPtr, FxHashMap, LevelPtr, LevelsPtr, NamePtr, SPtr, StringPtr, TcCtx};
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Expr<'a> {
    /// A string literal with a pointer to a utf-8 string.
    StringLit {
        hash: u64,
        ptr: StringPtr<'a>,
    },
    /// A nat literal, holds a pointer to an arbitrary precision bignum.
    NatLit {
        hash: u64,
        ptr: BigUintPtr<'a>,
    },
    Proj {
        hash: u64,
        /// The name of the structure being projected. E.g. `Prod` if this is
        /// projection 0 of `Prod.mk ..`
        ty_name: NamePtr<'a>,
        /// The 0-based position of the constructor argument, not considering the
        /// parameters. For some struct Foo A B, and a constructor Foo.mk A B p q r s,
        /// `q` will have idx 1.
        idx: u32,
        structure: SPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    /// A bound variable represented by a deBruijn index.
    /// In the DAG, only Var { dbj_idx: 0 } exists. All variable references
    /// are SPtr(var0_ptr, k) where k is the de Bruijn index.
    Var {
        hash: u64,
        dbj_idx: u16,
    },
    Sort {
        hash: u64,
        level: LevelPtr<'a>,
    },
    Const {
        hash: u64,
        name: NamePtr<'a>,
        levels: LevelsPtr<'a>,
    },
    App {
        hash: u64,
        fun: SPtr<'a>,
        arg: SPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Pi {
        hash: u64,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: SPtr<'a>,
        body: SPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Lambda {
        hash: u64,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: SPtr<'a>,
        body: SPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
    },
    Let {
        hash: u64,
        binder_name: NamePtr<'a>,
        binder_type: SPtr<'a>,
        val: SPtr<'a>,
        body: SPtr<'a>,
        num_loose_bvars: u16,
        has_fvars: bool,
        nondep: bool
    },
    /// A free variable with binder information and a unique identifier.
    Local {
        hash: u64,
        binder_name: NamePtr<'a>,
        binder_style: BinderStyle,
        binder_type: ExprPtr<'a>,
        id: FVarId,
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
            | Proj { hash, .. } => *hash,
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
    pub(crate) fn inst_forall_params(&mut self, mut e: SPtr<'t>, n: usize, all_args: &[SPtr<'t>]) -> SPtr<'t> {
        for _ in 0..n {
            match self.read_expr(e.core) {
                Pi { body, .. } => {
                    if e.shift == 0 {
                        e = body;
                    } else if body.shift >= 1 {
                        // body.shift >= 1 means all vars in body.core are >= 1,
                        // so cutoff=1 is irrelevant — uniform shift composition
                        e = self.sptr_shift(body, e.shift);
                    } else {
                        // body.shift == 0 and e.shift > 0: need cutoff=1
                        e = self.shift_expr(body.core, e.shift, 1);
                    }
                }
                _ => panic!()
            }
        }
        self.inst_beta(e, &all_args[0..n])
    }

    /// Instantiate `e` with the substitutions in `substs`.
    /// Replaces Var(offset + i) with substs[rev(i)] for i < substs.len().
    /// Vars beyond the substitution range are left unchanged (no shifting).
    /// Used for local-to-local replacement (e.g. replace_params, inductive.rs).
    pub fn inst(&mut self, e: SPtr<'t>, substs: &[SPtr<'t>]) -> SPtr<'t> {
        self.trace.inst_calls += 1;
        if substs.is_empty() {
            return e
        }
        // SPtr fast path: if e.shift >= n_substs, no substituted variable appears.
        if e.shift >= substs.len() as u16 {
            return e;
        }
        self.expr_cache.inst_substs_id = self.expr_cache.inst_substs_id.wrapping_add(1);
        self.inst_aux(e.core, substs, 0, false, e.shift as i16, 0)
    }

    /// Like `inst`, but also shifts down Var indices beyond the substitution range.
    /// Used for beta reduction and let-substitution where binders are being removed.
    pub fn inst_beta(&mut self, e: SPtr<'t>, substs: &[SPtr<'t>]) -> SPtr<'t> {
        self.trace.inst_calls += 1;
        if substs.is_empty() {
            return e
        }
        // SPtr fast path: if e.shift >= n_substs, all substituted variables are dead.
        // With SPtr, the shift can be adjusted arithmetically.
        let n_substs = substs.len() as u16;
        if e.shift >= n_substs {
            return SPtr::new(e.core, e.shift - n_substs);
        }
        self.expr_cache.inst_substs_id = self.expr_cache.inst_substs_id.wrapping_add(1);
        self.inst_aux(e.core, substs, 0, true, e.shift as i16, 0)
    }

    /// Combined shift+instantiation in one pass.
    /// `sh_amt`/`sh_cut` represent a pending outer Shift that is applied to `e` before
    /// instantiation, without creating intermediate Shift wrapper expressions.
    /// With SPtr children, the child's shift composes with the pending (sh_amt, sh_cut).
    fn inst_aux(&mut self, e: ExprPtr<'t>, substs: &[SPtr<'t>], offset: u16, shift_down: bool, sh_amt: i16, sh_cut: u16) -> SPtr<'t> {
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.inst_aux_body(e, substs, offset, shift_down, sh_amt, sh_cut))
    }

    /// Inlined fast path for inst_aux on SPtr children.
    /// Composes the child's SPtr shift (cutoff=0) with the pending (sh_amt, sh_cut).
    #[inline(always)]
    fn inst_aux_quick_sptr(&mut self, child: SPtr<'t>, substs: &[SPtr<'t>], offset: u16, shift_down: bool, sh_amt: i16, sh_cut: u16) -> SPtr<'t> {
        if child.shift == 0 {
            return self.inst_aux_quick(child.core, substs, offset, shift_down, sh_amt, sh_cut);
        }
        // If child's core is closed, substitution doesn't affect it.
        // Return child unchanged — preserving its shift for OSNF consistency.
        // (In the old code, Shift(closed, k) had nlbv=k and wouldn't be dropped.)
        if self.num_loose_bvars(child.core) == 0 {
            return child;
        }
        if sh_cut == 0 || child.shift >= sh_cut {
            let new_sh_amt = sh_amt + child.shift as i16;
            return self.inst_aux_quick(child.core, substs, offset, shift_down, new_sh_amt, 0);
        }
        // Mismatch: 0 < child.shift < sh_cut. Can't compose into a single (sh_amt, sh_cut).
        // Materialize the child's view, then process each child of the viewed expression.
        // For now, use a simpler approach: view the SPtr and recurse.
        let viewed = self.view_sptr(child);
        // Process the viewed expression (which has adjusted SPtr children)
        // We need to process it as if it were at the current (sh_amt, sh_cut) level.
        // The viewed expression is a temporary Expr, not in the DAG. We need to process its children.
        match viewed {
            Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => {
                SPtr::unshifted(child.core) // closed, shift irrelevant
            }
            Var { dbj_idx, .. } => {
                // The viewed var already has the correct index (child.shift applied)
                // Now apply pending (sh_amt, sh_cut)
                let shifted_idx = if sh_amt != 0 && dbj_idx >= sh_cut { (dbj_idx as i16 + sh_amt) as u16 } else { dbj_idx };
                let n_substs = substs.len() as u16;
                if shifted_idx < offset {
                    self.mk_var(shifted_idx)
                } else {
                    let rel_idx = shifted_idx - offset;
                    if rel_idx < n_substs {
                        let val = substs[substs.len() - 1 - rel_idx as usize];
                        self.sptr_shift(val, offset)
                    } else if shift_down {
                        self.mk_var(shifted_idx - n_substs)
                    } else {
                        self.mk_var(shifted_idx)
                    }
                }
            }
            App { fun, arg, .. } => {
                let new_fun = self.inst_aux_quick_sptr(fun, substs, offset, shift_down, sh_amt, sh_cut);
                let new_arg = self.inst_aux_quick_sptr(arg, substs, offset, shift_down, sh_amt, sh_cut);
                self.mk_app(new_fun, new_arg)
            }
            Pi { binder_name, binder_style, binder_type, body, .. } => {
                let new_type = self.inst_aux_quick_sptr(binder_type, substs, offset, shift_down, sh_amt, sh_cut);
                let new_body = self.inst_aux_quick_sptr(body, substs, offset + 1, shift_down, sh_amt, sh_cut + 1);
                self.mk_pi(binder_name, binder_style, new_type, new_body)
            }
            Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let new_type = self.inst_aux_quick_sptr(binder_type, substs, offset, shift_down, sh_amt, sh_cut);
                let new_body = self.inst_aux_quick_sptr(body, substs, offset + 1, shift_down, sh_amt, sh_cut + 1);
                self.mk_lambda(binder_name, binder_style, new_type, new_body)
            }
            Let { binder_name, binder_type, val, body, nondep, .. } => {
                let new_type = self.inst_aux_quick_sptr(binder_type, substs, offset, shift_down, sh_amt, sh_cut);
                let new_val = self.inst_aux_quick_sptr(val, substs, offset, shift_down, sh_amt, sh_cut);
                let new_body = self.inst_aux_quick_sptr(body, substs, offset + 1, shift_down, sh_amt, sh_cut + 1);
                self.mk_let(binder_name, new_type, new_val, new_body, nondep)
            }
            Proj { ty_name, idx, structure, .. } => {
                let new_structure = self.inst_aux_quick_sptr(structure, substs, offset, shift_down, sh_amt, sh_cut);
                self.mk_proj(ty_name, idx, new_structure)
            }
        }
    }

    /// Inlined fast path for inst_aux on children: avoids function call + stacker overhead
    /// for the common early-exit cases (closed expressions, nlbv below offset).
    #[inline(always)]
    fn inst_aux_quick(&mut self, e: ExprPtr<'t>, substs: &[SPtr<'t>], offset: u16, shift_down: bool, sh_amt: i16, sh_cut: u16) -> SPtr<'t> {
        let nlbv = self.num_loose_bvars(e);
        let n_substs = substs.len() as u16;
        if sh_amt == 0 {
            if nlbv <= offset { return SPtr::unshifted(e); }
            // OSNF dead-substitution: if all free vars are past the substitution range,
            // no variable gets substituted.
            let fvar_lb = self.fvar_lb(e);
            if fvar_lb >= offset + n_substs {
                if shift_down {
                    // TODO: push_shift_down_cutoff should return SPtr once util.rs is updated
                    let r = self.push_shift_down_cutoff(e, n_substs, offset);
                    return SPtr::unshifted(r);
                } else {
                    return SPtr::unshifted(e);
                }
            }
        } else {
            if nlbv == 0 { return SPtr::unshifted(e); }
            let effective_nlbv = if nlbv <= sh_cut { nlbv as i16 } else { nlbv as i16 + sh_amt };
            if effective_nlbv <= offset as i16 {
                if nlbv <= sh_cut { return SPtr::unshifted(e); }
                if sh_cut == 0 { return self.mk_shift(e, sh_amt as u16); }
                return self.shift_expr(e, sh_amt as u16, sh_cut);
            }
            // OSNF dead-substitution for shifted case: if fvar_lb > sh_cut (shift applies to lowest var),
            // and the effective lower bound is past the subst range, short-circuit.
            let fvar_lb = self.fvar_lb(e);
            if fvar_lb > sh_cut {
                let effective_fvar_lb = fvar_lb + sh_amt as u16;
                if effective_fvar_lb >= offset + n_substs {
                    if shift_down {
                        // Net effect: shift(e, sh_amt, sh_cut) then shift_down(n_substs, offset).
                        // All effective vars >= offset + n_substs, so all get shifted down.
                        // For sh_cut == 0: uniform shift, net = sh_amt - n_substs applied to core.
                        if sh_cut == 0 {
                            if sh_amt as u16 > n_substs {
                                return self.mk_shift(e, sh_amt as u16 - n_substs);
                            } else if (sh_amt as u16) < n_substs {
                                let r = self.push_shift_down_cutoff(e, n_substs - sh_amt as u16, 0);
                                return SPtr::unshifted(r);
                            } else {
                                return SPtr::unshifted(e);
                            }
                        }
                        // sh_cut > 0: fall through to full inst_aux
                    } else {
                        if sh_cut == 0 { return self.mk_shift(e, sh_amt as u16); }
                        return self.shift_expr(e, sh_amt as u16, sh_cut);
                    }
                }
            }
        }
        self.inst_aux(e, substs, offset, shift_down, sh_amt, sh_cut)
    }

    fn inst_aux_body(&mut self, e: ExprPtr<'t>, substs: &[SPtr<'t>], offset: u16, shift_down: bool, sh_amt: i16, sh_cut: u16) -> SPtr<'t> {
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
                return SPtr::unshifted(e);
            }
        } else {
            let effective_nlbv = if nlbv <= sh_cut { nlbv as i16 } else { nlbv as i16 + sh_amt };
            if effective_nlbv <= offset as i16 {
                self.trace.inst_aux_elided += 1;
                if nlbv <= sh_cut {
                    return SPtr::unshifted(e);
                }
                if sh_cut == 0 {
                    return self.mk_shift(e, sh_amt as u16);
                } else {
                    return self.shift_expr(e, sh_amt as u16, sh_cut);
                }
            }
        }

        // inst_cache: direct-mapped cache keyed by (e, substs_id, params)
        let params = (offset as u64) | ((sh_amt as u16 as u64) << 16) | ((sh_cut as u64) << 32);
        let substs_id = self.expr_cache.inst_substs_id;
        let cache_tag = e.get_hash().wrapping_mul(0x517cc1b727220a95) ^ params;
        if self.expr_cache.inst_cache.is_empty() {
            let dummy = SPtr::unshifted(crate::util::Ptr::from(crate::util::DagMarker::ExportFile, 0));
            let dummy_e: ExprPtr<'t> = crate::util::Ptr::from(crate::util::DagMarker::ExportFile, 0);
            self.expr_cache.inst_cache.resize(crate::util::INST_CACHE_SIZE, (0, 0, dummy_e, dummy));
        }
        let slot = (cache_tag as usize) & (crate::util::INST_CACHE_SIZE - 1);
        let (sid, p, ke, result) = self.expr_cache.inst_cache[slot];
        if sid == substs_id && p == params && ke == e {
            self.trace.inst_aux_cache_hits += 1;
            return result;
        }

        let n_substs = substs.len() as u16;

        // Key optimization: when the shift pushes all vars past the substitution range,
        // no variable will be substituted.
        if sh_amt > 0 && shift_down && sh_amt == n_substs as i16 && sh_cut == offset {
            self.trace.inst_aux_shift_skip_clean += 1;
            self.trace.inst_aux_elided += 1;
            let r = SPtr::unshifted(e);
            self.expr_cache.inst_cache[slot] = (substs_id, params, e, r);
            return r;
        }
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
            self.expr_cache.inst_cache[slot] = (substs_id, params, e, r);
            return r;
        }

        // Shift-down-only optimization: when all free bvars are past the substitution
        // range, no substitution occurs — only shift_down.
        if shift_down && sh_amt == 0 && n_substs >= 4 && nlbv > offset + n_substs {
            let lb = self.fvar_lb(e);
            if lb >= offset + n_substs {
                let r = SPtr::unshifted(self.push_shift_down_cutoff(e, n_substs, offset));
                self.expr_cache.inst_cache[slot] = (substs_id, params, e, r);
                return r;
            }
        }

        // Main dispatch: read the DAG node and process.
        // Children are SPtr — their shifts compose with the pending (sh_amt, sh_cut).
        let calcd = match self.read_expr(e) {
            Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => {
                if sh_amt > 0 { return SPtr::unshifted(e); }
                panic!("inst_aux_body reached closed expr with sh_amt=0 but nlbv > offset")
            }
            Var { dbj_idx, .. } => {
                let shifted_idx = if sh_amt != 0 && dbj_idx >= sh_cut { (dbj_idx as i16 + sh_amt) as u16 } else { dbj_idx };
                if shifted_idx < offset {
                    self.mk_var(shifted_idx)
                } else {
                    let rel_idx = shifted_idx - offset;
                    if rel_idx < n_substs {
                        let val = substs[substs.len() - 1 - rel_idx as usize];
                        self.sptr_shift(val, offset)
                    } else if shift_down {
                        self.mk_var(shifted_idx - n_substs)
                    } else {
                        if sh_amt != 0 { self.mk_var(shifted_idx) }
                        else { SPtr::unshifted(e) }
                    }
                }
            }
            App { fun, arg, .. } => {
                let new_fun = self.inst_aux_quick_sptr(fun, substs, offset, shift_down, sh_amt, sh_cut);
                let new_arg = self.inst_aux_quick_sptr(arg, substs, offset, shift_down, sh_amt, sh_cut);
                self.mk_app(new_fun, new_arg)
            }
            Pi { binder_name, binder_style, binder_type, body, .. } => {
                let new_type = self.inst_aux_quick_sptr(binder_type, substs, offset, shift_down, sh_amt, sh_cut);
                let new_body = self.inst_aux_quick_sptr(body, substs, offset + 1, shift_down, sh_amt, sh_cut + 1);
                self.mk_pi(binder_name, binder_style, new_type, new_body)
            }
            Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let new_type = self.inst_aux_quick_sptr(binder_type, substs, offset, shift_down, sh_amt, sh_cut);
                let new_body = self.inst_aux_quick_sptr(body, substs, offset + 1, shift_down, sh_amt, sh_cut + 1);
                self.mk_lambda(binder_name, binder_style, new_type, new_body)
            }
            Let { binder_name, binder_type, val, body, nondep, .. } => {
                let new_type = self.inst_aux_quick_sptr(binder_type, substs, offset, shift_down, sh_amt, sh_cut);
                let new_val = self.inst_aux_quick_sptr(val, substs, offset, shift_down, sh_amt, sh_cut);
                let new_body = self.inst_aux_quick_sptr(body, substs, offset + 1, shift_down, sh_amt, sh_cut + 1);
                self.mk_let(binder_name, new_type, new_val, new_body, nondep)
            }
            Proj { ty_name, idx, structure, .. } => {
                let new_structure = self.inst_aux_quick_sptr(structure, substs, offset, shift_down, sh_amt, sh_cut);
                self.mk_proj(ty_name, idx, new_structure)
            }
        };
        self.expr_cache.inst_cache[slot] = (substs_id, params, e, calcd);
        calcd
    }

    /// Shift all free variables in `e` (those with index >= cutoff) up by `amount`.
    /// For cutoff=0, creates a lazy Shift node (O(1)).
    /// For cutoff>0, traverses and rebuilds.
    pub fn shift_expr(&mut self, e: ExprPtr<'t>, amount: u16, cutoff: u16) -> SPtr<'t> {
        if amount == 0 || self.num_loose_bvars(e) <= cutoff {
            return SPtr::unshifted(e)
        }
        if cutoff == 0 {
            return self.mk_shift(e, amount);
        }
        self.shift_expr_aux(e, amount, cutoff)
    }

    fn shift_expr_aux(&mut self, e: ExprPtr<'t>, amount: u16, cutoff: u16) -> SPtr<'t> {
        if self.num_loose_bvars(e) <= cutoff {
            return SPtr::unshifted(e)
        }
        // If all free bvars are already >= cutoff, the cutoff is irrelevant —
        // this is a uniform shift, so use O(1) mk_shift instead of traversing.
        if self.fvar_lb(e) >= cutoff {
            return self.mk_shift(e, amount);
        }
        if let Some(&cached) = self.expr_cache.shift_cache.get(&(e, amount, cutoff)) {
            return cached;
        }
        let calcd = match self.read_expr(e) {
            Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => panic!(),
            Var { dbj_idx, .. } => {
                if dbj_idx >= cutoff {
                    self.mk_var(dbj_idx + amount)
                } else {
                    SPtr::unshifted(e)
                }
            }
            App { fun, arg, .. } => {
                let new_fun = self.shift_expr_aux_sptr(fun, amount, cutoff);
                let new_arg = self.shift_expr_aux_sptr(arg, amount, cutoff);
                self.mk_app(new_fun, new_arg)
            }
            Pi { binder_name, binder_style, binder_type, body, .. } => {
                let new_type = self.shift_expr_aux_sptr(binder_type, amount, cutoff);
                let new_body = self.shift_expr_aux_sptr(body, amount, cutoff + 1);
                self.mk_pi(binder_name, binder_style, new_type, new_body)
            }
            Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let new_type = self.shift_expr_aux_sptr(binder_type, amount, cutoff);
                let new_body = self.shift_expr_aux_sptr(body, amount, cutoff + 1);
                self.mk_lambda(binder_name, binder_style, new_type, new_body)
            }
            Let { binder_name, binder_type, val, body, nondep, .. } => {
                let new_type = self.shift_expr_aux_sptr(binder_type, amount, cutoff);
                let new_val = self.shift_expr_aux_sptr(val, amount, cutoff);
                let new_body = self.shift_expr_aux_sptr(body, amount, cutoff + 1);
                self.mk_let(binder_name, new_type, new_val, new_body, nondep)
            }
            Proj { ty_name, idx, structure, .. } => {
                let new_structure = self.shift_expr_aux_sptr(structure, amount, cutoff);
                self.mk_proj(ty_name, idx, new_structure)
            }
        };
        self.expr_cache.shift_cache.insert((e, amount, cutoff), calcd);
        calcd
    }

    /// Helper: shift an SPtr child. The child's own shift composes with the operation.
    /// Returns an SPtr (as the mk_* functions now expect SPtr children).
    pub(crate) fn shift_expr_aux_sptr(&mut self, child: SPtr<'t>, amount: u16, cutoff: u16) -> SPtr<'t> {
        // If the child has a shift, vars in child.core at index >= 0 become >= child.shift.
        // If child.shift >= cutoff, the cutoff is irrelevant for child.core's vars —
        // just add amount to the child's shift.
        if child.shift >= cutoff {
            return self.sptr_shift(child, amount);
        }
        // Otherwise, we need to traverse child.core with adjusted cutoff.
        let new_cutoff = cutoff - child.shift;
        let result = self.shift_expr_aux(child.core, amount, new_cutoff);
        SPtr::new(result.core, result.shift + child.shift)
    }

    /// From `e[x_1..x_n/v_1..v_n]`, abstract and re-inst, creating `e[y_1..y_n/v_1..v_n]`.
    pub(crate) fn replace_params(
        &mut self,
        e: ExprPtr<'t>,
        ingoing: &[ExprPtr<'t>],
        outgoing: &[ExprPtr<'t>],
    ) -> SPtr<'t> {
        let e = self.abstr(e, outgoing);
        let ingoing_sptrs: AppArgs<'t> = ingoing.iter().map(|&p| SPtr::unshifted(p)).collect();
        self.inst(e, &ingoing_sptrs)
    }

    fn abstr_aux(&mut self, e: ExprPtr<'t>, locals: &[ExprPtr<'t>], offset: u16) -> SPtr<'t> {
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.abstr_aux_body(e, locals, offset))
    }

    fn abstr_aux_body(&mut self, e: ExprPtr<'t>, locals: &[ExprPtr<'t>], offset: u16) -> SPtr<'t> {
        if !self.has_fvars(e) {
            SPtr::unshifted(e)
        } else if let Some(cached) = self.expr_cache.abstr_cache.get(&(e, offset)) {
            *cached
        } else {
            // Children are SPtr. Locals never appear under shift (nlbv=0).
            let calcd = match self.read_expr(e) {
                Local { .. } => {
                    locals.iter().rev().position(|x| *x == e)
                        .map(|pos| self.mk_var(u16::try_from(pos).unwrap() + offset))
                        .unwrap_or(SPtr::unshifted(e))
                }
                App { fun, arg, .. } => {
                    let new_fun = self.abstr_aux_sptr(fun, locals, offset);
                    let new_arg = self.abstr_aux_sptr(arg, locals, offset);
                    self.mk_app(new_fun, new_arg)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let new_type = self.abstr_aux_sptr(binder_type, locals, offset);
                    let new_body = self.abstr_aux_sptr(body, locals, offset + 1);
                    self.mk_pi(binder_name, binder_style, new_type, new_body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let new_type = self.abstr_aux_sptr(binder_type, locals, offset);
                    let new_body = self.abstr_aux_sptr(body, locals, offset + 1);
                    self.mk_lambda(binder_name, binder_style, new_type, new_body)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let new_type = self.abstr_aux_sptr(binder_type, locals, offset);
                    let new_val = self.abstr_aux_sptr(val, locals, offset);
                    let new_body = self.abstr_aux_sptr(body, locals, offset + 1);
                    self.mk_let(binder_name, new_type, new_val, new_body, nondep)
                }
                StringLit { .. } | NatLit { .. } => panic!(),
                Proj { ty_name, idx, structure, .. } => {
                    let new_structure = self.abstr_aux_sptr(structure, locals, offset);
                    self.mk_proj(ty_name, idx, new_structure)
                }
                Var { .. } | Sort { .. } | Const { .. } => panic!("should flag as no locals"),
            };

            self.expr_cache.abstr_cache.insert((e, offset), calcd);
            calcd
        }
    }

    /// Helper for abstr_aux: process an SPtr child.
    /// Locals have nlbv=0 so they can't appear under a shift.
    /// We recurse on child.core and re-wrap with child.shift.
    /// Abstract locals in an SPtr child. Adjusts offset to account for child's shift.
    fn abstr_aux_sptr(&mut self, child: SPtr<'t>, locals: &[ExprPtr<'t>], offset: u16) -> SPtr<'t> {
        if child.shift == 0 {
            return self.abstr_aux(child.core, locals, offset);
        }
        // child.shift > 0: the core is at a lower depth.
        // Adjust offset down to compensate, then reapply child.shift to result.
        if offset >= child.shift {
            let result = self.abstr_aux(child.core, locals, offset - child.shift);
            SPtr::new(result.core, result.shift + child.shift)
        } else {
            // offset < child.shift: materialize via view_sptr and recurse
            let viewed = self.view_sptr(child);
            match viewed {
                Local { .. } => {
                    locals.iter().rev().position(|x| *x == child.core)
                        .map(|pos| self.mk_var(u16::try_from(pos).unwrap() + offset))
                        .unwrap_or(child)
                }
                App { fun, arg, .. } => {
                    let f = self.abstr_aux_sptr(fun, locals, offset);
                    let a = self.abstr_aux_sptr(arg, locals, offset);
                    self.mk_app(f, a)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let t = self.abstr_aux_sptr(binder_type, locals, offset);
                    let b = self.abstr_aux_sptr(body, locals, offset + 1);
                    self.mk_pi(binder_name, binder_style, t, b)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let t = self.abstr_aux_sptr(binder_type, locals, offset);
                    let b = self.abstr_aux_sptr(body, locals, offset + 1);
                    self.mk_lambda(binder_name, binder_style, t, b)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let t = self.abstr_aux_sptr(binder_type, locals, offset);
                    let v = self.abstr_aux_sptr(val, locals, offset);
                    let b = self.abstr_aux_sptr(body, locals, offset + 1);
                    self.mk_let(binder_name, t, v, b, nondep)
                }
                Proj { ty_name, idx, structure, .. } => {
                    let s = self.abstr_aux_sptr(structure, locals, offset);
                    self.mk_proj(ty_name, idx, s)
                }
                _ => child,
            }
        }
    }

    /// Abstraction of unique identifiers; replaces free variables with the appropriate
    /// bound variable, if the free variable is in `locals`.
    pub fn abstr(&mut self, e: ExprPtr<'t>, locals: &[ExprPtr<'t>]) -> SPtr<'t> {
        self.expr_cache.abstr_cache.clear();
        self.abstr_aux(e, locals, 0u16)
    }

    /// Abstraction by deBruijn level: converts DbjLevel locals back to Var.
    /// Used by nanoda's locally-nameless TC.
    fn abstr_aux_levels(&mut self, e: ExprPtr<'t>, start_pos: u16, num_open_binders: u16) -> SPtr<'t> {
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.abstr_aux_levels_body(e, start_pos, num_open_binders))
    }

    fn abstr_aux_levels_body(&mut self, e: ExprPtr<'t>, start_pos: u16, num_open_binders: u16) -> SPtr<'t> {
        if !self.has_fvars(e) {
            SPtr::unshifted(e)
        } else if let Some(&cached) = self.expr_cache.abstr_cache_levels.get(&(e, start_pos, num_open_binders)) {
            cached
        } else {
            // Children are SPtr. Locals have nlbv=0 so never under shift.
            let calcd = match self.read_expr(e) {
                Local { id: FVarId::DbjLevel(serial), .. } =>
                    if serial < start_pos {
                        SPtr::unshifted(e)
                    } else {
                        self.fvar_to_bvar(num_open_binders, serial)
                    },
                Local { id: FVarId::Unique(..), .. } => SPtr::unshifted(e),
                App { fun, arg, .. } => {
                    let new_fun = self.abstr_aux_levels_sptr(fun, start_pos, num_open_binders);
                    let new_arg = self.abstr_aux_levels_sptr(arg, start_pos, num_open_binders);
                    self.mk_app(new_fun, new_arg)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let new_type = self.abstr_aux_levels_sptr(binder_type, start_pos, num_open_binders);
                    let new_body = self.abstr_aux_levels_sptr(body, start_pos, num_open_binders + 1);
                    self.mk_pi(binder_name, binder_style, new_type, new_body)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let new_type = self.abstr_aux_levels_sptr(binder_type, start_pos, num_open_binders);
                    let new_body = self.abstr_aux_levels_sptr(body, start_pos, num_open_binders + 1);
                    self.mk_lambda(binder_name, binder_style, new_type, new_body)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let new_type = self.abstr_aux_levels_sptr(binder_type, start_pos, num_open_binders);
                    let new_val = self.abstr_aux_levels_sptr(val, start_pos, num_open_binders);
                    let new_body = self.abstr_aux_levels_sptr(body, start_pos, num_open_binders + 1);
                    self.mk_let(binder_name, new_type, new_val, new_body, nondep)
                }
                StringLit { .. } | NatLit { .. } => panic!(),
                Proj { ty_name, idx, structure, .. } => {
                    let new_structure = self.abstr_aux_levels_sptr(structure, start_pos, num_open_binders);
                    self.mk_proj(ty_name, idx, new_structure)
                }
                Var { .. } | Sort { .. } | Const { .. } => panic!("should flag as no locals"),
            };
            self.expr_cache.abstr_cache_levels.insert((e, start_pos, num_open_binders), calcd);
            calcd
        }
    }

    /// Helper for abstr_aux_levels: process an SPtr child.
    fn abstr_aux_levels_sptr(&mut self, child: SPtr<'t>, start_pos: u16, num_open_binders: u16) -> SPtr<'t> {
        if child.shift == 0 {
            return self.abstr_aux_levels(child.core, start_pos, num_open_binders);
        }
        // Adjust num_open_binders by child.shift (same logic as abstr_aux_sptr)
        if num_open_binders >= child.shift {
            let result = self.abstr_aux_levels(child.core, start_pos, num_open_binders - child.shift);
            SPtr::new(result.core, result.shift + child.shift)
        } else {
            // Fallback: materialize and recurse
            let viewed = self.view_sptr(child);
            match viewed {
                Local { id: FVarId::DbjLevel(serial), .. } => {
                    if serial < start_pos { child }
                    else { self.fvar_to_bvar(num_open_binders, serial) }
                }
                Local { .. } => child,
                App { fun, arg, .. } => {
                    let f = self.abstr_aux_levels_sptr(fun, start_pos, num_open_binders);
                    let a = self.abstr_aux_levels_sptr(arg, start_pos, num_open_binders);
                    self.mk_app(f, a)
                }
                Pi { binder_name, binder_style, binder_type, body, .. } => {
                    let t = self.abstr_aux_levels_sptr(binder_type, start_pos, num_open_binders);
                    let b = self.abstr_aux_levels_sptr(body, start_pos, num_open_binders + 1);
                    self.mk_pi(binder_name, binder_style, t, b)
                }
                Lambda { binder_name, binder_style, binder_type, body, .. } => {
                    let t = self.abstr_aux_levels_sptr(binder_type, start_pos, num_open_binders);
                    let b = self.abstr_aux_levels_sptr(body, start_pos, num_open_binders + 1);
                    self.mk_lambda(binder_name, binder_style, t, b)
                }
                Let { binder_name, binder_type, val, body, nondep, .. } => {
                    let t = self.abstr_aux_levels_sptr(binder_type, start_pos, num_open_binders);
                    let v = self.abstr_aux_levels_sptr(val, start_pos, num_open_binders);
                    let b = self.abstr_aux_levels_sptr(body, start_pos, num_open_binders + 1);
                    self.mk_let(binder_name, t, v, b, nondep)
                }
                Proj { ty_name, idx, structure, .. } => {
                    let s = self.abstr_aux_levels_sptr(structure, start_pos, num_open_binders);
                    self.mk_proj(ty_name, idx, s)
                }
                _ => child,
            }
        }
    }

    /// Abstract deBruijn-level free variables back to bound variables.
    /// Used by nanoda's locally-nameless TC.
    pub fn abstr_levels(&mut self, e: ExprPtr<'t>, start_pos: u16) -> SPtr<'t> {
        self.expr_cache.abstr_cache_levels.clear();
        self.abstr_aux_levels(e, start_pos, self.dbj_level_counter)
    }

    fn subst_aux(&mut self, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> SPtr<'t> {
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.subst_aux_body(e, ks, vs))
    }

    fn subst_aux_body(&mut self, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> SPtr<'t> {
        if let Some(&cached) = self.expr_cache.subst_cache.get(&(e, ks, vs)) {
            return cached;
        }
        // Level substitution commutes with variable shifting (they operate on
        // independent parts: levels vs. bvar indices). For SPtr children,
        // we recurse on child.core and preserve child.shift.
        let r = match self.read_expr(e) {
            Var { .. } | NatLit { .. } | StringLit { .. } => SPtr::unshifted(e),
            Sort { level, .. } => {
                let new_level = self.subst_level(level, ks, vs);
                if new_level == level { SPtr::unshifted(e) } else { self.mk_sort(new_level) }
            }
            Const { name, levels, .. } => {
                let new_levels = self.subst_levels(levels, ks, vs);
                if new_levels == levels { SPtr::unshifted(e) } else { self.mk_const(name, new_levels) }
            }
            App { fun, arg, .. } => {
                let new_fun = self.subst_aux_sptr(fun, ks, vs);
                let new_arg = self.subst_aux_sptr(arg, ks, vs);
                if new_fun == fun && new_arg == arg { SPtr::unshifted(e) } else { self.mk_app(new_fun, new_arg) }
            }
            Pi { binder_name, binder_style, binder_type, body, .. } => {
                let new_type = self.subst_aux_sptr(binder_type, ks, vs);
                let new_body = self.subst_aux_sptr(body, ks, vs);
                if new_type == binder_type && new_body == body { SPtr::unshifted(e) } else { self.mk_pi(binder_name, binder_style, new_type, new_body) }
            }
            Lambda { binder_name, binder_style, binder_type, body, .. } => {
                let new_type = self.subst_aux_sptr(binder_type, ks, vs);
                let new_body = self.subst_aux_sptr(body, ks, vs);
                if new_type == binder_type && new_body == body { SPtr::unshifted(e) } else { self.mk_lambda(binder_name, binder_style, new_type, new_body) }
            }
            Let { binder_name, binder_type, val, body, nondep, .. } => {
                let new_type = self.subst_aux_sptr(binder_type, ks, vs);
                let new_val = self.subst_aux_sptr(val, ks, vs);
                let new_body = self.subst_aux_sptr(body, ks, vs);
                if new_type == binder_type && new_val == val && new_body == body { SPtr::unshifted(e) } else { self.mk_let(binder_name, new_type, new_val, new_body, nondep) }
            }
            Local { .. } => panic!("level substitution should not find locals"),
            Proj { ty_name, idx, structure, .. } => {
                let new_structure = self.subst_aux_sptr(structure, ks, vs);
                if new_structure == structure { SPtr::unshifted(e) } else { self.mk_proj(ty_name, idx, new_structure) }
            }
        };
        self.expr_cache.subst_cache.insert((e, ks, vs), r);
        r
    }

    /// Helper for subst_aux: level substitution commutes with shifting,
    /// so recurse on child.core and preserve child.shift.
    fn subst_aux_sptr(&mut self, child: SPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> SPtr<'t> {
        let result = self.subst_aux(child.core, ks, vs);
        SPtr::new(result.core, result.shift + child.shift)
    }

    pub fn subst_expr_levels(&mut self, e: ExprPtr<'t>, ks: LevelsPtr<'t>, vs: LevelsPtr<'t>) -> SPtr<'t> {
        if let Some(&cached) = self.expr_cache.dsubst_cache.get(&(e, ks, vs)) {
            return cached;
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
    ) -> SPtr<'t> {
        self.subst_expr_levels(info.ty, info.uparams, in_vals)
    }

    pub fn num_args(&self, e: ExprPtr<'t>) -> usize {
        let (mut cursor, mut num_args) = (e, 0);
        while let App { fun, .. } = self.read_expr(cursor) {
            cursor = fun.core;
            num_args += 1;
        }
        num_args
    }

    /// From `f a_0 .. a_N`, return `f` as SPtr.
    pub fn unfold_apps_fun(&self, mut e: SPtr<'t>) -> SPtr<'t> {
        loop {
            match self.read_expr(e.core) {
                App { fun, .. } => {
                    let new_shift = fun.shift + e.shift;
                    e = SPtr::new(fun.core, new_shift);
                }
                _ => break,
            }
        }
        e
    }

    /// From `f a_0 .. a_N`, return `(f, [a_0, ..a_N])`.
    /// Composes shifts through the App spine via SPtr arithmetic.
    pub fn unfold_apps(&self, mut e: SPtr<'t>) -> (SPtr<'t>, AppArgs<'t>) {
        let mut args = AppArgs::new();
        loop {
            match self.read_expr(e.core) {
                App { fun, arg, .. } => {
                    args.push(self.sptr_shift(arg, e.shift));
                    e = self.sptr_shift(fun, e.shift);
                }
                _ => break,
            }
        }
        args.reverse();
        (e, args)
    }

    /// If this is a const application, return (head_sptr, name, levels, args)
    pub fn unfold_const_apps(
        &self,
        e: SPtr<'t>,
    ) -> Option<(SPtr<'t>, NamePtr<'t>, LevelsPtr<'t>, AppArgs<'t>)> {
        let (f, args) = self.unfold_apps(e);
        match self.read_expr(f.core) {
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

    /// Like unfold_apps but returns args in reverse order (stack order).
    pub(crate) fn unfold_apps_stack(&self, mut e: SPtr<'t>) -> (SPtr<'t>, AppArgs<'t>) {
        let mut args = AppArgs::new();
        loop {
            match self.read_expr(e.core) {
                App { fun, arg, .. } => {
                    args.push(self.sptr_shift(arg, e.shift));
                    e = self.sptr_shift(fun, e.shift);
                }
                _ => break,
            }
        }
        (e, args)
    }

    pub fn foldl_apps(&mut self, mut fun: SPtr<'t>, args: impl Iterator<Item = SPtr<'t>>) -> SPtr<'t> {
        for arg in args {
            fun = self.mk_app(fun, arg);
        }
        fun
    }

    pub(crate) fn abstr_pis<I>(&mut self, mut binders: I, body: SPtr<'t>) -> SPtr<'t>
    where
        I: Iterator<Item = ExprPtr<'t>> + DoubleEndedIterator, {
        let mut result = body;
        while let Some(local) = binders.next_back() {
            result = self.abstr_pi(local, result)
        }
        result
    }

    pub(crate) fn abstr_pi(&mut self, binder: ExprPtr<'t>, body: SPtr<'t>) -> SPtr<'t> {
        match self.read_expr(binder) {
            Local { binder_name, binder_style, binder_type, .. } => {
                // Use abstr_aux_sptr to correctly handle body.shift.
                // abstr(body.core, ...) would drop the shift, producing wrong var indices.
                self.expr_cache.abstr_cache.clear();
                let body = self.abstr_aux_sptr(body, &[binder], 0);
                self.mk_pi(binder_name, binder_style, SPtr::unshifted(binder_type), body)
            }
            _ => unreachable!("Cannot apply pi with non-local domain type"),
        }
    }

    pub(crate) fn apply_lambda(&mut self, binder: ExprPtr<'t>, body: SPtr<'t>) -> SPtr<'t> {
        match self.read_expr(binder) {
            Local { binder_name, binder_style, binder_type, .. } => {
                self.expr_cache.abstr_cache.clear();
                let body = self.abstr_aux_sptr(body, &[binder], 0);
                self.mk_lambda(binder_name, binder_style, SPtr::unshifted(binder_type), body)
            }
            _ => unreachable!("Cannot apply lambda with non-local domain type"),
        }
    }
    
    pub(crate) fn is_nat_zero(&mut self, e: SPtr<'t>) -> bool {
        // NatLit and Const are closed (nlbv=0), so shift is irrelevant
        match self.read_expr(e.core) {
            Const { .. } => self.c_nat_zero().map(|z| z == e.core).unwrap_or(false),
            NatLit { ptr, .. } => self.read_bignum(ptr).map(|n| n.is_zero()).unwrap_or(false),
            _ => false,
        }
    }

    pub(crate) fn pred_of_nat_succ(&mut self, e: SPtr<'t>) -> Option<SPtr<'t>> {
        match self.read_expr(e.core) {
            App { fun, arg, .. } => {
                // fun is SPtr; Nat.succ is a Const (closed), so fun.shift doesn't matter
                let succ = self.c_nat_succ()?;
                if fun.core == succ {
                    Some(self.sptr_shift(arg, e.shift))
                } else {
                    None
                }
            }
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
    pub(crate) fn nat_lit_to_constructor(&mut self, n: BigUintPtr<'t>) -> Option<SPtr<'t>> {
        assert!(self.export_file.config.nat_extension);
        let n = self.read_bignum(n).unwrap();
        if n.is_zero() {
            self.c_nat_zero().map(SPtr::unshifted)
        } else {
            let pred = self.alloc_bignum(core::ops::Sub::sub(n, 1u8)).unwrap();
            let pred = self.mk_nat_lit(pred).unwrap();
            let succ_c = self.c_nat_succ()?;
            Some(self.mk_app(SPtr::unshifted(succ_c), pred))
        }
    }
    
    /// Check if `e` is an application of a specific constant with the given arity.
    /// With SPtr children, just follow the App.fun spine ignoring shifts.
    pub(crate) fn is_app_of_const(&self, e: ExprPtr<'t>, name: NamePtr<'t>, arity: usize) -> bool {
        let mut cur = e;
        for _ in 0..arity {
            if let App { fun, .. } = self.read_expr(cur) { cur = fun.core; } else { return false; }
        }
        if let Const { name: n, .. } = self.read_expr(cur) { n == name } else { false }
    }

    /// Return `true` iff `e` is an application of `@eagerReduce A a`
    pub(crate) fn is_eager_reduce_app(&self, e: ExprPtr<'t>) -> bool {
        if let Some(eager_name) = self.export_file.name_cache.eager_reduce {
            self.is_app_of_const(e, eager_name, 2)
        } else {
            false
        }
    }

    /// Convert a string literal to `String.ofList <| List.cons (Char.ofNat _) .. List.nil`
    pub(crate) fn str_lit_to_constructor(&mut self, s: StringPtr<'t>) -> Option<SPtr<'t>> {
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
    pub(crate) fn get_bignum_from_expr(&mut self, e: SPtr<'t>) -> Option<BigUint> {
        // NatLit and Const are closed, shift irrelevant
        match self.read_expr(e.core) {
            NatLit { ptr, .. } => self.read_bignum(ptr).cloned(),
            Const { .. } => {
                if Some(e.core) == self.c_nat_zero() {
                    Some(BigUint::zero())
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub(crate) fn get_bignum_succ_from_expr(&mut self, e: SPtr<'t>) -> Option<SPtr<'t>> {
        match self.read_expr(e.core) {
            NatLit { ptr, .. } => {
                self.mk_nat_lit_quick(self.read_bignum(ptr)? + 1usize)
            }
            Const { .. } => {
                if Some(e.core) == self.c_nat_zero() {
                    self.mk_nat_lit_quick(BigUint::zero() + 1usize)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Return the expression representing either `true` or `false`
    pub(crate) fn bool_to_expr(&mut self, b: bool) -> Option<SPtr<'t>> {
        if b {
            self.c_bool_true()
        } else {
            self.c_bool_false()
        }
    }

    pub(crate) fn c_bool_true(&mut self) -> Option<SPtr<'t>> {
        let n = self.export_file.name_cache.bool_true?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    pub(crate) fn c_bool_false(&mut self) -> Option<SPtr<'t>> {
        let n = self.export_file.name_cache.bool_false?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    /// c_nat_zero and c_nat_succ return ExprPtr for easy comparison with .core fields
    pub(crate) fn c_nat_zero(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.nat_zero?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels).core)
    }

    pub(crate) fn c_nat_succ(&mut self) -> Option<ExprPtr<'t>> {
        let n = self.export_file.name_cache.nat_succ?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels).core)
    }

    /// Make `Const("Nat", [])`
    pub(crate) fn nat_type(&mut self) -> Option<SPtr<'t>> {
        let n = self.export_file.name_cache.nat?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    /// Make `Const("String", [])`
    pub(crate) fn string_type(&mut self) -> Option<SPtr<'t>> {
        let n = self.export_file.name_cache.string?;
        let levels = self.alloc_levels_slice(&[]);
        Some(self.mk_const(n, levels))
    }

    /// Abstract `e` with the binders in `binders`, creating a lambda
    /// telescope while backing out.
    ///
    /// `[a, b, c], e` ~> `(fun (a b c) => e)`
    pub(crate) fn abstr_lambda_telescope(&mut self, mut binders: &[ExprPtr<'t>], body: SPtr<'t>) -> SPtr<'t> {
        let mut result = body;
        while let [tl @ .., binder] = binders {
            result = self.apply_lambda(*binder, result);
            binders = tl;
        }
        result
    }

    /// Abstract `e` with the binders in `binders`, creating a pi
    /// telescope while backing out.
    ///
    /// `[a, b, c], e` ~> `(Pi (a b c) => e)`
    pub(crate) fn abstr_pi_telescope(&mut self, mut binders: &[ExprPtr<'t>], body: SPtr<'t>) -> SPtr<'t> {
        let mut result = body;
        while let [tl @ .., binder] = binders {
            result = self.abstr_pi(*binder, result);
            binders = tl;
        }
        result
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
                App { fun, arg, .. } => self.find_const_aux(fun.core, pred, cache) || self.find_const_aux(arg.core, pred, cache),
                Pi { binder_type, body, .. } | Lambda { binder_type, body, .. } =>
                    self.find_const_aux(binder_type.core, pred, cache) || self.find_const_aux(body.core, pred, cache),
                Let { binder_type, val, body, .. } =>
                    self.find_const_aux(binder_type.core, pred, cache)
                        || self.find_const_aux(val.core, pred, cache)
                        || self.find_const_aux(body.core, pred, cache),
                Local { binder_type, .. } => self.find_const_aux(binder_type, pred, cache),
                Proj { structure, .. } => self.find_const_aux(structure.core, pred, cache),
            };
            cache.insert(e, r);
            r
        }
    }

    /// Return the number of leading `Pi` binders on this expression.
    pub(crate) fn pi_telescope_size(&mut self, mut e: SPtr<'t>) -> u16 {
        let mut size = 0u16;
        loop {
            match self.read_expr(e.core) {
                Pi { body, .. } => {
                    size += 1;
                    if e.shift == 0 {
                        e = body;
                    } else if body.shift >= 1 {
                        e = self.sptr_shift(body, e.shift);
                    } else {
                        e = self.shift_expr(body.core, e.shift, 1);
                    }
                }
                _ => break,
            }
        }
        size
    }

    /// Make `Sort(Level::Zero)` (Prop).
    pub(crate) fn prop(&mut self) -> SPtr<'t> { self.mk_sort(self.zero()) }

    pub fn get_nth_pi_binder(&mut self, mut e: SPtr<'t>, n: usize) -> Option<SPtr<'t>> {
        for _ in 0..n {
            match self.read_expr(e.core) {
                Pi { body, .. } => {
                    if e.shift == 0 {
                        e = body;
                    } else if body.shift >= 1 {
                        e = self.sptr_shift(body, e.shift);
                    } else {
                        e = self.shift_expr(body.core, e.shift, 1);
                    }
                }
                _ => return None
            }
        }
        match self.read_expr(e.core) {
            Pi { binder_type, .. } => Some(self.sptr_shift(binder_type, e.shift)),
            _ => None
        }
    }

    /// Get the name of the inductive type which is the major premise for this recursor
    /// by finding the correct binder in the recursor's type.
    pub fn get_major_induct(&mut self, rec: &crate::env::RecursorData<'t>) -> Option<NamePtr<'t>> {
        let binder = self.get_nth_pi_binder(SPtr::unshifted(rec.info.ty), rec.major_idx());
        match binder.map(|x| { let f = self.unfold_apps_fun(x); self.read_expr(f.core) }) {
            Some(Const { name, .. }) => Some(name),
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

    /// With SPtr, fvar_lb of a DAG ExprPtr is always 0 (cores are OSNF-normalized).
    /// The effective fvar_lb of an SPtr is sptr.shift.
    #[inline(always)]
    pub(crate) fn fvar_lb(&self, _e: ExprPtr<'t>) -> u16 {
        0
    }

}

impl<'t> Expr<'t> {
    /// The number of "loose" bound variables in this core expression.
    /// For compound expressions with SPtr children, this accounts for children's shifts.
    pub(crate) fn num_loose_bvars(&self) -> u16 {
        match self {
            Sort { .. } | Const { .. } | Local { .. } | StringLit { .. } | NatLit { .. } => 0,
            Var { dbj_idx, .. } => dbj_idx + 1,
            App { num_loose_bvars, .. }
            | Pi { num_loose_bvars, .. }
            | Lambda { num_loose_bvars, .. }
            | Let { num_loose_bvars, .. }
            | Proj { num_loose_bvars, .. } => *num_loose_bvars,
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
            | Proj { has_fvars, .. } => *has_fvars,
        }
    }
}


