use crate::env::ReducibilityHint;
use crate::env::{ConstructorData, Declar, DeclarInfo, Env, InductiveData, RecRule, RecursorData};
use crate::expr::Expr;
use crate::level::Level;
use crate::util::{
    nat_div, nat_mod, nat_sub, nat_gcd, nat_land, nat_lor,
    nat_xor, nat_shr, nat_shl, new_fx_hash_map, ExportFile, ExprPtr, FxHashMap, LevelPtr,
    LevelsPtr, NamePtr, TcCache, TcCtx, StringPtr
};
use std::error::Error;
use num_traits::pow::Pow;


use DeltaResult::*;
use Expr::*;
use InferFlag::*;

/// Communicates the result of lazy delta reduction during definitional equality
/// checking; if we can no longer unfold any definitions, and we weren't already
/// able to show that the expressions were equal using a cheap method, then we return
/// `Exhaused(x, y)`, and continue with more expensive checks. If we were able to cheaply
/// determine that two expressions are or are not equal, we return `FoundEqResult`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DeltaResult<'a> {
    FoundEqResult(bool),
    Exhausted(ExprPtr<'a>, ExprPtr<'a>),
}

/// An enum for type safety and convenience; used during nat literal reduction, and also for testing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NatBinOp {
    Add,
    Sub,
    Mul,
    Pow,
    Mod,
    Div,
    Beq,
    Ble,
    Gcd,
    LAnd,
    LOr,
    XOr,
    Shl,
    Shr,
}

/// A flag that accompanies calls to type inference; if the flag is `Check`,
/// we perform additional definitional equality checks (for example, the type of an
/// argument to a lambda is the same type as the binder in the labmda). These checks
/// are costly however, and in some cases we're using inference during reduction of
/// expressions we know to be well-typed, so we can pass the flag `InferOnly` to omit
/// these checks when they are not needed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum InferFlag {
    InferOnly,
    Check,
}

pub struct TypeChecker<'x, 't, 'p> {
    pub(crate) ctx: &'x mut TcCtx<'t, 'p>,
    /// An immutable reference to an environment, which contains declarations and notation.
    /// To accommodate the temporary declarations created while checking nested inductives,
    /// the environment may have a temporary extension which also holds declarations, and
    /// is searched before the persistent environment.
    ///
    /// This is stored as a field in `TypeChecker` rather than being placed in `TcCtx` so
    /// that the borrow checker will allow us to mutably reference `TcCtx` while we have
    /// outstanding references to environment declarations. Rust can tell that borrows
    /// of different struct fields are exclusive, but it can't analyze what fields of a given
    /// field's type are being exclusively borrowed.
    pub(crate) env: &'x Env<'x, 't>,
    /// The caches for things like inference, reduction, and equality checking.
    pub(crate) tc_cache: TcCache<'t>,
    /// If this type checker is being used to check a simple declaration, this field will
    /// contain the universe parameters of that declaration. This is used in a couple of places
    /// to make sure that all of the universe paramters actually used in a declaration `d` are
    /// properly represented in the declaration's uparams info.
    pub(crate) declar_info: Option<DeclarInfo<'t>>,
    /// Local typing context for de Bruijn variables.
    /// `local_ctx[0]` is the type of `Var(0)` (most recently bound variable).
    /// Types are stored as they appear in the binder (valid at the depth before the binder).
    /// When looking up `Var(k)`, we shift `local_ctx[k]` up by `k+1`.
    pub(crate) local_ctx: Vec<ExprPtr<'t>>,
}

impl<'p> ExportFile<'p> {
    /// The entry point for checking a declaration `d`.
    pub fn check_declar(&self, d: &Declar<'p>) {
        use Declar::*;
        match d {
            Axiom { .. } => self.with_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap()),
            Inductive(..) => self.check_inductive_declar(d),
            Quot { .. } => self.with_ctx(|ctx| crate::quot::check_quot(ctx, d)),
            Definition { val, .. } | Theorem { val, .. } | Opaque { val, .. } =>
                self.with_tc_and_declar(*d.info(), |tc| {
                    tc.check_declar_info(d).unwrap();
                    let inferred_type = tc.infer(*val, crate::tc::InferFlag::Check);
                    tc.assert_def_eq(inferred_type, d.info().ty);
                }),
            Constructor(ctor_data) => {
                self.with_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap());
                assert!(self.declars.get(&ctor_data.inductive_name).is_some());
            }
            Recursor(recursor_data) => {
                self.with_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap());
                for ind_name in recursor_data.all_inductives.iter() {
                    assert!(self.declars.get(ind_name).is_some())
                }
            }
        }
    }

    /// Check all declarations in this export file using a single thread.
    pub(crate) fn check_all_declars_serial(&self) {
        let total = self.declars.len();
        for (i, declar) in self.declars.values().enumerate() {
            if i % 10000 == 0 {
                eprintln!("[{}/{}]", i, total);
            }
            self.check_declar(declar);
        }
    }

    /// Check all declarations in this export file, spawning `num_threads` as
    /// checkers.
    fn check_all_declars_par(&self, num_threads: usize) {
        use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
        use std::thread;
        let task_num = AtomicUsize::new(0);
        thread::scope(|sco| {
            let mut handles = Vec::new();
            for i in 0..num_threads {
                handles.push(
                    thread::Builder::new()
                        .name(format!("thread_{}", i))
                        .stack_size(crate::STACK_SIZE)
                        .spawn_scoped(sco, || loop {
                            let idx = task_num.fetch_add(1, Relaxed);
                            if let Some((_, declar)) = self.declars.get_index(idx) {
                                self.check_declar(declar);
                            } else {
                                break
                            }
                        })
                        .unwrap(),
                )
            }
            for t in handles {
                t.join().expect("A thread in `check_all_declars` panicked while being joined");
            }
        });
    }

    /// Check all of the declarations in this export file on the specified number
    /// of threads (checking will be serial on the main thread is num_threads <= 1).
    pub fn check_all_declars(&self) {
        if self.config.num_threads > 1 {
            self.check_all_declars_par(self.config.num_threads)
        } else {
            self.check_all_declars_serial()
        }
    }
}

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    pub fn new(dag: &'x mut TcCtx<'t, 'p>, env: &'x Env<'x, 't>, declar_info: Option<DeclarInfo<'t>>) -> Self {
        Self { ctx: dag, env, tc_cache: TcCache::new(), declar_info, local_ctx: Vec::new() }
    }

    /// Look up the type of Var(k) in the local context, shifting it to be valid at
    /// the current depth.
    fn lookup_var(&mut self, dbj_idx: u16) -> ExprPtr<'t> {
        let depth = self.local_ctx.len();
        let ty = self.local_ctx[depth - 1 - dbj_idx as usize];
        // ty was valid at depth (depth - 1 - dbj_idx), i.e., before the
        // binder that introduced Var(dbj_idx). To make it valid at current depth,
        // we shift up by dbj_idx + 1.
        self.ctx.shift_expr(ty, dbj_idx + 1, 0)
    }

    /// Push a binder type onto the local context (entering a binder).
    fn push_local(&mut self, ty: ExprPtr<'t>) {
        self.local_ctx.push(ty);
        self.tc_cache.infer_cache.push(new_fx_hash_map());
        self.tc_cache.defeq_pos_open.push(new_fx_hash_map());
        self.tc_cache.defeq_neg_open.push(new_fx_hash_map());
    }

    /// Pop a binder type from the local context (exiting a binder).
    fn pop_local(&mut self) {
        self.local_ctx.pop().expect("pop_local: empty context");
        self.tc_cache.infer_cache.pop();
        self.tc_cache.defeq_pos_open.pop();
        self.tc_cache.defeq_neg_open.pop();
    }

    /// Restore local context to a previous depth.
    fn restore_depth(&mut self, depth: usize) {
        if self.local_ctx.len() > depth {
            self.local_ctx.truncate(depth);
            self.tc_cache.infer_cache.truncate(depth + 1); // +1 for base bucket
            self.tc_cache.defeq_pos_open.truncate(depth);
            self.tc_cache.defeq_neg_open.truncate(depth);
        }
    }

    /// Conduct the preliminary checks done on all declarations; a declaration
    /// must not contain duplicate universe parameters, mut not have free variables,
    /// and must have an ascribed type that is actually a type (`infer declaration.type` must
    /// be a sort).
    pub(crate) fn check_declar_info(&mut self, d: &Declar<'t>) -> Result<(), Box<dyn Error>> {
        let info = d.info();
        assert!(self.ctx.no_dupes_all_params(info.uparams));
        assert!(self.ctx.num_loose_bvars(info.ty) == 0);
        let inferred_type = self.infer(info.ty, Check);
        let sort = self.ensure_sort(inferred_type);

        // This is sort of a "soft" check in terms of soundness, but for theorems, ensure 
        // that they're propositions.
        if let Declar::Theorem {..} = d {
            if !self.ctx.is_zero(sort) {
                return Err(Box::<dyn Error>::from(format!("Theorem type for {:?} must be `Prop` (sort 0); found type {:?}",
                    self.ctx.debug_print(info.name),
                    self.ctx.debug_print(sort)
                )))
            }
        } 
        Ok(())
    }

    /// Infer a `Const` by retrieving its type from the environment, then substituting
    /// the universe parameters for the ones in the declaration we're checking.
    fn infer_const(&mut self, c_name: NamePtr<'t>, c_uparams: LevelsPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        if let Some(declar_info) = self.env.get_declar(&c_name).map(|x| x.info()).cloned() {
            if let (Check, Some(this_declar_info)) = (flag, self.declar_info) {
                for c_uparam in self.ctx.read_levels(c_uparams).iter().copied() {
                    assert!(self.ctx.all_uparams_defined(c_uparam, this_declar_info.uparams))
                }
            }
            self.ctx.subst_declar_info_levels(declar_info, c_uparams)
        } else {
            panic!("declaration not found in infer_const, {:?}", self.ctx.debug_print(c_name))
        }
    }

    /// Retrieve the recursor rule corresponding to the constructor used in the major premise.
    fn get_rec_rule(&self, rec_rules: &[RecRule<'t>], major_const: ExprPtr<'t>) -> Option<RecRule<'t>> {
        if let Const { name: major_ctor_name, .. } = self.ctx.read_expr(major_const) {
            for r @ RecRule { ctor_name, .. } in rec_rules.iter().copied() {
                if ctor_name == major_ctor_name {
                    return Some(r)
                }
            }
        }
        None
    }

    /// Expand `(x : Prod A B)` into `Prod.mk (Prod.fst x) (Prod.snd x)`
    fn expand_eta_struct_aux(&mut self, e_type: ExprPtr<'t>, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        // `c_name = Point`
        let (_f, c_name, c_levels, args) = self.ctx.unfold_const_apps(e_type)?;
        // `Point` declaration
        let InductiveData { all_ctor_names, .. } = self.env.get_inductive(&c_name)?;
        // Name = `Point.mk`
        let ctor_name0 = all_ctor_names.get(0).copied()?;
        // Ctor data for `Point.mk`
        let ConstructorData { num_params, num_fields, .. } = self.env.get_constructor(&ctor_name0).unwrap();
        // Const { name := Point.mk, levels := .. }
        let mut out = self.ctx.mk_const(ctor_name0, c_levels);
        // apply the params taken from the inferred type
        // `Point.mk (A : Type) (B : Type)`
        for i in 0..((*num_params) as usize) {
            out = self.ctx.mk_app(out, args[i])
        }
        // for (a : A) and (b : B),
        // `Proj {idx := 0, struct := e}`
        // `Point.mk A B (Point.0 e) (Point.1 e)`
        for i in 0..((*num_fields) as u32) {
            let proj = self.ctx.mk_proj(c_name, i, e);
            out = self.ctx.mk_app(out, proj);
        }
        Some(out)
    }

    pub(crate) fn ensure_infers_as_sort(&mut self, e: ExprPtr<'t>) -> LevelPtr<'t> {
        let infd = self.infer(e, Check);
        self.ensure_sort(infd)
    }

    pub(crate) fn ensure_sort(&mut self, e: ExprPtr<'t>) -> LevelPtr<'t> {
        if let Sort { level, .. } = self.ctx.read_expr(e) {
            return level
        }
        let whnfd = self.whnf(e);
        match self.ctx.view_expr(whnfd) {
            Sort { level, .. } => level,
            _ => panic!("ensur_sort could not produce a sort"),
        }
    }

    fn ensure_pi(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        if let Pi { .. } = self.ctx.read_expr(e) {
            return e
        }
        let whnfd = self.whnf(e);
        match self.ctx.view_expr(whnfd) {
            Pi { .. } => whnfd,
            _ => panic!("ensure_pi could not produce a pi"),
        }
    }

    pub(crate) fn infer_sort_of(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> LevelPtr<'t> {
        let ty = self.infer(e, flag);
        let whnfd = self.whnf(ty);
        match self.ctx.view_expr(whnfd) {
            Sort { level, .. } => level,
            _ => {
                panic!("infer_sort_of: expected Sort, got {:?} from e={:?}, infer={:?}, depth={}", self.ctx.debug_print(whnfd), self.ctx.debug_print(e), self.ctx.debug_print(ty), self.local_ctx.len());
            }
        }
    }

    fn try_eta_struct(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        matches!(self.try_eta_struct_aux(x, y), Some(true)) || matches!(self.try_eta_struct_aux(y, x), Some(true))
    }

    fn try_eta_struct_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        let (_, name, _, args) = self.ctx.unfold_const_apps(y)?;
        let ConstructorData { inductive_name, num_params, num_fields, .. } = self.env.get_constructor(&name)?;
        if args.len() == (*num_params + *num_fields) as usize && self.env.can_be_struct(inductive_name) {
            let (x_type, y_type) = (self.infer(x, InferOnly), self.infer(y, InferOnly));
            if self.def_eq(x_type, y_type) {
                for i in (*num_params as usize)..args.len() {
                    let proj = self.ctx.mk_proj(*inductive_name, (i - *num_params as usize) as u32, x);
                    let rhs = args[i];
                    if !self.def_eq(proj, rhs) {
                        return None
                    }
                }
                return Some(true)
            }
        }
        None
    }

    fn str_lit_to_ctor_reducing(&mut self, x: StringPtr<'t>) -> Option<ExprPtr<'t>> {
        self.ctx.str_lit_to_constructor(x).map(|x| self.whnf(x))
    }

    fn try_string_lit_expansion_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        if let (StringLit { ptr, .. }, App { fun, .. }) = self.ctx.read_expr_pair(x, y) {
            if let Some((name, _levels)) = self.ctx.try_const_info(fun) {
                if name == self.ctx.export_file.name_cache.string_of_list? {
                    // levels should be empty
                    let lhs = self.str_lit_to_ctor_reducing(ptr)?;
                    return Some(self.def_eq(lhs, y))
                }
            }
        }
        None
    }

    fn try_string_lit_expansion(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        if !self.ctx.export_file.config.string_extension {
            return false
        }
        matches!(self.try_string_lit_expansion_aux(x, y), Some(true))
            || matches!(self.try_string_lit_expansion_aux(y, x), Some(true))
    }

    // For structures that carry no additional information, elements with the same type are def_eq.
    fn def_eq_unit(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        let x_ty = self.infer_then_whnf(x, InferOnly);
        let (_, name, _levels, _) = self.ctx.unfold_const_apps(x_ty)?;
        let InductiveData { num_indices, all_ctor_names, .. } = self.env.get_inductive(&name)?;
        if all_ctor_names.len() != 1 || *num_indices != 0 {
            return None
        }
        let ctor_name = &all_ctor_names[0];
        let ctor = self.env.get_constructor(ctor_name)?;
        if ctor.num_fields != 0 {
            return None
        }
        let y_type = self.infer(y, InferOnly);
        Some(self.def_eq(x_ty, y_type))
    }

    fn do_nat_bin(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>, op: NatBinOp) -> Option<ExprPtr<'t>> {
        use NatBinOp::*;
        let (x, y) = (self.whnf(x), self.whnf(y));
        let (arg1, arg2) = (self.ctx.get_bignum_from_expr(x)?, self.ctx.get_bignum_from_expr(y)?);
        match op {
            Add => self.ctx.mk_nat_lit_quick(arg1 + arg2),
            Sub => self.ctx.mk_nat_lit_quick(nat_sub(arg1, arg2)),
            Mul => self.ctx.mk_nat_lit_quick(arg1 * arg2),
            Pow => self.ctx.mk_nat_lit_quick(arg1.pow(arg2)),
            Div => self.ctx.mk_nat_lit_quick(nat_div(arg1, arg2)),
            Mod => self.ctx.mk_nat_lit_quick(nat_mod(arg1, arg2)),
            Gcd => self.ctx.mk_nat_lit_quick(nat_gcd(&arg1, &arg2)),
            LAnd => self.ctx.mk_nat_lit_quick(nat_land(arg1, arg2)),
            LOr => self.ctx.mk_nat_lit_quick(nat_lor(arg1, arg2)),
            XOr => self.ctx.mk_nat_lit_quick(nat_xor(&arg1, &arg2)),
            Shl => self.ctx.mk_nat_lit_quick(nat_shl(arg1, arg2)),
            Shr => self.ctx.mk_nat_lit_quick(nat_shr(arg1, arg2)),
            Beq => self.ctx.bool_to_expr(arg1 == arg2),
            Ble => self.ctx.bool_to_expr(arg1 <= arg2),
        }
    }
    
    /// Try to reduce an expression `e` which is an application of `Nat.succ`,
    /// or an application of a supported binary operation. `e` must have no free
    /// variables.
    pub(crate) fn try_reduce_nat(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        if !self.ctx.export_file.config.nat_extension {
            return None
        }
        if self.ctx.num_loose_bvars(e) > 0 {
            return None
        }
        let (f, args) = self.ctx.unfold_apps(e);
        let out = match (self.ctx.read_expr(f), args.as_slice()) {
            (Const { name, .. }, [arg]) if Some(name) == self.ctx.export_file.name_cache.nat_succ => {
                let v_expr = self.whnf(*arg);
                self.ctx.get_bignum_succ_from_expr(v_expr)
            }
            (Const { name, .. }, [arg1, arg2]) => {
                let op = if Some(name) == self.ctx.export_file.name_cache.nat_add {
                    NatBinOp::Add
                } else if Some(name) == self.ctx.export_file.name_cache.nat_sub {
                    NatBinOp::Sub
                } else if Some(name) == self.ctx.export_file.name_cache.nat_mul {
                    NatBinOp::Mul
                } else if Some(name) == self.ctx.export_file.name_cache.nat_pow {
                    NatBinOp::Pow
                } else if Some(name) == self.ctx.export_file.name_cache.nat_mod {
                    NatBinOp::Mod
                } else if Some(name) == self.ctx.export_file.name_cache.nat_div {
                    NatBinOp::Div
                } else if Some(name) == self.ctx.export_file.name_cache.nat_beq {
                    NatBinOp::Beq
                } else if Some(name) == self.ctx.export_file.name_cache.nat_ble {
                    NatBinOp::Ble
                } else if Some(name) == self.ctx.export_file.name_cache.nat_land {
                    NatBinOp::LAnd
                } else if Some(name) == self.ctx.export_file.name_cache.nat_lor {
                    NatBinOp::LOr
                } else if Some(name) == self.ctx.export_file.name_cache.nat_xor {
                    NatBinOp::XOr
                } else if Some(name) == self.ctx.export_file.name_cache.nat_gcd {
                    NatBinOp::Gcd
                } else if Some(name) == self.ctx.export_file.name_cache.nat_shl {
                    NatBinOp::Shl
                } else if Some(name) == self.ctx.export_file.name_cache.nat_shr {
                    NatBinOp::Shr
                } else {
                    return None
                };
                self.do_nat_bin(*arg1, *arg2, op)
            }
            _ => None,
        };
        out
    }

    fn reduce_proj(&mut self, idx: u32, structure: ExprPtr<'t>, cheap: bool) -> Option<ExprPtr<'t>> {
        let mut structure = if cheap { self.whnf_no_unfolding_cheap_proj(structure) } else { self.whnf(structure) };
        if let StringLit { ptr, .. } = self.ctx.view_expr(structure) {
            if let Some(s) = self.str_lit_to_ctor_reducing(ptr) {
                structure = s;
            }
        }
        let (_, name, _, args) = self.ctx.unfold_const_apps(structure)?;
        let ConstructorData { num_params, .. } = self.env.get_constructor(&name)?;
        let i = (*num_params as usize) + idx as usize;
        Some(args.get(i).copied().unwrap())
    }

    pub(crate) fn infer_then_whnf(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let ty = self.infer(e, flag);
        self.whnf(ty)
    }

    #[allow(non_snake_case)]
    fn infer_proj(&mut self, _ty_name: NamePtr<'t>, idx: u32, structure: ExprPtr<'t>) -> ExprPtr<'t> {
        let (structure_ty_is_prop, structure_ty) = {
            let (is_proof, t) = self.is_proof(structure);
            (is_proof, self.whnf(t))
        };
        let (_, struct_ty_name, struct_ty_levels, struct_ty_args) = self.ctx.unfold_const_apps(structure_ty).unwrap();

        let InductiveData { info: inductive_info, all_ctor_names, num_params, .. } =
            self.env.get_inductive(&struct_ty_name).unwrap();

        let ConstructorData { info: ctor_info, .. } = self.env.get_constructor(&all_ctor_names[0]).unwrap();
        let mut ctor_ty = self.ctx.subst_declar_info_levels(*ctor_info, struct_ty_levels);
        for i in 0..(*num_params) {
            ctor_ty = self.whnf(ctor_ty);
            match self.ctx.view_expr(ctor_ty) {
                Pi { body, .. } => {
                    ctor_ty = self.ctx.inst_beta(body, &[struct_ty_args[i as usize]]);
                }
                _ => panic!("Ran out of param telescope"),
            }
        }
        for i in 0..idx {
            ctor_ty = self.whnf(ctor_ty);
            match self.ctx.view_expr(ctor_ty) {
                Pi { binder_type, body, .. } => {
                    if self.ctx.num_loose_bvars(body) != 0 {
                      if structure_ty_is_prop && !self.is_proposition(binder_type).0 {
                          panic!("infer_proj prop")
                      }
                      let arg = self.ctx.mk_proj(inductive_info.name, i, structure);
                      ctor_ty = self.ctx.inst_beta(body, &[arg]);
                    } else {
                      ctor_ty = body;
                    }
                }
                _ => panic!("Ran out of constructor telescope"),
            }
        }
        let reduced = self.whnf(ctor_ty);
        match self.ctx.view_expr(reduced) {
            Pi { binder_type, .. } => {
                if structure_ty_is_prop && !self.is_proposition(binder_type).0 {
                    panic!("infer_proj prop")
                }
                binder_type
            }
            _ => panic!("Ran out of constructor telescope getting field")
        }
    }

    pub(crate) fn infer(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.infer_inner(e, flag))
    }

    fn infer_inner(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        // Handle Shift nodes without forcing: infer(Shift(inner, k, 0), d) = mk_shift(infer(inner, d-k), k).
        // Temporarily shrink the context to depth d-k, infer inner, restore, shift result.
        // Only works for cutoff=0 (top-level shifts). For cutoff>0, force first.
        if let Expr::Shift { inner, amount, cutoff, .. } = self.ctx.read_expr(e) {
            if cutoff == 0 {
                let new_depth = self.local_ctx.len() - amount as usize;
                let saved_locals = self.local_ctx.split_off(new_depth);
                let saved_cache = self.tc_cache.infer_cache.split_off(new_depth + 1); // +1 for base bucket
                let saved_pos = self.tc_cache.defeq_pos_open.split_off(new_depth);
                let saved_neg = self.tc_cache.defeq_neg_open.split_off(new_depth);
                let inner_type = self.infer(inner, flag);
                self.local_ctx.extend(saved_locals);
                self.tc_cache.infer_cache.extend(saved_cache);
                self.tc_cache.defeq_pos_open.extend(saved_pos);
                self.tc_cache.defeq_neg_open.extend(saved_neg);
                return self.ctx.mk_shift(inner_type, amount);
            } else {
                let forced = self.ctx.force_shift_shallow(inner, amount, cutoff);
                return self.infer(forced, flag);
            }
        }
        // Shift-invariant infer cache: bucket 0 for closed, bucket (depth - fvar_lb) for open.
        let depth = self.local_ctx.len() as u16;
        let bucket_idx = if self.ctx.num_loose_bvars(e) == 0 {
            0
        } else {
            let e_fvl = self.ctx.read_expr(e).get_fvar_list();
            let e_lb = self.ctx.fvar_lb(e_fvl);
            (depth - e_lb) as usize
        };
        let canon = self.ctx.canonical_hash(e);
        if let Some(bucket) = self.tc_cache.infer_cache.get(bucket_idx) {
            if let Some(&(stored_input, stored_result, stored_depth)) = bucket.get(&canon) {
                if stored_input == e && stored_depth == depth {
                    return stored_result;
                }
                if depth >= stored_depth {
                    let delta = depth - stored_depth;
                    if delta > 0 && self.ctx.shift_eq(stored_input, e, delta) {
                        return self.ctx.mk_shift(stored_result, delta);
                    }
                }
            }
        }
        let r = match self.ctx.read_expr(e) {
            Local { binder_type, .. } => binder_type,
            Var { dbj_idx, .. } => self.lookup_var(dbj_idx),
            Sort { level, .. } => self.infer_sort(level, flag),
            App { .. } => self.infer_app(e, flag),
            Pi { .. } => self.infer_pi(e, flag),
            Lambda { .. } => self.infer_lambda(e, flag),
            Let { binder_type, val, body, .. } => self.infer_let(binder_type, val, body, flag),
            Const { name, levels, .. } => self.infer_const(name, levels, flag),
            Proj { ty_name, idx, structure, .. } => self.infer_proj(ty_name, idx, structure),
            NatLit { .. } => {
                assert!(self.ctx.export_file.config.nat_extension);
                self.ctx.nat_type().unwrap()
            }
            StringLit { .. } => {
                assert!(self.ctx.export_file.config.string_extension);
                self.ctx.string_type().unwrap()
            }
            Shift { .. } => unreachable!("Shift handled before cache lookup")
        };
        if let Some(bucket) = self.tc_cache.infer_cache.get_mut(bucket_idx) {
            // Prefer entry at lower depth (better for future shift hits)
            if bucket.get(&canon).map_or(true, |&(_, _, sd)| depth < sd) {
                bucket.insert(canon, (e, r, depth));
            }
        }
        r
    }

    fn infer_sort(&mut self, l: LevelPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        if let (Check, Some(declar_info)) = (flag, self.declar_info) {
            assert!(self.ctx.all_uparams_defined(l, declar_info.uparams))
        }
        let out = self.ctx.succ(l);
        self.ctx.mk_sort(out)
    }

    fn infer_app(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let (mut fun, mut args) = self.ctx.unfold_apps_stack(e);
        let mut ctx = Vec::new();
        fun = self.infer(fun, flag);
        while !args.is_empty() {
            match self.ctx.view_expr(fun) {
                Pi { binder_type, body, .. } => {
                    let arg = args.pop().unwrap();
                    if flag == Check {
                        let arg_type = self.infer(arg, flag);
                        let binder_type_instd = self.ctx.inst_beta(binder_type, ctx.as_slice());
                        let outer_scope_eager_setting = self.ctx.eager_mode;
                        if self.ctx.is_eager_reduce_app(arg) {
                            self.ctx.eager_mode = true;
                        }
                        // `arg_type` and `binder_type` get swapped here to accommodate the
                        // eager reduction branch in `def_eq` being focused on reducing the lhs.
                        self.assert_def_eq(binder_type_instd, arg_type);
                        // replace the outer scope's setting before next iteration
                        self.ctx.eager_mode = outer_scope_eager_setting;
                    }
                    ctx.push(arg);
                    fun = body;
                }
                _ => {
                    let as_pi = self.ctx.inst_beta(fun, ctx.as_slice());
                    let as_pi = self.ensure_pi(as_pi);
                    match self.ctx.view_expr(as_pi) {
                        Pi { .. } => {
                            // Only clear what we just instantiated.
                            ctx.clear();
                            fun = as_pi;
                        }
                        _ => panic!(),
                    }
                }
            }
        }
        self.ctx.inst_beta(fun, ctx.as_slice())
    }

    //fn infer_app(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
    //    match self.ctx.read_expr(e) {
    //        App {fun, arg, ..} => {
    //            let fun_ty = self.infer_then_whnf(fun, flag);
    //            match self.ctx.read_expr(fun_ty) {
    //                Pi {binder_type, body, ..} => {
    //                    if flag == InferFlag::Check {
    //                        let arg_ty = self.infer(arg, flag);
    //                        let outer_scope_eager_setting = self.ctx.eager_mode;
    //                        if self.ctx.is_eager_reduce_app(arg) {
    //                            self.ctx.eager_mode = true;
    //                        }
    //                        self.assert_def_eq(binder_type, arg_ty);
    //                        self.ctx.eager_mode = outer_scope_eager_setting;
    //                    }
    //                    self.ctx.inst(body, &[arg])
    //                },
    //                _ => panic!()
    //            }
    //        },
    //        _ => panic!()
    //    }
    //}

    fn infer_lambda(&mut self, mut e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        // Collect binder info while descending into nested lambdas
        let mut binders: Vec<(NamePtr<'t>, crate::expr::BinderStyle, ExprPtr<'t>)> = Vec::new();
        while let Lambda { binder_name, binder_style, binder_type, body, .. } = self.ctx.view_expr(e) {
            if let Check = flag {
                self.infer_sort_of(binder_type, flag);
            }
            self.push_local(binder_type);
            binders.push((binder_name, binder_style, binder_type));
            e = body;
        }

        // Infer the type of the body (which has Var(0)..Var(n-1) for bound vars)
        let mut result_ty = self.infer(e, flag);

        // Build the Pi type by popping binders in reverse
        for (binder_name, binder_style, binder_type) in binders.into_iter().rev() {
            self.pop_local();
            // result_ty has Var(0) referring to this binder; wrap in Pi
            result_ty = self.ctx.mk_pi(binder_name, binder_style, binder_type, result_ty);
        }
        result_ty
    }

    fn infer_pi(&mut self, mut e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let mut universes = Vec::new();
        let depth0 = self.local_ctx.len();
        while let Pi { binder_type, body, .. } = self.ctx.view_expr(e) {
            let dom_univ = self.infer_sort_of(binder_type, flag);
            universes.push(dom_univ);
            self.push_local(binder_type);
            e = body;
        }
        // e is now the body of the innermost Pi; infer its sort
        let mut infd = self.infer_sort_of(e, flag);
        // Pop binders in reverse, combining universe levels
        while let Some(universe) = universes.pop() {
            infd = self.ctx.imax(universe, infd);
            self.pop_local();
        }
        assert_eq!(depth0, self.local_ctx.len());
        self.ctx.mk_sort(infd)
    }

    fn infer_let(
        &mut self,
        binder_type: ExprPtr<'t>,
        val: ExprPtr<'t>,
        body: ExprPtr<'t>,
        flag: InferFlag,
    ) -> ExprPtr<'t> {
        if flag == Check {
            // The binder type has to be a type
            self.infer_sort_of(binder_type, flag);
            let val_ty = self.infer(val, flag);
            // assert that the type annotation of the let value is appropriate.
            self.assert_def_eq(val_ty, binder_type);
        }
        let body = self.ctx.inst_beta(body, &[val]);
        self.infer(body, flag)
    }
    
    // Not well tested, used for introspection/debugging.
    #[allow(dead_code)]
    pub(crate) fn strong_reduce(&mut self, e: ExprPtr<'t>, reduce_types: bool, reduce_proofs: bool) -> ExprPtr<'t> {
        if (!reduce_types) || (!reduce_proofs) {
            let ty = self.infer(e, InferOnly);
            if !reduce_types && matches!(self.ctx.read_expr(ty), Sort {..}) {
                return e
            }
            if !reduce_proofs && self.is_proposition(ty).0 {
                return e
            }
        }
        let e = self.whnf(e);
        if let Some(cached) = self.tc_cache.strong_cache.get(&(e, reduce_types, reduce_proofs)).copied() {
            return cached
        }

        let out = match self.ctx.view_expr(e) {
            Expr::App {fun, arg, ..} => {
                let f = self.strong_reduce(fun, reduce_types, reduce_proofs);
                let arg = self.strong_reduce(arg, reduce_types, reduce_proofs);
                self.ctx.mk_app(f, arg)
            }
            Expr::Lambda {binder_name, binder_style, binder_type, body, ..} => {
                let binder_type_r = self.strong_reduce(binder_type, reduce_types, reduce_proofs);
                self.push_local(binder_type_r);
                let body_r = self.strong_reduce(body, reduce_types, reduce_proofs);
                self.pop_local();
                self.ctx.mk_lambda(binder_name, binder_style, binder_type_r, body_r)
            }
            Expr::Pi {binder_name, binder_style, binder_type, body, ..} => {
                let binder_type_r = self.strong_reduce(binder_type, reduce_types, reduce_proofs);
                self.push_local(binder_type_r);
                let body_r = self.strong_reduce(body, reduce_types, reduce_proofs);
                self.pop_local();
                self.ctx.mk_pi(binder_name, binder_style, binder_type_r, body_r)
            }
            Expr::Proj {ty_name, idx, structure, ..} => {
                let structure = self.strong_reduce(structure, reduce_types, reduce_proofs);
                let x = self.ctx.mk_proj(ty_name, idx, structure);
                let y = self.whnf(x);
                if y != x {
                    self.strong_reduce(y, reduce_types, reduce_proofs)
                } else {
                    x
                }
                
            }
            _ => e
        };
        self.tc_cache.strong_cache.insert((e, reduce_types, reduce_proofs), out);
        out
    }

    pub fn whnf(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.whnf_inner(e))
    }

    fn whnf_inner(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {

        if matches!(self.ctx.read_expr(e), NatLit { .. } | StringLit { .. }) {
            return e
        }
        // whnf is shift-equivariant: whnf(Shift(e, k, 0)) = shift(whnf(e), k)
        // Peel off cutoff=0 Shift nodes (iteratively). For cutoff>0, force first.
        let mut total_shift: u16 = 0;
        let mut e = e;
        while let Shift { inner, amount, cutoff, .. } = self.ctx.read_expr(e) {
            if cutoff == 0 {
                total_shift += amount;
                e = inner;
            } else {
                // Shallow-force the cutoff>0 shift, then continue peeling
                e = self.ctx.force_shift_shallow(inner, amount, cutoff);
            }
        }
        if total_shift > 0 {
            let r = self.whnf(e);
            return self.ctx.force_shift_shallow(r, total_shift, 0);
        }
        // Shift-invariant cache: keyed by canonical hash.
        // On hit, verify structural equality up to shift, then apply delta.
        let canon = self.ctx.canonical_hash(e);
        let e_bvar_ub = self.ctx.num_loose_bvars(e);
        if let Some(&(stored_input, stored_result, stored_bvar_ub)) = self.tc_cache.whnf_cache.get(&canon) {
            // Fast path: exact pointer match (no shift_eq needed)
            if stored_input == e {
                return stored_result;
            }
            if false && e_bvar_ub >= stored_bvar_ub {
                let delta = e_bvar_ub - stored_bvar_ub;
                if delta > 0 && self.ctx.shift_eq(stored_input, e, delta) {
                    return self.ctx.force_shift_shallow(stored_result, delta, 0);
                }
            }
        }
        let mut cursor = e;
        loop {
            let whnfd = self.whnf_no_unfolding(cursor);
            if let Some(reduce_nat_ok) = self.try_reduce_nat(whnfd) {
                cursor = reduce_nat_ok;
            } else if let Some(next_term) = self.unfold_def(whnfd) {
                cursor = next_term;
            } else {
                // Only store if no entry exists or if this bvar_ub is smaller (better for future shift hits)
                if self.tc_cache.whnf_cache.get(&canon).map_or(true, |&(_, _, stored_bvar_ub)| e_bvar_ub < stored_bvar_ub) {
                    self.tc_cache.whnf_cache.insert(canon, (e, whnfd, e_bvar_ub));
                }
                return whnfd
            }
        }
    }

    fn whnf_no_unfolding_cheap_proj(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> { self.whnf_no_unfolding_aux(e, true) }

    pub fn whnf_no_unfolding(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> { self.whnf_no_unfolding_aux(e, false) }

    fn whnf_no_unfolding_aux(&mut self, e: ExprPtr<'t>, cheap_proj: bool) -> ExprPtr<'t> {
        // whnf_no_unfolding is shift-equivariant: peel top-level Shifts.
        let mut total_shift: u16 = 0;
        let mut e = e;
        while let Shift { inner, amount, cutoff, .. } = self.ctx.read_expr(e) {
            if cutoff == 0 {
                total_shift += amount;
                e = inner;
            } else {
                e = self.ctx.force_shift_shallow(inner, amount, cutoff);
            }
        }
        if total_shift > 0 {
            let r = self.whnf_no_unfolding_aux(e, cheap_proj);
            return self.ctx.force_shift_shallow(r, total_shift, 0);
        }
        // Iterative version: tail-recursive calls become loop iterations.
        // We track original inputs to cache on exit.
        let mut cache_entries: Vec<ExprPtr<'t>> = Vec::new();
        let mut cur = e;
        let result = loop {
            // Shift-invariant cache lookup: canonical hash keyed.
            let cur_canon = self.ctx.canonical_hash(cur);
            let cur_bvar_ub = self.ctx.num_loose_bvars(cur);
            if let Some(&(stored_input, stored_result, stored_bvar_ub)) = self.tc_cache.whnf_no_unfolding_cache.get(&cur_canon) {
                if stored_input == cur {
                    break stored_result;
                }
                if cur_bvar_ub >= stored_bvar_ub {
                    let delta = cur_bvar_ub - stored_bvar_ub;
                    if delta > 0 && self.ctx.shift_eq(stored_input, cur, delta) {
                        let shifted = self.ctx.force_shift_shallow(stored_result, delta, 0);
                        break shifted;
                    }
                }
            }
            let (e_fun, args) = self.ctx.unfold_apps(cur);
            match self.ctx.read_expr(e_fun) {
                Proj { idx, structure, .. } =>
                    if let Some(e) = self.reduce_proj(idx, structure, cheap_proj) {
                        let next = self.ctx.foldl_apps(e, args.into_iter());
                        if !cheap_proj { cache_entries.push(cur); }
                        cur = next;
                        continue;
                    } else {
                        break self.ctx.foldl_apps(e_fun, args.into_iter());
                    },
                Sort { level, .. } => {
                    debug_assert!(args.is_empty());
                    let level = self.ctx.simplify(level);
                    break self.ctx.mk_sort(level);
                }
                Lambda { .. } if !args.is_empty() => {
                    let (mut e, mut n_args) = (e_fun, 0usize);
                    while let (Lambda { body, .. }, [_arg, _rest @ ..]) = (self.ctx.view_expr(e), &args[n_args..]) {
                        n_args += 1;
                        e = body;
                    }
                    e = self.ctx.inst_beta(e, &args[..n_args]);
                    let next = self.ctx.foldl_apps(e, args.into_iter().skip(n_args));
                    if !cheap_proj { cache_entries.push(cur); }
                    cur = next;
                    continue;
                }
                Lambda { .. } => {
                    debug_assert!(args.is_empty());
                    break self.ctx.foldl_apps(e_fun, args.into_iter());
                }
                Let { val, body, .. } => {
                    let e = self.ctx.inst_beta(body, &[val]);
                    let next = self.ctx.foldl_apps(e, args.into_iter());
                    if !cheap_proj { cache_entries.push(cur); }
                    cur = next;
                    continue;
                }
                Const { name, levels, .. } =>
                    if let Some(reduced) = self.reduce_quot(name, &args) {
                        if !cheap_proj { cache_entries.push(cur); }
                        cur = reduced;
                        continue;
                    } else if let Some(reduced) = self.reduce_rec(name, levels, &args) {
                        if !cheap_proj { cache_entries.push(cur); }
                        cur = reduced;
                        continue;
                    } else {
                        break self.ctx.foldl_apps(e_fun, args.into_iter());
                    },
                Var { .. } => break self.ctx.foldl_apps(e_fun, args.into_iter()),
                Pi { .. } => {
                    debug_assert!(args.is_empty());
                    break e_fun;
                }
                App { .. } => panic!(),
                Local { .. } | NatLit { .. } | StringLit { .. } => break self.ctx.foldl_apps(e_fun, args.into_iter()),
                Shift { inner, amount, cutoff, .. } => {
                    let forced = self.ctx.force_shift_shallow(inner, amount, cutoff);
                    let next = self.ctx.foldl_apps(forced, args.into_iter());
                    if !cheap_proj { cache_entries.push(cur); }
                    cur = next;
                    continue;
                }
            }
        };
        // Cache intermediate inputs (non-cheap_proj only).
        if !cheap_proj {
            for entry in cache_entries {
                let entry_canon = self.ctx.canonical_hash(entry);
                let entry_bvar_ub = self.ctx.num_loose_bvars(entry);
                if self.tc_cache.whnf_no_unfolding_cache.get(&entry_canon).map_or(true, |&(_, _, s)| entry_bvar_ub < s) {
                    self.tc_cache.whnf_no_unfolding_cache.insert(entry_canon, (entry, result, entry_bvar_ub));
                }
            }
        }
        result
    }

    fn def_eq_nat(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        if self.ctx.is_nat_zero(x) && self.ctx.is_nat_zero(y) {
            return Some(true)
        }
        if let (NatLit { .. }, NatLit { .. }) = (self.ctx.read_expr(x), self.ctx.read_expr(y)) {
            assert!(self.ctx.export_file.config.nat_extension);
            return Some(x == y)
        }
        if let (Some(x_pred), Some(y_pred)) = (self.ctx.pred_of_nat_succ(x), self.ctx.pred_of_nat_succ(y)) {
            Some(self.def_eq(x_pred, y_pred))
        } else {
            None
        }
    }

    fn def_eq_binder_multi(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        if matches!(self.ctx.read_expr_pair(x, y), (Pi { .. }, Pi { .. }) | (Lambda { .. }, Lambda { .. })) {
            self.def_eq_binder_aux(x, y)
        } else {
            None
        }
    }

    fn def_eq_binder_aux(&mut self, mut x: ExprPtr<'t>, mut y: ExprPtr<'t>) -> Option<bool> {
        let depth0 = self.local_ctx.len();
        while let (
            Pi { binder_type: t1, body: body1, .. },
            Pi { binder_type: t2, body: body2, .. },
        )
        | (
            Lambda { binder_type: t1, body: body1, .. },
            Lambda { binder_type: t2, body: body2, .. },
        ) = self.ctx.view_expr_pair(x, y)
        {
            if self.def_eq(t1, t2) {
                self.push_local(t1);
                x = body1;
                y = body2;
            } else {
                self.restore_depth(depth0);
                return Some(false)
            }
        }

        let r = self.def_eq(x, y);
        self.restore_depth(depth0);
        Some(r)
    }

    fn def_eq_proj(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        match self.ctx.read_expr_pair(x, y) {
            (Proj { idx: idx_l, structure: structure_l, .. }, Proj { idx: idx_r, structure: structure_r, .. }) =>
                idx_l == idx_r && self.def_eq(structure_l, structure_r),
            _ => false,
        }
    }

    fn def_eq_local(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        match self.ctx.read_expr_pair(x, y) {
            // Pure de Bruijn: two Vars are equal iff same index
            (Var { dbj_idx: x_idx, .. }, Var { dbj_idx: y_idx, .. }) =>
                x_idx == y_idx,
            (Local { id: x_id, binder_type: tx, .. }, Local { id: y_id, binder_type: ty, .. }) =>
                x_id == y_id && self.def_eq(tx, ty),
            _ => false,
        }
    }
    fn def_eq_const(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        match self.ctx.read_expr_pair(x, y) {
            (Const { name: x_name, levels: x_levels, .. }, Const { name: y_name, levels: y_levels, .. }) =>
                x_name == y_name && self.ctx.eq_antisymm_many(x_levels, y_levels),
            _ => false,
        }
    }

    fn def_eq_app(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        let (f1, args1) = self.ctx.unfold_apps(x);
        if args1.is_empty() {
            return false
        }

        let (f2, args2) = self.ctx.unfold_apps(y);
        if args2.is_empty() {
            return false
        }

        if args1.len() != args2.len() {
            return false
        }

        let args_eq = args1.into_iter().zip(args2).all(|(xx, yy)| self.def_eq(xx, yy));

        if !args_eq {
            return false
        }

        if !self.def_eq(f1, f2) {
            return false
        }
        true
    }

    pub fn assert_def_eq(&mut self, u: ExprPtr<'t>, v: ExprPtr<'t>) { assert!(self.def_eq(u, v)) }

    pub fn def_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.def_eq_inner(x, y))
    }

    fn def_eq_inner(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {

        if let Some(easy) = self.def_eq_quick_check(x, y) {
            return easy
        }

        let x_n = self.whnf_no_unfolding_cheap_proj(x);
        let y_n = self.whnf_no_unfolding_cheap_proj(y);

        if (self.ctx.num_loose_bvars(x_n) == 0 || self.ctx.eager_mode) && Some(y_n) == self.ctx.c_bool_true() {
            let x_nn = self.whnf(x_n);
            if Some(x_nn) == self.ctx.c_bool_true() {
                return true
            }
        }

        if let Some(easy) = self.def_eq_quick_check(x_n, y_n) {
            return easy
        }

        let result = if self.proof_irrel_eq(x_n, y_n) {
            true
        } else {
            match self.lazy_delta_step(x_n, y_n) {
                FoundEqResult(short) => short,
                Exhausted(x_n, y_n) => {
                    if self.def_eq_const(x_n, y_n) || self.def_eq_local(x_n, y_n) || self.def_eq_proj(x_n, y_n) {
                        true
                    } else {
                        let (xn0, yn0) = (x_n, y_n);
                        let (x_n, y_n) = (self.whnf_no_unfolding(xn0), self.whnf_no_unfolding(yn0));
                        if x_n != xn0 || y_n != yn0 {
                            self.def_eq(x_n, y_n)
                        } else {
                            self.def_eq_app(x_n, y_n)
                                || self.try_eta_expansion(x_n, y_n)
                                || self.try_eta_struct(x_n, y_n)
                                || self.try_string_lit_expansion(x_n, y_n)
                                || matches!(self.def_eq_unit(x_n, y_n), Some(true))
                        }
                    }
                }
            }
        };
        if result {
            self.tc_cache.eq_cache.union(x, y);
            self.defeq_open_store_pos(x, y);
        }
        result
    }

    fn mk_nullary_ctor(&mut self, e: ExprPtr<'t>, num_params: usize) -> Option<ExprPtr<'t>> {
        let (_fun, name, levels, args) = self.ctx.unfold_const_apps(e)?;
        let InductiveData { all_ctor_names, .. } = self.env.get_inductive(&name)?;
        let ctor_name = all_ctor_names[0];
        let new_const = self.ctx.mk_const(ctor_name, levels);
        let args = args.into_iter().take(num_params);
        Some(self.ctx.foldl_apps(new_const, args))
    }

    fn to_ctor_when_k(
        &mut self,
        major: ExprPtr<'t>,
        rec: &RecursorData<'t>,
    ) -> Option<ExprPtr<'t>> {
        if !rec.is_k {
            return None
        }
        let major_ty = self.infer_then_whnf(major, InferOnly);
        let f = self.ctx.unfold_apps_fun(major_ty);
        match (self.ctx.read_expr(f), self.ctx.get_major_induct(rec)) {
            (Const { name, .. }, Some(n)) if name == n => {
                let new_ctor_app = self.mk_nullary_ctor(major_ty, rec.num_params as usize)?;
                // This sometimes has free variables.
                let new_type = self.infer(new_ctor_app, InferOnly);
                if self.def_eq(major_ty, new_type) {
                    Some(new_ctor_app)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn is_ctor_app(&mut self, e: ExprPtr<'t>) -> Option<NamePtr<'t>> {
        let f = self.ctx.unfold_apps_fun(e);
        if let Const { name, .. } = self.ctx.read_expr(f) {
            if let Some(Declar::Constructor { .. }) = self.env.get_declar(&name) {
                return Some(name)
            }
        }
        None
    }

    fn iota_try_eta_struct(&mut self, ind_name: NamePtr<'t>, e: ExprPtr<'t>) -> ExprPtr<'t> {
        if (!self.env.can_be_struct(&ind_name)) || self.is_ctor_app(e).is_some() {
            e
        } else {
            let e_type = self.infer_then_whnf(e, InferOnly);
            let e_type_f = self.ctx.unfold_apps_fun(e_type);
            match self.ctx.read_expr(e_type_f) {
                Const { name, .. } if name == ind_name => {
                    let e_sort = self.infer_then_whnf(e_type, InferOnly);
                    // If it's a prop, return the original `e`
                    if e_sort == self.ctx.prop() {
                        e
                    } else {
                        // if it's not a prop, try to eta expand
                        self.expand_eta_struct_aux(e_type, e).unwrap_or(e)
                    }
                }
                _ => e,
            }
        }
    }
    
    fn reduce_rec(
        &mut self,
        const_name: NamePtr<'t>,
        const_levels: LevelsPtr<'t>,
        args: &[ExprPtr<'t>],
    ) -> Option<ExprPtr<'t>> {
        let rec @ RecursorData { info, rec_rules, num_params, num_motives, num_minors, .. } =
            self.env.get_recursor(&const_name)?;
        let major = args.get(rec.major_idx()).copied()?;
        let major = self.to_ctor_when_k(major, rec).unwrap_or(major);
        let major = self.whnf(major);
        let major = match self.ctx.view_expr(major) {
            NatLit { ptr, .. } => self.ctx.nat_lit_to_constructor(ptr).unwrap_or(major),
            StringLit { ptr, .. } => self.str_lit_to_ctor_reducing(ptr).unwrap_or(major),
            _ => {
                let ind_rec_name_prefix = self.ctx.get_major_induct(rec).unwrap();
                self.iota_try_eta_struct(ind_rec_name_prefix, major)
            }
        };
        let (major_ctor, major_ctor_args) = self.ctx.unfold_apps(major);
        let rec_rule = self.get_rec_rule(rec_rules, major_ctor)?;

        // The number of parameters in the constructor is not necessarily
        // equal to the number of parameters in the recursor when we have
        // nested inductive types.
        let num_extra_params_to_major =
            major_ctor_args.len().checked_sub(rec_rule.ctor_telescope_size_wo_params as usize).unwrap();
        let major_ctor_args_wo_params = major_ctor_args.into_iter().skip(num_extra_params_to_major).collect::<Vec<_>>();
        let r = self.ctx.subst_expr_levels(rec_rule.val, info.uparams, const_levels);
        let r = self.ctx.foldl_apps(r, args.iter().copied().take((num_params + num_motives + num_minors) as usize));
        let r = self.ctx.foldl_apps(r, major_ctor_args_wo_params.into_iter());
        Some(self.ctx.foldl_apps(r, args.iter().skip(rec.major_idx() + 1).copied()))
    }

    pub fn reduce_quot(&mut self, c_name: NamePtr<'t>, args: &[ExprPtr<'t>]) -> Option<ExprPtr<'t>> {
        if !matches!(self.env.get_declar(&c_name), Some(Declar::Quot {..})) {
            return None
        }
        let (qmk, rest_idx) = if c_name == self.ctx.export_file.name_cache.quot_lift? {
            let qmk = args.get(5).copied()?;
            (self.whnf(qmk), 6)
        } else if c_name == self.ctx.export_file.name_cache.quot_ind? {
            let qmk = args.get(4).copied()?;
            (self.whnf(qmk), 5)
        } else {
            return None
        };
        {
            let (qmk_const, qmk_args) = self.ctx.unfold_apps(qmk);
            match self.ctx.read_expr(qmk_const) {
                Const { name, .. } if name == self.ctx.export_file.name_cache.quot_mk? && qmk_args.len() == 3 => (),
                _ => return None,
            };
        }
        let f = args.get(3).copied()?;
        let appd = match self.ctx.view_expr(qmk) {
            App { arg, .. } => self.ctx.mk_app(f, arg),
            _ => panic!("Quot iota"),
        };
        Some(self.ctx.foldl_apps(appd, args.iter().copied().skip(rest_idx)))
    }

    // We only need the name and reducibility from this.
    fn get_applied_def(&mut self, e: ExprPtr<'t>) -> Option<(NamePtr<'t>, ReducibilityHint)> {
        let f = self.ctx.unfold_apps_fun(e);
        if let Const { name, .. } = self.ctx.read_expr(f) {
            if let Some(Declar::Definition { info, hint, .. }) = self.env.get_declar(&name) {
                return Some((info.name, *hint))
            } else if let Some(Declar::Theorem { info, .. }) = self.env.get_declar(&name) {
                return Some((info.name, ReducibilityHint::Opaque))
            }
        }
        None
    }

    /// For an expression already known to be an applied definition, unfold
    /// the definition and perform cheap reduction on the unfolded result.
    fn delta(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        let unfolded = self.unfold_def(e).unwrap();
        self.whnf_no_unfolding_cheap_proj(unfolded)
    }

    /// Try to unfold the base `Const` and re-fold applications, but don't
    /// do any further reduction.
    fn unfold_def(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        let (fun, args) = self.ctx.unfold_apps(e);
        let (name, levels) = self.ctx.try_const_info(fun)?;
        let (def_uparams, def_value) = self.env.get_declar_val(&name)?;
        if self.ctx.read_levels(levels).len() == self.ctx.read_levels(def_uparams).len() {
            let def_val = self.ctx.subst_expr_levels(def_value, def_uparams, levels);
            Some(self.ctx.foldl_apps(def_val, args.into_iter()))
        } else {
            None
        }
    }

    fn def_eq_sort(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        match self.ctx.read_expr_pair(x, y) {
            (Sort { level: l, .. }, Sort { level: r, .. }) => Some(self.ctx.eq_antisymm(l, r)),
            _ => None,
        }
    }

    fn def_eq_quick_check(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        if x == y {

            return Some(true)
        }
        // Strip matching Shift wrappers: Shift(a, k, c) == Shift(b, k, c) iff a == b
        if let (Shift { inner: ix, amount: kx, cutoff: cx, .. }, Shift { inner: iy, amount: ky, cutoff: cy, .. }) =
            (self.ctx.read_expr(x), self.ctx.read_expr(y))
        {
            if kx == ky && cx == cy {
                return Some(self.def_eq(ix, iy))
            }
        }
        // Check if one side is a shift of the other (non-allocating structural comparison)
        match (self.ctx.read_expr(x), self.ctx.read_expr(y)) {
            (Shift { inner, amount, cutoff: 0, .. }, _) => {
                if self.ctx.shift_eq(inner, y, amount) {
                    return Some(true)
                }
            }
            (_, Shift { inner, amount, cutoff: 0, .. }) => {
                if self.ctx.shift_eq(inner, x, amount) {
                    return Some(true)
                }
            }
            _ => {}
        }
        if self.tc_cache.eq_cache.check_uf_eq(x, y) {
            return Some(true)
        }
        // Shift-invariant positive def_eq cache for open expressions
        if self.defeq_open_lookup(&self.tc_cache.defeq_pos_open, x, y) {
            return Some(true)
        }
        if let Some(r) = self.def_eq_sort(x, y) {
            return Some(r)
        }
        if let Some(r) = self.def_eq_binder_multi(x, y) {
            return Some(r)
        }
        None
    }

    fn failure_cache_contains(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        let pr = if x.get_hash() <= y.get_hash() { (x, y) } else { (y, x) };
        if self.tc_cache.failure_cache.contains(&pr) {
            return true;
        }
        if self.defeq_open_lookup(&self.tc_cache.defeq_neg_open, x, y) {
            return true;
        }
        false
    }

    fn failure_cache_insert(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        let pr = if x.get_hash() <= y.get_hash() { (x, y) } else { (y, x) };
        self.tc_cache.failure_cache.insert(pr);
        self.defeq_open_store_neg(x, y);
    }

    /// Compute bucket index for shift-invariant def_eq cache.
    /// Returns None if both expressions are closed (use global cache instead).
    fn defeq_bucket_idx(&self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<usize> {
        let depth = self.local_ctx.len() as u16;
        let x_nlbv = self.ctx.num_loose_bvars(x);
        let y_nlbv = self.ctx.num_loose_bvars(y);
        if x_nlbv == 0 && y_nlbv == 0 {
            return None;
        }
        if depth == 0 {
            return None;
        }
        // Use u16::MAX for closed expressions so they don't constrain the bucket
        let x_lb = if x_nlbv > 0 { self.ctx.fvar_lb(self.ctx.read_expr(x).get_fvar_list()) } else { u16::MAX };
        let y_lb = if y_nlbv > 0 { self.ctx.fvar_lb(self.ctx.read_expr(y).get_fvar_list()) } else { u16::MAX };
        let min_lb = x_lb.min(y_lb);
        Some((depth - 1 - min_lb) as usize)
    }

    /// Ordered canonical hash key for a pair of expressions.
    fn defeq_canon_key(&self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> (((u64, u64), (u64, u64)), bool) {
        let cx = self.ctx.canonical_hash(x);
        let cy = self.ctx.canonical_hash(y);
        if cx <= cy {
            ((cx, cy), false)
        } else {
            ((cy, cx), true)
        }
    }

    /// Look up in a shift-invariant def_eq cache (positive or negative).
    fn defeq_open_lookup(
        &self,
        cache: &[FxHashMap<((u64, u64), (u64, u64)), (ExprPtr<'t>, ExprPtr<'t>, u16)>],
        x: ExprPtr<'t>,
        y: ExprPtr<'t>,
    ) -> bool {
        let Some(bucket_idx) = self.defeq_bucket_idx(x, y) else { return false };
        let Some(bucket) = cache.get(bucket_idx) else { return false };
        let (key, swapped) = self.defeq_canon_key(x, y);
        let Some(&(stored_a, stored_b, stored_depth)) = bucket.get(&key) else { return false };
        let depth = self.local_ctx.len() as u16;
        let (qx, qy) = if swapped { (y, x) } else { (x, y) };
        // Exact match
        if stored_a == qx && stored_b == qy && stored_depth == depth {
            return true;
        }
        // Shift-invariant match
        if depth >= stored_depth {
            let delta = depth - stored_depth;
            if delta > 0 {
                if self.ctx.shift_eq(stored_a, qx, delta) && self.ctx.shift_eq(stored_b, qy, delta) {
                    return true;
                }
                // Try swapped assignment if canonical hashes are equal
                if self.ctx.canonical_hash(x) == self.ctx.canonical_hash(y)
                    && self.ctx.shift_eq(stored_a, qy, delta)
                    && self.ctx.shift_eq(stored_b, qx, delta)
                {
                    return true;
                }
            }
        }
        false
    }

    /// Store in a shift-invariant def_eq cache (positive or negative).
    fn defeq_open_store_pos(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        Self::defeq_open_store_impl(self.ctx, &mut self.tc_cache.defeq_pos_open, &self.local_ctx, x, y);
    }

    fn defeq_open_store_neg(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        Self::defeq_open_store_impl(self.ctx, &mut self.tc_cache.defeq_neg_open, &self.local_ctx, x, y);
    }

    fn defeq_open_store_impl(
        ctx: &mut TcCtx<'t, 'p>,
        cache: &mut Vec<FxHashMap<((u64, u64), (u64, u64)), (ExprPtr<'t>, ExprPtr<'t>, u16)>>,
        local_ctx: &[ExprPtr<'t>],
        x: ExprPtr<'t>,
        y: ExprPtr<'t>,
    ) {
        let depth = local_ctx.len() as u16;
        let x_nlbv = ctx.num_loose_bvars(x);
        let y_nlbv = ctx.num_loose_bvars(y);
        if x_nlbv == 0 && y_nlbv == 0 { return; }
        if depth == 0 { return; }
        let x_lb = if x_nlbv > 0 { ctx.fvar_lb(ctx.read_expr(x).get_fvar_list()) } else { u16::MAX };
        let y_lb = if y_nlbv > 0 { ctx.fvar_lb(ctx.read_expr(y).get_fvar_list()) } else { u16::MAX };
        let min_lb = x_lb.min(y_lb);
        let bucket_idx = (depth - 1 - min_lb) as usize;
        let cx = ctx.canonical_hash(x);
        let cy = ctx.canonical_hash(y);
        let (key, swapped) = if cx <= cy { ((cx, cy), false) } else { ((cy, cx), true) };
        let (sx, sy) = if swapped { (y, x) } else { (x, y) };
        if let Some(bucket) = cache.get_mut(bucket_idx) {
            if bucket.get(&key).map_or(true, |&(_, _, sd)| depth < sd) {
                bucket.insert(key, (sx, sy, depth));
            }
        }
    }

    fn try_eq_const_app(
        &mut self,
        x: ExprPtr<'t>,
        x_defname: NamePtr<'t>,
        x_hint: ReducibilityHint,
        y: ExprPtr<'t>,
        y_defname: NamePtr<'t>,
        y_hint: ReducibilityHint,
    ) -> Option<DeltaResult<'t>> {
        if x_defname != y_defname {
            return None
        }
        if !matches!((x_hint, y_hint), (ReducibilityHint::Regular(..), ReducibilityHint::Regular(..))) {
            return None
        }
        if x_hint != y_hint {
            return None
        }
        if self.failure_cache_contains(x, y) {
            return None
        }

        match self.ctx.read_expr_pair(x, y) {
            (App { .. }, App { .. }) if (x_defname == y_defname) => {
                let (l_fun, l_args) = self.ctx.unfold_apps(x);
                let (r_fun, r_args) = self.ctx.unfold_apps(y);
                match self.ctx.read_expr_pair(l_fun, r_fun) {
                    (Const { levels: l_levels, .. }, Const { levels: r_levels, .. })
                        if l_args.len() == r_args.len()
                            && !self.failure_cache_contains(x, y)
                            && l_args.iter().copied().zip(r_args.iter().copied()).all(|(x, y)| self.def_eq(x, y))
                            && self.ctx.eq_antisymm_many(l_levels, r_levels) =>
                        Some(FoundEqResult(true)),
                    (Const { .. }, Const { .. }) => {
                        self.failure_cache_insert(x, y);
                        None
                    }
                    _ => panic!(),
                }
            }
            _ => None,
        }
    }

    fn try_unfold_proj_app(&mut self, e: ExprPtr<'t>) -> Option<ExprPtr<'t>> {
        let f = self.ctx.unfold_apps_fun(e);
        if let Proj { .. } = self.ctx.read_expr(f) {
            let eprime = self.whnf_no_unfolding(e);
            if eprime != e {
                return Some(eprime)
            }
        }
        None
    }

    fn delta_try_nat(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<DeltaResult<'t>> {
        if let Some(short) = self.def_eq_nat(x, y) {
            return Some(DeltaResult::FoundEqResult(short))
        }
        if (self.ctx.num_loose_bvars(x) == 0 && self.ctx.num_loose_bvars(y) == 0) || self.ctx.eager_mode {
            if let Some(xprime) = self.try_reduce_nat(x) {
                return Some(DeltaResult::FoundEqResult(self.def_eq(xprime, y)))
            } else if let Some(yprime) = self.try_reduce_nat(y) {
                return Some(DeltaResult::FoundEqResult(self.def_eq(x, yprime)))
            }
        }
        None
    }

    /// If `x` and/or `y` are definitions that need to be unfolded, try to lazily unfold
    /// the "higher" definition to bring it closer to the lower one. Also try to efficiently
    /// check for congruence if `x` and `y` apply the same definitions.
    ///
    /// After each reduction, check whether we can show definitional equality without having
    /// to continue unfolding.
    fn lazy_delta_step(&mut self, mut x: ExprPtr<'t>, mut y: ExprPtr<'t>) -> DeltaResult<'t> {
        loop {
            if let Some(r) = self.delta_try_nat(x, y) {
                return r
            }
            let (r1, r2) = (self.get_applied_def(x), self.get_applied_def(y));
            match (r1, r2) {
                (None, None) => return Exhausted(x, y),
                (Some(..), None) =>
                    if let Some(yprime) = self.try_unfold_proj_app(y) {
                        y = yprime;
                    } else {
                        x = self.delta(x);
                    },
                (None, Some(..)) =>
                    if let Some(xprime) = self.try_unfold_proj_app(x) {
                        x = xprime;
                    } else {
                        y = self.delta(y);
                    },
                (Some((_, l_hint)), Some((_, r_hint))) if l_hint.is_lt(&r_hint) => {
                    y = self.delta(y);
                }
                (Some((_, l_hint)), Some((_, r_hint))) if r_hint.is_lt(&l_hint) => {
                    x = self.delta(x);
                }
                (Some((x_name, l_hint)), Some((y_name, r_hint))) => {
                    if let Some(r) = self.try_eq_const_app(x, x_name, l_hint, y, y_name, r_hint) {
                        return r
                    } else {
                        x = self.delta(x);
                        y = self.delta(y);
                    }
                }
            }
            if let Some(quick_result) = self.def_eq_quick_check(x, y) {
                return FoundEqResult(quick_result)
            }
        }
    }

    pub fn is_sort_zero(&mut self, e: ExprPtr<'t>) -> bool {
        let e = self.whnf(e);
        match self.ctx.view_expr(e) {
            Sort { level, .. } => self.ctx.read_level(level) == Level::Zero,
            _ => false,
        }
    }
    pub fn is_proposition(&mut self, e: ExprPtr<'t>) -> (bool, ExprPtr<'t>) {
        let infd = self.infer(e, InferOnly);
        (self.is_sort_zero(infd), infd)
    }

    pub fn is_proof(&mut self, e: ExprPtr<'t>) -> (bool, ExprPtr<'t>) {
        let infd = self.infer(e, InferOnly);
        (self.is_proposition(infd).0, infd)
    }

    fn proof_irrel_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        match self.is_proof(x) {
            (false, _) => false,
            (true, l_type) => match self.is_proof(y) {
                (false, _) => false,
                (true, r_type) => self.def_eq(l_type, r_type),
            },
        }
    }

    fn try_eta_expansion(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        self.try_eta_expansion_aux(x, y) || self.try_eta_expansion_aux(y, x)
    }

    fn try_eta_expansion_aux(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        if let Lambda { .. } = self.ctx.view_expr(x) {
            let y_ty = self.infer_then_whnf(y, InferOnly);
            if let Pi { binder_name, binder_type, binder_style, .. } = self.ctx.view_expr(y_ty) {
                // Shift y up by 1 since it will be placed inside a new lambda body
                let y_shifted = self.ctx.shift_expr(y, 1, 0);
                let v0 = self.ctx.mk_var(0);
                let new_body = self.ctx.mk_app(y_shifted, v0);
                let new_lambda = self.ctx.mk_lambda(binder_name, binder_style, binder_type, new_body);
                return self.def_eq(x, new_lambda)
            }
        }
        false
    }
}
