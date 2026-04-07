use crate::env::ReducibilityHint;
use crate::env::{ConstructorData, Declar, DeclarInfo, Env, InductiveData, RecRule, RecursorData};
use crate::expr::Expr;
use crate::level::Level;
use crate::util::{
    nat_div, nat_mod, nat_sub, nat_gcd, nat_land, nat_lor,
    nat_xor, nat_shr, nat_shl, CacheKey, ExportFile, ExprPtr, LevelPtr,
    LevelsPtr, NamePtr, TcCache, TcCtx, StringPtr, WhnfSlot
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
    // Local context + per-depth caches are now bundled in tc_cache.frames.
}

impl<'p> ExportFile<'p> {
    /// The entry point for checking a declaration `d`.
    pub fn check_declar(&self, d: &Declar<'p>) -> crate::util::TcTrace {
        if self.config.use_nanoda_tc {
            self.check_declar_nanoda(d)
        } else {
            self.check_declar_shift(d, crate::util::ReusableCaches::new()).0
        }
    }

    /// Check using our shift-based TC, reusing pre-allocated caches.
    fn check_declar_shift(&self, d: &Declar<'p>, reusable: crate::util::ReusableCaches) -> (crate::util::TcTrace, crate::util::ReusableCaches) {
        use Declar::*;
        match d {
            Axiom { .. } => {
                let (r, reusable) = self.with_tc_and_declar_reusing(*d.info(), reusable, |tc| tc.check_declar_info(d).unwrap());
                (r.1, reusable)
            }
            Inductive(..) => { self.check_inductive_declar(d); (crate::util::TcTrace::default(), reusable) },
            Quot { .. } => { self.with_ctx(|ctx| crate::quot::check_quot(ctx, d)); (crate::util::TcTrace::default(), reusable) },
            Definition { val, .. } | Theorem { val, .. } | Opaque { val, .. } => {
                let (r, reusable) = self.with_tc_and_declar_reusing(*d.info(), reusable, |tc| {
                    tc.check_declar_info(d).unwrap();
                    let inferred_type = tc.infer(*val, crate::tc::InferFlag::Check);
                    tc.assert_def_eq(inferred_type, d.info().ty);
                });
                (r.1, reusable)
            }
            Constructor(ctor_data) => {
                let (r, reusable) = self.with_tc_and_declar_reusing(*d.info(), reusable, |tc| tc.check_declar_info(d).unwrap());
                assert!(self.declars.get(&ctor_data.inductive_name).is_some());
                (r.1, reusable)
            }
            Recursor(recursor_data) => {
                let (r, reusable) = self.with_tc_and_declar_reusing(*d.info(), reusable, |tc| tc.check_declar_info(d).unwrap());
                for ind_name in recursor_data.all_inductives.iter() {
                    assert!(self.declars.get(ind_name).is_some())
                }
                (r.1, reusable)
            }
        }
    }

    /// Check using nanoda's original locally-nameless TC.
    fn check_declar_nanoda(&self, d: &Declar<'p>) -> crate::util::TcTrace {
        use Declar::*;
        match d {
            Axiom { .. } => self.with_nanoda_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap()).1,
            Inductive(..) => { self.check_inductive_declar(d); crate::util::TcTrace::default() },
            Quot { .. } => { self.with_ctx(|ctx| crate::quot::check_quot(ctx, d)); crate::util::TcTrace::default() },
            Definition { val, .. } | Theorem { val, .. } | Opaque { val, .. } =>
                self.with_nanoda_tc_and_declar(*d.info(), |tc| {
                    tc.check_declar_info(d).unwrap();
                    let inferred_type = tc.infer(*val, crate::nanoda_tc::InferFlag::Check);
                    tc.assert_def_eq(inferred_type, d.info().ty);
                }).1,
            Constructor(ctor_data) => {
                let trace = self.with_nanoda_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap()).1;
                assert!(self.declars.get(&ctor_data.inductive_name).is_some());
                trace
            }
            Recursor(recursor_data) => {
                let trace = self.with_nanoda_tc_and_declar(*d.info(), |tc| tc.check_declar_info(d).unwrap()).1;
                for ind_name in recursor_data.all_inductives.iter() {
                    assert!(self.declars.get(ind_name).is_some())
                }
                trace
            }
        }
    }

    /// Check all declarations in this export file using a single thread.
    /// Returns the number of declarations that panicked (type-check errors).
    pub(crate) fn check_all_declars_serial(&self) -> usize {
        let total = self.declars.len();
        let start = std::time::Instant::now();
        let mut last_report = start;
        let max_decl = self.config.max_declarations;
        let skip_decl = self.config.skip_declarations;
        let timeout_secs = self.config.declaration_timeout_secs;
        let mut skipped_count = 0usize;
        let mut reusable = crate::util::ReusableCaches::new();
        for (i, declar) in self.declars.values().enumerate() {
            if max_decl > 0 && i >= max_decl {
                eprintln!("[stopping at {} declarations as configured]", max_decl);
                break;
            }
            if i < skip_decl { continue; }
            let decl_start = std::time::Instant::now();
            if i % 1000 == 0 || (skip_decl > 0 && i == skip_decl) {
                let elapsed = decl_start.duration_since(start).as_millis();
                let delta = decl_start.duration_since(last_report).as_millis();
                eprintln!("[{}/{} {}ms +{}ms]", i, total, elapsed, delta);
                last_report = decl_start;
            }
            let trace;
            if self.config.use_nanoda_tc {
                trace = self.check_declar_nanoda(declar);
            } else if timeout_secs > 0 {
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    self.check_declar_shift(declar, reusable)
                }));
                match result {
                    Err(_) => {
                        self.with_ctx(|ctx| {
                            eprintln!("  PANIC #{}: {:?} (skipping)", i, ctx.debug_print(declar.info().name));
                        });
                        reusable = crate::util::ReusableCaches::new();
                        skipped_count += 1;
                        continue;
                    }
                    Ok((t, r)) => { trace = t; reusable = r; }
                }
            } else {
                let (t, r) = self.check_declar_shift(declar, reusable);
                trace = t;
                reusable = r;
            }
            let decl_time = decl_start.elapsed().as_millis();
            if decl_time > 0 {
                self.with_ctx(|ctx| {
                    eprintln!("  SLOW #{}: {:?} took {}ms | {}", i, ctx.debug_print(declar.info().name), decl_time, trace);
                });
            }
        }
        if skipped_count > 0 {
            eprintln!("[WARNING: {} declarations panicked and were skipped]", skipped_count);
        }
        skipped_count
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
                        .spawn_scoped(sco, || {
                            let mut reusable = crate::util::ReusableCaches::new();
                            loop {
                                let idx = task_num.fetch_add(1, Relaxed);
                                if let Some((_, declar)) = self.declars.get_index(idx) {
                                    if self.config.use_nanoda_tc {
                                        let _ = self.check_declar_nanoda(declar);
                                    } else {
                                        let (_, r) = self.check_declar_shift(declar, reusable);
                                        reusable = r;
                                    }
                                } else {
                                    break
                                }
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
    /// Returns the number of declarations that panicked (type-check errors).
    pub fn check_all_declars(&self) -> usize {
        if self.config.num_threads > 1 {
            self.check_all_declars_par(self.config.num_threads);
            0 // par mode doesn't track panics yet
        } else {
            self.check_all_declars_serial()
        }
    }
}

impl<'x, 't: 'x, 'p: 't> TypeChecker<'x, 't, 'p> {
    pub fn new(dag: &'x mut TcCtx<'t, 'p>, env: &'x Env<'x, 't>, declar_info: Option<DeclarInfo<'t>>) -> Self {
        Self { ctx: dag, env, tc_cache: TcCache::new(), declar_info }
    }

    /// Current binding depth.
    fn depth(&self) -> usize { self.tc_cache.depth() }

    /// Look up the type of Var(k) in the local context, shifting it to be valid at
    /// the current depth.
    fn lookup_var(&mut self, dbj_idx: u16) -> ExprPtr<'t> {
        let ty = self.tc_cache.local_type(dbj_idx);
        self.ctx.shift_expr(ty, dbj_idx + 1, 0)
    }

    /// Look up the value of a let-bound Var(k), shifted to be valid at current depth.
    /// Returns None for lambda/pi binders.
    fn lookup_var_value(&mut self, dbj_idx: u16) -> Option<ExprPtr<'t>> {
        let val = self.tc_cache.local_value(dbj_idx)?;
        Some(self.ctx.shift_expr(val, dbj_idx + 1, 0))
    }

    /// Push a lambda/pi binder onto the local context.
    fn push_local(&mut self, ty: ExprPtr<'t>) {
        self.tc_cache.push_local(ty);
    }

    /// Push a let-binding onto the local context (type + value).
    fn push_local_let(&mut self, ty: ExprPtr<'t>, val: ExprPtr<'t>) {
        self.tc_cache.push_local_let(ty, val);
    }

    /// Pop a binder from the local context (exiting a binder).
    fn pop_local(&mut self) {
        self.tc_cache.pop_local();
    }

    /// Restore local context to a previous depth.
    fn restore_depth(&mut self, depth: usize) {
        self.tc_cache.restore_depth(depth);
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
                panic!("infer_sort_of: expected Sort, got {:?} from e={:?}, infer={:?}, depth={}", self.ctx.debug_print(whnfd), self.ctx.debug_print(e), self.ctx.debug_print(ty), self.depth());
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
            other => panic!("Ran out of constructor telescope getting field: ty_name={:?}, struct_ty_name={:?}, idx={}, num_params={}, struct_ty={:?}, ctor_ty_whnf={:?}, variant={}",
                self.ctx.debug_print(_ty_name), self.ctx.debug_print(struct_ty_name),
                idx, num_params, self.ctx.debug_print(structure_ty), self.ctx.debug_print(reduced),
                match other { Sort {..} => "Sort", Const {..} => "Const", App {..} => "App", Lambda {..} => "Lambda", _ => "other" })
        }
    }

    pub(crate) fn infer(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        self.ctx.trace.infer_calls += 1;
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.infer_inner(e, flag))
    }

    fn infer_inner(&mut self, e: ExprPtr<'t>, flag: InferFlag) -> ExprPtr<'t> {
        let depth = self.depth() as u16;
        // Handle Shift nodes without forcing: infer(Shift(inner, k, 0), d) = mk_shift(infer(inner, d-k), k).
        // Temporarily shrink the context to depth d-k, infer inner, restore, shift result.
        // Only works for cutoff=0 (top-level shifts). For cutoff>0, force first.
        if let Expr::Shift { inner, amount, cutoff, .. } = self.ctx.read_expr(e) {
            if cutoff == 0 && amount > 0 {
                let new_depth = self.depth() - amount as usize;
                self.ctx.trace.infer_shift_peel += 1;
                self.ctx.trace.shift_peel_frames_total += amount as u64;
                let saved = self.tc_cache.split_off(new_depth);
                let inner_type = self.infer(inner, flag);
                self.tc_cache.extend(saved);
                return self.ctx.mk_shift(inner_type, amount);
            } else {
                // Negative shift or non-zero cutoff: force one level and re-infer.
                let forced = self.ctx.push_shift(inner, amount, cutoff);
                return self.infer(forced, flag);
            }
        }
        // Shift-invariant infer cache: bucket 0 for closed, bucket (depth - fvar_lb) for open.
        let depth = self.depth() as u16;
        let bucket_idx = if self.ctx.num_loose_bvars(e) == 0 {
            0
        } else {
            let e_fvl = self.ctx.read_expr(e).get_fvar_list();
            let e_lb = self.ctx.fvar_lb(e_fvl);
            (depth - e_lb) as usize
        };
        let canon = self.ctx.canonical_hash(e);
        let is_check = flag == InferFlag::Check;
        // Infer cache lookup: scan chain.
        let infer_chain = self.tc_cache.infer_cache_chain(bucket_idx, &canon);
        if !infer_chain.is_empty() {
            self.ctx.trace.infer_cache_hash_hit += 1;
            for (ci, &(stored_input, stored_result, stored_depth, checked)) in infer_chain.iter().enumerate() {
                if let Some(r) = self.try_infer_cache_hit(e, stored_input, stored_result, stored_depth, depth, checked, is_check) {
                    self.ctx.trace.infer_cache_hits += 1;
                    if ci > 0 { self.ctx.trace.infer_cache_overflow_hits += 1; }
                    // On same-depth hit: replace entry's input ptr for future ptr_eq lookups.
                    // On above-depth hit: do NOT replace — keep the low-depth canonical entry.
                    if stored_depth == depth && stored_input != e {
                        if let Some(slot) = self.tc_cache.infer_cache_get_mut(bucket_idx, &canon, ci) {
                            *slot = (e, r, depth, is_check || checked);
                        }
                    }
                    return r;
                }
            }
            self.ctx.trace.infer_cache_verify_fail += 1;
        }
        let r = match self.ctx.read_expr(e) {
            Local { binder_type, .. } => binder_type,
            Var { dbj_idx, .. } => {
                self.lookup_var(dbj_idx)
            },
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
        self.infer_cache_store(bucket_idx, canon, e, r, depth, is_check);
        r
    }

    /// Try to match a query against a stored infer cache entry.
    fn try_infer_cache_hit(&mut self, e: ExprPtr<'t>, stored_input: ExprPtr<'t>, stored_result: ExprPtr<'t>, stored_depth: u16, depth: u16, checked: bool, is_check: bool) -> Option<ExprPtr<'t>> {
        // A Check entry can serve both flags; an InferOnly entry can only serve InferOnly.
        if !checked && is_check { return None; }
        if stored_depth == depth {
            if stored_input == e || self.ctx.sem_eq(stored_input, e) {
                return Some(stored_result);
            }
            return None; // caller counts vf_same
        }
        if depth > stored_depth {
            let delta = (depth - stored_depth) as i16;
            if self.ctx.shift_eq(stored_input, e, delta) {
                return Some(self.ctx.mk_shift(stored_result, delta));
            }
            return None; // caller counts vf_above
        }
        // depth < stored_depth: reverse shift_eq + push_shift_down
        let delta = (stored_depth - depth) as i16;
        if self.ctx.shift_eq(e, stored_input, delta) {
            let result_fvar_lb = self.ctx.fvar_lb(self.ctx.read_expr(stored_result).get_fvar_list());
            if self.ctx.num_loose_bvars(stored_result) == 0 || result_fvar_lb >= delta as u16 {
                return Some(self.ctx.push_shift_down(stored_result, delta as u16));
            }
        }
        None
    }

    /// Store an infer result in the chained cache.
    fn infer_cache_store(&mut self, bucket_idx: usize, canon: CacheKey, e: ExprPtr<'t>, r: ExprPtr<'t>, depth: u16, is_check: bool) {
        let chain = self.tc_cache.infer_cache_chain(bucket_idx, &canon);
        for (ci, &(si, _sr, sd, sc)) in chain.iter().enumerate() {
            if si == e { return; }
            let is_family = if depth == sd {
                self.ctx.sem_eq(si, e)
            } else if depth > sd {
                self.ctx.shift_eq(si, e, (depth - sd) as i16)
            } else {
                self.ctx.shift_eq(e, si, (sd - depth) as i16)
            };
            if is_family {
                // Same family — prefer checked, then lower depth
                let dominated = (is_check && !sc) || (is_check == sc && depth < sd);
                if dominated {
                    if let Some(slot) = self.tc_cache.infer_cache_get_mut(bucket_idx, &canon, ci) {
                        *slot = (e, r, depth, is_check);
                    }
                }
                return;
            }
        }
        // No matching family — append
        if !chain.is_empty() { self.ctx.trace.infer_cache_overflow_stores += 1; }
        self.tc_cache.infer_cache_push(bucket_idx, canon, (e, r, depth, is_check));
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
        let depth0 = self.depth();
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
        assert_eq!(depth0, self.depth());
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
        // Eager: substitute first, then infer.
        let subst_body = self.ctx.inst_beta(body, &[val]);
        self.infer(subst_body, flag)
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
                if !self.ctx.sem_eq(y, x) {
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
        self.ctx.trace.whnf_calls += 1;
        self.ctx.check_heartbeat();
        let r = stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.whnf_inner(e));
        r
    }

    fn whnf_inner(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        if matches!(self.ctx.read_expr(e), NatLit { .. } | StringLit { .. }) {
            return e
        }
        // whnf is shift-equivariant: whnf(Shift(e, k, 0)) = shift(whnf(e), k)
        // Peel off cutoff=0 Shift nodes (iteratively). For cutoff>0, force first.
        // Must also shrink local_ctx because whnf can indirectly call infer
        // (via reduce_rec → to_ctor_when_k) which depends on local_ctx.
        let mut total_shift: i16 = 0;
        let mut e = e;
        while let Shift { inner, amount, cutoff, .. } = self.ctx.read_expr(e) {
            if cutoff == 0 && amount > 0 {
                total_shift += amount;
                e = inner;
            } else if cutoff > 0 {
                e = self.ctx.push_shift(inner, amount, cutoff);
            } else {
                break; // negative shift with cutoff=0: can't peel (would need higher depth)
            }
        }
        if total_shift > 0 {
            if self.depth() == 0 {
                let r = self.whnf(e);
                return self.ctx.mk_shift(r, total_shift);
            }
            let new_depth = self.depth() - total_shift as usize;
            self.ctx.trace.whnf_shift_peel += 1;
            self.ctx.trace.shift_peel_frames_total += total_shift as u64;
            let saved = self.tc_cache.split_off(new_depth);
            let r = self.whnf(e);
            self.tc_cache.extend(saved);
            return self.ctx.mk_shift(r, total_shift);
        }
        // Stacked whnf cache: bucket 0 for closed, bucket (depth - fvar_lb) for open.
        // Using fvar_lb-based bucketing ensures shift-related expressions at different
        // depths land in the same bucket, enabling cross-depth shift_eq reuse.
        let canon = self.ctx.canonical_hash(e);
        let depth = self.depth() as u16;
        let e_nlbv = self.ctx.num_loose_bvars(e);
        let whnf_bucket_idx = if e_nlbv == 0 {
            0
        } else {
            let e_lb = self.ctx.fvar_lb(self.ctx.read_expr(e).get_fvar_list());
            (depth - e_lb) as usize
        };
        // Look up in whnf cache chain.
        // Copy chain entries to release borrow before calling methods on self.
        let chain = self.tc_cache.whnf_cache_chain(whnf_bucket_idx, &canon);
        if !chain.is_empty() {
            for (ci, &(stored_input, stored_result, stored_depth)) in chain.iter().enumerate() {
                if let Some(result) = self.try_whnf_cache_hit(e, stored_input, stored_result, stored_depth, depth) {
                    self.ctx.trace.whnf_cache_hits += 1;
                    if ci > 0 { self.ctx.trace.whnf_cache_overflow_hits += 1; }
                    if stored_depth == depth && stored_input != e {
                        if let Some(slot) = self.tc_cache.whnf_cache_get_mut(whnf_bucket_idx, &canon, ci) {
                            *slot = (e, result, depth);
                        }
                    }
                    if stored_depth > depth {
                        // Below-depth hit: return eagerly shifted result
                        return result;
                    }
                    return result;
                }
            }
            self.ctx.trace.whnf_cache_verify_fail += 1;
        } else if self.tc_cache.whnf_cache_bucket_exists(whnf_bucket_idx) {
            self.ctx.trace.whnf_cache_no_entry += 1;
        } else {
            self.ctx.trace.whnf_cache_no_bucket += 1;
        }
        let mut cursor = e;
        loop {
            let whnfd = self.whnf_no_unfolding(cursor);
            if let Some(reduce_nat_ok) = self.try_reduce_nat(whnfd) {
                cursor = reduce_nat_ok;
            } else if let Some(next_term) = self.unfold_def(whnfd) {
                cursor = next_term;
            } else {
                // Store with depth for cross-depth reuse (2-slot).
                self.whnf_cache_store(whnf_bucket_idx, canon, e, whnfd, depth);
                return whnfd
            }
        }
    }

    /// Try to match a query expression against a stored cache slot.
    /// Returns Some(result) on hit, None on miss.
    fn try_whnf_cache_hit(&mut self, e: ExprPtr<'t>, stored_input: ExprPtr<'t>, stored_result: ExprPtr<'t>, stored_depth: u16, depth: u16) -> Option<ExprPtr<'t>> {
        if stored_depth == depth && (stored_input == e || self.ctx.sem_eq(stored_input, e)) {
            return Some(stored_result);
        }
        // Above-depth hit: positive shift wraps result
        if depth > stored_depth {
            let delta = (depth - stored_depth) as i16;
            if self.ctx.shift_eq(stored_input, e, delta) {
                if self.ctx.num_loose_bvars(stored_result) == 0 {
                    return Some(stored_result);
                }
                return Some(self.ctx.push_shift(stored_result, delta, 0));
            }
        }
        // Below-depth hit: shift result down via eager push_shift_down
        if depth < stored_depth {
            let abs_delta = (stored_depth - depth) as i16;
            if self.ctx.shift_eq(e, stored_input, abs_delta) {
                let result_fvar_lb = self.ctx.fvar_lb(self.ctx.read_expr(stored_result).get_fvar_list());
                if result_fvar_lb >= abs_delta as u16 {
                    self.ctx.trace.whnf_below_depth_hits += 1;
                    let shifted = self.ctx.push_shift_down(stored_result, abs_delta as u16);
                    return Some(shifted);
                }
            }
        }
        None
    }

    /// Store a whnf result in the chained cache.
    fn whnf_cache_store(&mut self, bucket_idx: usize, canon: CacheKey, e: ExprPtr<'t>, result: ExprPtr<'t>, depth: u16) {
        // Validate: stored result's fvar_lb must be < depth (or closed)
        let new_slot: WhnfSlot<'t> = (e, result, depth);
        let chain = self.tc_cache.whnf_cache_chain(bucket_idx, &canon);
        for (ci, &(si, _sr, sd)) in chain.iter().enumerate() {
            if si == e { return; } // already stored
            let is_family = if depth == sd {
                self.ctx.sem_eq(si, e)
            } else if depth > sd {
                self.ctx.shift_eq(si, e, (depth - sd) as i16)
            } else {
                self.ctx.shift_eq(e, si, (sd - depth) as i16)
            };
            if is_family {
                // Same family — prefer the lowest depth (canonical representative)
                if depth < sd {
                    if let Some(slot) = self.tc_cache.whnf_cache_get_mut(bucket_idx, &canon, ci) {
                        *slot = new_slot;
                    }
                }
                return;
            }
        }
        // No matching family — append new entry
        if !chain.is_empty() { self.ctx.trace.whnf_cache_overflow_stores += 1; }
        self.tc_cache.whnf_cache_push(bucket_idx, canon, new_slot);
    }

    fn whnf_no_unfolding_cheap_proj(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        self.whnf_no_unfolding_aux(e, true)
    }

    pub fn whnf_no_unfolding(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        self.whnf_no_unfolding_aux(e, false)
    }

    fn whnf_no_unfolding_aux(&mut self, e: ExprPtr<'t>, cheap_proj: bool) -> ExprPtr<'t> {
        self.ctx.trace.wnu_calls += 1;
        // whnf_no_unfolding is shift-equivariant: peel top-level Shifts.
        // Must also shrink local_ctx because reduce_rec → to_ctor_when_k → infer
        // depends on local_ctx.
        let mut total_shift: i16 = 0;
        let mut e = e;
        while let Shift { inner, amount, cutoff, .. } = self.ctx.read_expr(e) {
            if cutoff == 0 && amount > 0 {
                total_shift += amount;
                e = inner;
            } else if cutoff > 0 {
                e = self.ctx.push_shift(inner, amount, cutoff);
            } else {
                break; // negative shift with cutoff=0: can't peel (would need higher depth)
            }
        }
        if total_shift > 0 {
            self.ctx.trace.wnu_shift_peel += 1;
            self.ctx.trace.shift_peel_frames_total += total_shift as u64;
            if self.depth() == 0 {
                let r = self.whnf_no_unfolding_aux(e, cheap_proj);
                return self.ctx.push_shift(r, total_shift, 0);
            }
            let new_depth = self.depth() - total_shift as usize;
            let saved = self.tc_cache.split_off(new_depth);
            let r = self.whnf_no_unfolding_aux(e, cheap_proj);
            self.tc_cache.extend(saved);
            return self.ctx.push_shift(r, total_shift, 0);
        }
        // Iterative version: tail-recursive calls become loop iterations.
        // We track original inputs to cache on exit.
        let mut cache_entries: Vec<ExprPtr<'t>> = Vec::new();
        let mut cur = e;
        let result = loop {
            // Stacked whnf_no_unfolding cache: bucket 0 for closed, bucket (depth - fvar_lb) for open.
            let cur_canon = self.ctx.canonical_hash(cur);
            let cur_nlbv = self.ctx.num_loose_bvars(cur);
            let cur_depth = self.depth() as u16;
            let wnu_bucket_idx = if cur_nlbv == 0 {
                0
            } else {
                let cur_lb = self.ctx.fvar_lb(self.ctx.read_expr(cur).get_fvar_list());
                (cur_depth - cur_lb) as usize
            };
            let wnu_chain = self.tc_cache.wnu_cache_chain(wnu_bucket_idx, &cur_canon);
            if !wnu_chain.is_empty() {
                let mut wnu_hit = false;
                for (ci, &(stored_input, stored_result, stored_depth)) in wnu_chain.iter().enumerate() {
                    if stored_depth == cur_depth && (stored_input == cur || self.ctx.sem_eq(stored_input, cur)) {
                        self.ctx.trace.wnu_cache_hits += 1;
                        if ci > 0 { self.ctx.trace.wnu_cache_overflow_hits += 1; }
                        wnu_hit = true;
                        cur = stored_result;
                        break;
                    }
                    if cur_depth > stored_depth {
                        let delta = (cur_depth - stored_depth) as i16;
                        if self.ctx.shift_eq(stored_input, cur, delta) {
                            self.ctx.trace.wnu_cache_hits += 1;
                            if ci > 0 { self.ctx.trace.wnu_cache_overflow_hits += 1; }
                            wnu_hit = true;
                            cur = self.ctx.push_shift(stored_result, delta, 0);
                            break;
                        }
                    }
                    // Below-depth hit: conservative O(1) adjustment only
                    if cur_depth < stored_depth {
                        let abs_delta = (stored_depth - cur_depth) as i16;
                        let result_nlbv = self.ctx.num_loose_bvars(stored_result);
                        let usable = if result_nlbv == 0 {
                            true
                        } else if stored_result == stored_input {
                            true
                        } else if let Expr::Shift { amount, cutoff: 0, .. } = self.ctx.read_expr(stored_result) {
                            amount >= abs_delta
                        } else {
                            false
                        };
                        if usable && self.ctx.shift_eq(cur, stored_input, abs_delta) {
                            self.ctx.trace.wnu_cache_hits += 1;
                            if ci > 0 { self.ctx.trace.wnu_cache_overflow_hits += 1; }
                            wnu_hit = true;
                            if result_nlbv == 0 {
                                cur = stored_result;
                            } else if stored_result == stored_input {
                                cur = cur; // identity (no-op)
                            } else if let Expr::Shift { inner, amount, cutoff: 0, .. } = self.ctx.read_expr(stored_result) {
                                cur = self.ctx.mk_shift(inner, amount - abs_delta);
                            }
                            break;
                        }
                    }
                }
                if wnu_hit { break cur; }
                self.ctx.trace.wnu_cache_verify_fail += 1;
            } else {
                // No entry at this bucket (or bucket doesn't exist).
                // Distinguish no_entry vs no_bucket for diagnostics.
                if wnu_bucket_idx == 0 || self.tc_cache.frames.get(wnu_bucket_idx - 1).is_some() {
                    self.ctx.trace.wnu_cache_no_entry += 1;
                } else {
                    self.ctx.trace.wnu_cache_no_bucket += 1;
                }
            }
            let (mut e_fun, args) = self.ctx.unfold_apps(cur);
            // Force any Shift wrapper on the head so the match sees real constructors.
            // unfold_apps handles Shift for App spines but wraps non-App heads in mk_shift.
            if let Expr::Shift { inner, amount, cutoff, .. } = self.ctx.read_expr(e_fun) {
                e_fun = self.ctx.push_shift(inner, amount, cutoff);
            }
            match self.ctx.read_expr(e_fun) {
                Proj { idx, structure, .. } =>
                    if let Some(e) = self.reduce_proj(idx, structure, cheap_proj) {
                        let next = self.ctx.foldl_apps(e, args.into_iter());
                        if !cheap_proj { cache_entries.push(cur); }
                        cur = next;
                        continue;
                    } else {
                        let r = self.ctx.foldl_apps(e_fun, args.into_iter());
                        // Identity cache: safe even for cheap_proj (no reduction applied)
                        cache_entries.push(cur);
                        break r;
                    },
                Sort { level, .. } => {
                    debug_assert!(args.is_empty());
                    let level = self.ctx.simplify(level);
                    cache_entries.push(cur);
                    break self.ctx.mk_sort(level);
                }
                Lambda { .. } if !args.is_empty() => {
                    let (mut e, mut n_args) = (e_fun, 0usize);
                    while let (Lambda { body, .. }, [_arg, _rest @ ..]) = (self.ctx.view_expr(e), &args[n_args..]) {
                        n_args += 1;
                        e = body;
                    }
                    self.ctx.trace.whnf_beta_reductions += 1;
                    e = self.ctx.inst_beta(e, &args[..n_args]);
                    let next = self.ctx.foldl_apps(e, args.into_iter().skip(n_args));
                    if !cheap_proj { cache_entries.push(cur); }
                    cur = next;
                    continue;
                }
                Lambda { .. } => {
                    debug_assert!(args.is_empty());
                    let r = self.ctx.foldl_apps(e_fun, args.into_iter());
                    cache_entries.push(cur);
                    break r;
                }
                Let { binder_type, val, body, .. } => {
                    self.ctx.trace.whnf_let_reductions += 1;
                    // Lazy zeta: push let-binding, reduce body in extended context,
                    // then pop and inst_beta on the (much smaller) whnf result.
                    // This avoids unbounded inst_beta growth on nested lets.
                    self.push_local_let(binder_type, val);
                    // Args from unfold_apps are in the outer context; body is in
                    // the let-extended context (one more binder). Shift args up by 1
                    // so their de Bruijn indices are valid under the let binder.
                    let inner = if args.is_empty() {
                        body
                    } else {
                        let shifted_args: Vec<_> = args.into_iter().map(|a| self.ctx.mk_shift(a, 1)).collect();
                        self.ctx.foldl_apps(body, shifted_args.into_iter())
                    };
                    let reduced = self.whnf_no_unfolding_aux(inner, cheap_proj);
                    self.pop_local();
                    let result = self.ctx.inst_beta(reduced, &[val]);
                    if !cheap_proj { cache_entries.push(cur); }
                    cur = result;
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
                        let r = self.ctx.foldl_apps(e_fun, args.into_iter());
                        // Identity cache: safe even for cheap_proj (no reduction applied)
                        cache_entries.push(cur);
                        break r;
                    },
                Var { dbj_idx, .. } => {
                    if let Some(val) = self.lookup_var_value(dbj_idx) {
                        self.ctx.trace.zeta_reductions += 1;
                        let next = self.ctx.foldl_apps(val, args.into_iter());
                        if !cheap_proj { cache_entries.push(cur); }
                        cur = next;
                        continue;
                    }
                    let r = self.ctx.foldl_apps(e_fun, args.into_iter());
                    // Identity cache: safe even for cheap_proj (no reduction applied)
                    cache_entries.push(cur);
                    break r;
                }
                Pi { .. } => {
                    debug_assert!(args.is_empty());
                    cache_entries.push(cur);
                    break e_fun;
                }
                App { .. } => panic!(),
                Local { .. } | NatLit { .. } | StringLit { .. } => {
                    let r = self.ctx.foldl_apps(e_fun, args.into_iter());
                    cache_entries.push(cur);
                    break r;
                }
                Shift { inner, amount, cutoff, .. } => {
                    let forced = self.ctx.push_shift(inner, amount, cutoff);
                    let next = self.ctx.foldl_apps(forced, args.into_iter());
                    if !cheap_proj { cache_entries.push(cur); }
                    cur = next;
                    continue;
                }
            }
        };
        // Cache intermediate inputs (non-cheap_proj only).
        if !cheap_proj {
            let store_depth = self.depth() as u16;
            for entry in cache_entries {
                let entry_canon = self.ctx.canonical_hash(entry);
                let entry_nlbv = self.ctx.num_loose_bvars(entry);
                let entry_bucket_idx = if entry_nlbv == 0 {
                    0
                } else {
                    let entry_lb = self.ctx.fvar_lb(self.ctx.read_expr(entry).get_fvar_list());
                    (store_depth - entry_lb) as usize
                };
                let new_slot: WhnfSlot<'t> = (entry, result, store_depth);
                let wnu_chain = self.tc_cache.wnu_cache_chain(entry_bucket_idx, &entry_canon);
                if !wnu_chain.is_empty() {
                    // Check if already stored
                    if wnu_chain.iter().any(|s| s.0 == entry) {
                        self.ctx.trace.wnu_cache_update_skip += 1;
                        continue;
                    }
                    // Try to replace an entry at higher depth
                    let mut replaced = false;
                    for (ci, &(_, _, sd)) in wnu_chain.iter().enumerate() {
                        if store_depth < sd {
                            if let Some(slot) = self.tc_cache.wnu_cache_get_mut(entry_bucket_idx, &entry_canon, ci) {
                                *slot = new_slot;
                            }
                            replaced = true;
                            self.ctx.trace.wnu_cache_update_lower += 1;
                            break;
                        }
                    }
                    if !replaced {
                        // Append new entry
                        self.ctx.trace.wnu_cache_overflow_stores += 1;
                        self.tc_cache.wnu_cache_push(entry_bucket_idx, entry_canon, new_slot);
                        self.ctx.trace.wnu_cache_update_higher += 1;
                    }
                } else {
                    self.tc_cache.wnu_cache_push(entry_bucket_idx, entry_canon, new_slot);
                    self.ctx.trace.wnu_cache_new_inserts += 1;
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
            return Some(self.ctx.sem_eq(x, y))
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
        let depth0 = self.depth();
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

    /// Speculative app congruence: try to prove App(f1,a1) == App(f2,a2)
    /// using only O(1) checks (sem_eq + eq_cache + UF), without whnf.
    /// Recursively peels matching App layers. Returns Some(true) on full match.
    fn spec_app_congruence(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<bool> {
        self.ctx.trace.spec_app_tried += 1;
        // Peel App layers, checking args via cheap_eq.
        // Use view_expr to see through Shift wrappers on the spine.
        let (mut fx, mut fy) = (x, y);
        loop {
            match self.ctx.view_expr_pair(fx, fy) {
                (App { fun: f1, arg: a1, .. }, App { fun: f2, arg: a2, .. }) => {
                    if !self.cheap_eq(a1, a2) {
                        return None;
                    }
                    fx = f1;
                    fy = f2;
                }
                _ => break,
            }
        }
        // Check the head
        if !self.cheap_eq(fx, fy) {
            return None;
        }
        self.ctx.trace.spec_app_hit += 1;
        Some(true)
    }

    /// O(1) equality check: sem_eq + eq_cache + UF + defeq_open.
    /// Never calls def_eq recursively.
    fn cheap_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        self.ctx.sem_eq(x, y)
            || self.eq_cache_contains(x, y)
            || self.tc_cache.eq_cache_uf.check_uf_eq(x, y)
            || self.defeq_open_lookup(true, x, y)
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

        let args_eq = args1.into_iter().zip(args2).all(|(xx, yy)| {
            self.def_eq(xx, yy)
        });

        if !args_eq {
            return false
        }

        if !self.def_eq(f1, f2) {
            return false
        }
        true
    }

    pub fn assert_def_eq(&mut self, u: ExprPtr<'t>, v: ExprPtr<'t>) {
        assert!(self.def_eq(u, v))
    }
    pub fn def_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        self.ctx.trace.def_eq_calls += 1;
        self.ctx.check_heartbeat();
        stacker::maybe_grow(64 * 1024, 2 * 1024 * 1024, || self.def_eq_inner(x, y))
    }

    fn def_eq_inner(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        if let Some(easy) = self.def_eq_quick_check(x, y) {
            return easy
        }
        self.ctx.trace.def_eq_inner_calls += 1;

        // Speculative app congruence: if both sides are applications, try comparing
        // their spines via cheap O(1) checks (sem_eq + caches) before doing whnf.
        // Avoids expensive whnf/delta steps for cases resolvable by structural congruence.
        if matches!((self.ctx.read_expr(x), self.ctx.read_expr(y)), (App { .. }, App { .. })) {
            if let Some(true) = self.spec_app_congruence(x, y) {
                // Cache the result for future lookups
                self.eq_cache_insert(x, y);
                self.defeq_open_store_pos(x, y);
                self.tc_cache.eq_cache_uf.union(x, y);
                return true;
            }
        }

        let x_n = self.whnf_no_unfolding_cheap_proj(x);
        let y_n = self.whnf_no_unfolding_cheap_proj(y);

        if (self.ctx.num_loose_bvars(x_n) == 0 || self.ctx.eager_mode) && Some(y_n) == self.ctx.c_bool_true() {
            let x_nn = self.whnf(x_n);
            if Some(x_nn) == self.ctx.c_bool_true() {
                return true
            }
        }

        if (x_n != x || y_n != y) {
            if let Some(easy) = self.def_eq_quick_check(x_n, y_n) {
                return easy
            }
        }

        // Second speculative app congruence on whnf-reduced forms (x_n, y_n)
        if (x_n != x || y_n != y) && matches!((self.ctx.read_expr(x_n), self.ctx.read_expr(y_n)), (App { .. }, App { .. })) {
            self.ctx.trace.spec_app2_tried += 1;
            let spec_result = {
                let (mut fx, mut fy) = (x_n, y_n);
                let mut ok = true;
                loop {
                    match self.ctx.view_expr_pair(fx, fy) {
                        (App { fun: f1, arg: a1, .. }, App { fun: f2, arg: a2, .. }) => {
                            if !self.cheap_eq(a1, a2) { ok = false; break; }
                            fx = f1; fy = f2;
                        }
                        _ => break,
                    }
                }
                if ok && self.cheap_eq(fx, fy) { Some(true) } else { None }
            };
            if let Some(true) = spec_result {
                self.ctx.trace.spec_app2_hit += 1;
                self.eq_cache_insert(x, y);
                self.eq_cache_insert(x_n, y_n);
                self.defeq_open_store_pos(x, y);
                self.tc_cache.eq_cache_uf.union(x, y);
                self.tc_cache.eq_cache_uf.union(x_n, y_n);
                return true;
            }
        }

        self.ctx.trace.def_eq_deep_calls += 1;

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
            self.eq_cache_insert(x, y);
            self.defeq_open_store_pos(x, y);
            self.tc_cache.eq_cache_uf.union(x, y);
            // Also union shift-stripped versions so UF works across shift levels.
            // Sound because Shift(a,k,0) = Shift(b,k,0) iff a = b.
            // Only attempt when at least one side is a Shift (avoid overhead on common case).
            if matches!((self.ctx.read_expr(x), self.ctx.read_expr(y)), (Expr::Shift { .. }, Expr::Shift { .. })) {
                let (mut xi, mut xa) = (x, 0i16);
                while let Expr::Shift { inner, amount, cutoff: 0, .. } = self.ctx.read_expr(xi) {
                    xa += amount; xi = inner;
                }
                let (mut yi, mut ya) = (y, 0i16);
                while let Expr::Shift { inner, amount, cutoff: 0, .. } = self.ctx.read_expr(yi) {
                    ya += amount; yi = inner;
                }
                if xa == ya && xa > 0 {
                    self.tc_cache.eq_cache_uf.union(xi, yi);
                }
            }
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
        // Semantic equality: handles internal Shift wrappers transparently.
        // Subsumes the old pointer equality, Shift-stripping, and shift_eq checks.
        if self.ctx.sem_eq(x, y) {
            return Some(true)
        }
        if self.eq_cache_contains(x, y) {
            return Some(true)
        }
        // Transitive pointer-based UnionFind: if A=B and B=C were proven,
        // finds A=C in O(α(n)) without needing a direct cache entry.
        if self.tc_cache.eq_cache_uf.check_uf_eq(x, y) {
            self.ctx.trace.eq_cache_uf_hits += 1;
            return Some(true)
        }
        // Shift-invariant positive def_eq cache for open expressions
        if self.defeq_open_lookup(true, x, y) {
            return Some(true)
        }
        // Shift-aware UF: strip matching Shift wrappers and check inner expressions.
        // Checked after open cache (cheaper checks first). Only when at least one is Shift.
        if matches!((self.ctx.read_expr(x), self.ctx.read_expr(y)), (Expr::Shift { .. }, Expr::Shift { .. })) {
            let (mut xi, mut xa) = (x, 0i16);
            while let Expr::Shift { inner, amount, cutoff: 0, .. } = self.ctx.read_expr(xi) {
                xa += amount; xi = inner;
            }
            let (mut yi, mut ya) = (y, 0i16);
            while let Expr::Shift { inner, amount, cutoff: 0, .. } = self.ctx.read_expr(yi) {
                ya += amount; yi = inner;
            }
            if xa == ya && xa > 0 && self.tc_cache.eq_cache_uf.check_uf_eq(xi, yi) {
                self.ctx.trace.eq_cache_uf_hits += 1;
                return Some(true)
            }
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
        let (key, swapped) = self.defeq_canon_key(x, y);
        let (qx, qy) = if swapped { (y, x) } else { (x, y) };
        let chain = self.tc_cache.failure_cache.get_chain(&key);
        if !chain.is_empty() {
            for (ci, &(stored_a, stored_b)) in chain.iter().enumerate() {
                if self.ctx.sem_eq(stored_a, qx) && self.ctx.sem_eq(stored_b, qy) {
                    if ci > 0 { self.ctx.trace.fail_cache_overflow_hits += 1; }
                    return true;
                }
            }
            self.ctx.trace.fail_cache_verify_fail += 1;
        }
        if self.defeq_open_lookup(false, x, y) {
            return true;
        }
        false
    }

    fn failure_cache_insert(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        let (key, swapped) = self.defeq_canon_key(x, y);
        let (a, b) = if swapped { (y, x) } else { (x, y) };
        let chain = self.tc_cache.failure_cache.get_chain(&key);
        if chain.iter().any(|&(sa, sb)| sa == a && sb == b) { return; }
        if !chain.is_empty() { self.ctx.trace.fail_cache_overflow_stores += 1; }
        self.tc_cache.failure_cache.push(key, (a, b));
        self.defeq_open_store_neg(x, y);
    }

    /// Compute bucket index for shift-invariant def_eq cache.
    /// Returns None if both expressions are closed (use global cache instead).
    fn defeq_bucket_idx(&self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> Option<usize> {
        let depth = self.depth() as u16;
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

    /// Canonical-hash-keyed eq_cache lookup for closed expressions.
    /// Uses sem_eq to verify (handles internal Shift wrappers).
    fn eq_cache_contains(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        let (key, swapped) = self.defeq_canon_key(x, y);
        let (qx, qy) = if swapped { (y, x) } else { (x, y) };
        let chain = self.tc_cache.eq_cache.get_chain(&key);
        if chain.is_empty() { return false; }
        for (ci, &(stored_a, stored_b)) in chain.iter().enumerate() {
            if self.ctx.sem_eq(stored_a, qx) && self.ctx.sem_eq(stored_b, qy) {
                self.ctx.trace.eq_cache_hits += 1;
                if ci > 0 { self.ctx.trace.eq_cache_overflow_hits += 1; }
                if stored_a != qx || stored_b != qy {
                    self.ctx.trace.eq_cache_cross_depth_hits += 1;
                }
                return true;
            }
        }
        self.ctx.trace.eq_cache_verify_fail += 1;
        false
    }

    /// Canonical-hash-keyed eq_cache insert for closed expressions.
    /// Appends to chain if key already has entries with different pointers.
    fn eq_cache_insert(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        let (key, swapped) = self.defeq_canon_key(x, y);
        let (a, b) = if swapped { (y, x) } else { (x, y) };
        let chain = self.tc_cache.eq_cache.get_chain(&key);
        for &(stored_a, stored_b) in chain.iter() {
            if stored_a == a && stored_b == b {
                return; // Already stored
            }
        }
        if chain.is_empty() {
            self.tc_cache.eq_cache.insert_first(key, (a, b));
        } else {
            self.ctx.trace.eq_cache_overflow_stores += 1;
            self.tc_cache.eq_cache.push(key, (a, b));
        }
    }

    /// Ordered canonical hash key for a pair of expressions.
    fn defeq_canon_key(&self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> ((u64, u64), bool) {
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
        &mut self,
        is_pos: bool,
        x: ExprPtr<'t>,
        y: ExprPtr<'t>,
    ) -> bool {
        let Some(bucket_idx) = self.defeq_bucket_idx(x, y) else { return false };
        let (key, swapped) = self.defeq_canon_key(x, y);
        let Some(&(stored_a, stored_b, stored_depth)) = self.tc_cache.defeq_open_get(is_pos, bucket_idx, &key) else { return false };
        let depth = self.depth() as u16;
        let (qx, qy) = if swapped { (y, x) } else { (x, y) };
        // Exact depth match with semantic equality
        if stored_depth == depth && self.ctx.sem_eq(stored_a, qx) && self.ctx.sem_eq(stored_b, qy) {
            if is_pos { self.ctx.trace.defeq_open_pos_hits += 1; } else { self.ctx.trace.defeq_open_neg_hits += 1; }
            return true;
        }
        // Shift-invariant match
        if depth >= stored_depth {
            let delta = (depth - stored_depth) as i16;
            if delta > 0 {
                if self.ctx.shift_eq(stored_a, qx, delta) && self.ctx.shift_eq(stored_b, qy, delta) {
                    if is_pos { self.ctx.trace.defeq_open_pos_hits += 1; } else { self.ctx.trace.defeq_open_neg_hits += 1; }
                    return true;
                }
                // Try swapped assignment if canonical hashes are equal
                if self.ctx.canonical_hash(x) == self.ctx.canonical_hash(y)
                    && self.ctx.shift_eq(stored_a, qy, delta)
                    && self.ctx.shift_eq(stored_b, qx, delta)
                {
                    if is_pos { self.ctx.trace.defeq_open_pos_hits += 1; } else { self.ctx.trace.defeq_open_neg_hits += 1; }
                    return true;
                }
            }
        }
        false
    }

    /// Store in a shift-invariant def_eq cache (positive or negative).
    fn defeq_open_store_pos(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        self.defeq_open_store_impl(true, x, y);
    }

    fn defeq_open_store_neg(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        self.defeq_open_store_impl(false, x, y);
    }

    fn defeq_open_store_impl(&mut self, is_pos: bool, x: ExprPtr<'t>, y: ExprPtr<'t>) {
        let depth = self.depth() as u16;
        let x_nlbv = self.ctx.num_loose_bvars(x);
        let y_nlbv = self.ctx.num_loose_bvars(y);
        if x_nlbv == 0 && y_nlbv == 0 { return; }
        if depth == 0 { return; }
        let x_lb = if x_nlbv > 0 { self.ctx.fvar_lb(self.ctx.read_expr(x).get_fvar_list()) } else { u16::MAX };
        let y_lb = if y_nlbv > 0 { self.ctx.fvar_lb(self.ctx.read_expr(y).get_fvar_list()) } else { u16::MAX };
        let min_lb = x_lb.min(y_lb);
        let bucket_idx = (depth - 1 - min_lb) as usize;
        let cx = self.ctx.canonical_hash(x);
        let cy = self.ctx.canonical_hash(y);
        let (key, swapped) = if cx <= cy { ((cx, cy), false) } else { ((cy, cx), true) };
        let (sx, sy) = if swapped { (y, x) } else { (x, y) };
        if self.tc_cache.defeq_open_get(is_pos, bucket_idx, &key).map_or(true, |&(_, _, sd)| depth < sd) {
            self.tc_cache.defeq_open_insert(is_pos, bucket_idx, key, (sx, sy, depth));
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
            if !self.ctx.sem_eq(eprime, e) {
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
                (None, None) => {
                    return Exhausted(x, y);
                }
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
