//! Outermost-Shift Normal Form (OSNF) analysis.
//!
//! For expression `e` with `fvar_lb = k > 0`, the OSNF is `Shift(core, k, cutoff=0)`
//! where `core = shift_down(e, k, 0)` has `fvar_lb = 0`.
//!
//! Two expressions share a core iff they are uniform-shift-equivalent: they differ
//! only by a constant offset on all free bvar indices.
//!
//! This module computes statistics on potential OSNF sharing in the export file DAG
//! without modifying the DAG.

use crate::expr::{Expr, APP_HASH, LAMBDA_HASH, LET_HASH, PI_HASH, PROJ_HASH, VAR_HASH};
use crate::hash64;
use crate::util::{DagMarker, ExportFile, ExprPtr, FxHashMap, LeanDag, Ptr};

/// Compute and print OSNF sharing statistics for the export file DAG.
///
/// For each expression with `fvar_lb > 0` (could be shifted down to normalize),
/// compute the hash of its OSNF core and count how many expressions share each core.
pub fn compute_osnf_stats(export_file: &ExportFile) {
    let dag = &export_file.dag;
    compute_osnf_stats_inner(dag);
}

fn compute_osnf_stats_inner(dag: &LeanDag) {
    let n = dag.exprs.len();
    let mut memo: FxHashMap<(usize, u16, u16), u64> = FxHashMap::default();
    // core_hash -> (count of candidates mapping to this core, example fvar_lb values)
    let mut core_counts: FxHashMap<u64, u32> = FxHashMap::default();

    let mut total_open = 0u32; // expressions with nlbv > 0
    let mut candidates = 0u32; // expressions with nlbv > 0 AND fvar_lb > 0
    let mut fvar_lb_sum = 0u64; // sum of fvar_lb values for candidates

    // Also check: how many cores already exist in the DAG as fvar_lb=0 expressions?
    // Collect hashes of all fvar_lb=0 open expressions.
    let mut existing_cores: FxHashMap<u64, usize> = FxHashMap::default();
    for idx in 0..n {
        let expr = dag.exprs.get_index(idx).unwrap();
        let nlbv = dag.expr_nlbv[idx];
        if nlbv > 0 && expr.get_fvar_lb() == 0 {
            // This is an open expression already at fvar_lb=0 — a potential core
            existing_cores.insert(expr.get_hash(), idx);
        }
    }

    for idx in 0..n {
        let expr = dag.exprs.get_index(idx).unwrap();
        let nlbv = dag.expr_nlbv[idx];
        if nlbv == 0 {
            continue;
        }
        total_open += 1;

        let fvar_lb = expr.get_fvar_lb();
        if fvar_lb == 0 {
            continue;
        }
        candidates += 1;
        fvar_lb_sum += fvar_lb as u64;

        let ch = core_hash(dag, idx, fvar_lb, 0, &mut memo);
        *core_counts.entry(ch).or_insert(0) += 1;
    }

    if candidates == 0 {
        eprintln!("OSNF: dag_size={}, open={}, candidates=0 (nothing to normalize)", n, total_open);
        return;
    }

    let unique_cores = core_counts.len();
    let shared_cores = core_counts.values().filter(|&&c| c > 1).count();
    let total_in_shared = core_counts.values().filter(|&&c| c > 1).map(|&c| c as usize).sum::<usize>();
    let max_group = core_counts.values().copied().max().unwrap_or(0);

    // How many of these cores already exist as fvar_lb=0 expressions in the DAG?
    let cores_already_present = core_counts.keys().filter(|h| existing_cores.contains_key(h)).count();

    // Sharing distribution: group sizes
    let mut size_hist: FxHashMap<u32, u32> = FxHashMap::default();
    for &count in core_counts.values() {
        *size_hist.entry(count).or_insert(0) += 1;
    }
    let mut hist_vec: Vec<(u32, u32)> = size_hist.into_iter().collect();
    hist_vec.sort();

    eprintln!("OSNF stats (cutoff-0):");
    eprintln!("  DAG size: {} exprs ({} open, {} closed)", n, total_open, n as u32 - total_open);
    eprintln!("  Candidates (fvar_lb > 0): {} ({:.1}% of open)", candidates, 100.0 * candidates as f64 / total_open as f64);
    eprintln!("  Avg fvar_lb: {:.1}", fvar_lb_sum as f64 / candidates as f64);
    eprintln!("  Unique cores: {} (sharing ratio: {:.2}x)", unique_cores, candidates as f64 / unique_cores as f64);
    eprintln!("  Shared cores (group > 1): {} covering {} candidates", shared_cores, total_in_shared);
    eprintln!("  Largest group: {}", max_group);
    eprintln!("  Cores already in DAG (fvar_lb=0): {} ({:.1}% of unique)", cores_already_present, 100.0 * cores_already_present as f64 / unique_cores as f64);
    eprintln!("  Group size distribution:");
    for (size, count) in &hist_vec {
        eprintln!("    size {}: {} groups ({} exprs)", size, count, size * count);
    }
}

/// Recursively compute the hash of `shift_down(expr[idx], shift, cutoff)`.
///
/// This is the hash the expression would have if all free bvars >= cutoff
/// were decreased by `shift`. With memoization on `(idx, shift, cutoff)`.
fn core_hash(
    dag: &LeanDag,
    idx: usize,
    shift: u16,
    cutoff: u16,
    memo: &mut FxHashMap<(usize, u16, u16), u64>,
) -> u64 {
    if let Some(&h) = memo.get(&(idx, shift, cutoff)) {
        return h;
    }

    let expr = *dag.exprs.get_index(idx).unwrap();
    let nlbv = dag.expr_nlbv[idx];

    // Fast path: no free bvars above cutoff — shift doesn't affect this expression
    if nlbv <= cutoff {
        let h = expr.get_hash();
        memo.insert((idx, shift, cutoff), h);
        return h;
    }

    let h = match expr {
        Expr::Var { dbj_idx, .. } => {
            let shifted = if dbj_idx >= cutoff {
                dbj_idx - shift
            } else {
                dbj_idx
            };
            hash64!(VAR_HASH, shifted)
        }
        Expr::App { fun, arg, .. } => {
            let fh = core_hash(dag, fun.idx(), shift, cutoff, memo);
            let ah = core_hash(dag, arg.idx(), shift, cutoff, memo);
            hash64!(APP_HASH, fh, ah)
        }
        Expr::Lambda {
            binder_name,
            binder_style,
            binder_type,
            body,
            ..
        } => {
            let th = core_hash(dag, binder_type.idx(), shift, cutoff, memo);
            let bh = core_hash(dag, body.idx(), shift, cutoff + 1, memo);
            hash64!(LAMBDA_HASH, binder_name, binder_style, th, bh)
        }
        Expr::Pi {
            binder_name,
            binder_style,
            binder_type,
            body,
            ..
        } => {
            let th = core_hash(dag, binder_type.idx(), shift, cutoff, memo);
            let bh = core_hash(dag, body.idx(), shift, cutoff + 1, memo);
            hash64!(PI_HASH, binder_name, binder_style, th, bh)
        }
        Expr::Let {
            binder_name,
            binder_type,
            val,
            body,
            nondep,
            ..
        } => {
            let th = core_hash(dag, binder_type.idx(), shift, cutoff, memo);
            let vh = core_hash(dag, val.idx(), shift, cutoff, memo);
            let bh = core_hash(dag, body.idx(), shift, cutoff + 1, memo);
            hash64!(LET_HASH, binder_name, th, vh, bh, nondep)
        }
        Expr::Proj {
            ty_name,
            idx: proj_idx,
            structure,
            ..
        } => {
            let sh = core_hash(dag, structure.idx(), shift, cutoff, memo);
            hash64!(PROJ_HASH, ty_name, proj_idx, sh)
        }
        // These have no free bvars — should have been caught by nlbv <= cutoff
        Expr::Sort { .. }
        | Expr::Const { .. }
        | Expr::NatLit { .. }
        | Expr::StringLit { .. }
        | Expr::Local { .. } => expr.get_hash(),
        Expr::Shift { inner, amount, .. } => {
            // OSNF Shift nodes from parse-time normalization: hash the inner core shifted
            core_hash(dag, inner.idx(), shift + amount as u16, cutoff, memo)
        }
    };

    memo.insert((idx, shift, cutoff), h);
    h
}

// ---- OSNF transformation ----

/// OSNF-normalize the export file DAG in place.
///
/// For each expression with `fvar_lb > 0`, computes its core (shifted-down version
/// with `fvar_lb = 0`), inserts the core into the DAG, creates a `Shift(core, fvar_lb, 0)`
/// wrapper, and records the mapping in `ExportFile::osnf_remap`.
///
/// After this, `read_expr` on ExportFile expressions transparently returns the
/// OSNF-normalized version.
pub fn osnf_normalize(export_file: &mut ExportFile) {
    let dag = &mut export_file.dag;
    let original_len = dag.exprs.len();
    let mut osnf_core: Vec<u32> = (0..original_len as u32).collect(); // identity initially
    // memo: (original_idx, shift, cutoff) -> index of core expr in the dag
    let mut core_memo: FxHashMap<(usize, u16, u16), usize> = FxHashMap::default();

    let mut normalized_count = 0u32;
    let mut core_reuse_count = 0u32;

    for idx in 0..original_len {
        let nlbv = dag.expr_nlbv[idx];
        if nlbv == 0 {
            continue;
        }
        let fvar_lb = dag.exprs.get_index(idx).unwrap().get_fvar_lb();
        if fvar_lb == 0 {
            continue;
        }

        // Compute the core: shift_down(expr, fvar_lb, 0)
        let (core_idx, was_new) = compute_core(dag, idx, fvar_lb, 0, &mut core_memo);

        if !was_new {
            core_reuse_count += 1;
        }

        osnf_core[idx] = u32::try_from(core_idx).unwrap();
        normalized_count += 1;
    }

    // Also compute cores for newly created core expressions.
    // Core expressions under binders can have fvar_lb > 0 and need their own cores
    // for consistent canonicalization in mk_shift_cutoff.
    // Iterate until fixpoint (no new expressions created).
    let mut wave = 0u32;
    let mut wave_normalized = 0u32;
    loop {
        let current_len = dag.exprs.len();
        // Extend osnf_core for newly added expressions (identity mapping initially)
        while osnf_core.len() < current_len {
            osnf_core.push(osnf_core.len() as u32);
        }
        let mut new_in_wave = 0u32;
        for idx in original_len..current_len {
            // Skip if already has a non-identity core
            if (osnf_core[idx] as usize) != idx {
                continue;
            }
            let nlbv = dag.expr_nlbv[idx];
            if nlbv == 0 { continue; }
            let fvar_lb = dag.exprs.get_index(idx).unwrap().get_fvar_lb();
            if fvar_lb == 0 { continue; }
            let (core_idx, was_new) = compute_core(dag, idx, fvar_lb, 0, &mut core_memo);
            if !was_new { core_reuse_count += 1; }
            osnf_core[idx] = u32::try_from(core_idx).unwrap();
            new_in_wave += 1;
            wave_normalized += 1;
        }
        // Extend for any newly created expressions in this wave
        let after_len = dag.exprs.len();
        while osnf_core.len() < after_len {
            osnf_core.push(osnf_core.len() as u32);
        }
        wave += 1;
        if new_in_wave == 0 || after_len == current_len {
            break;
        }
    }

    let new_len = dag.exprs.len();
    eprintln!("OSNF normalize: {} + {} expressions normalized ({} waves), {} core reuses, DAG grew from {} to {} ({:+})",
        normalized_count, wave_normalized, wave, core_reuse_count, original_len, new_len,
        new_len as isize - original_len as isize);

    export_file.osnf_core = Some(osnf_core);
}

/// Remap child ExprPtrs in an expression according to the OSNF remap table.
/// Only remaps ExportFile ExprPtrs; TcCtx ptrs are left unchanged.
/// Recursively compute the core of expression `dag[idx]` shifted down by `shift` with `cutoff`.
/// Inserts core expressions into `dag`. Returns (core_index, was_newly_created).
fn compute_core(
    dag: &mut LeanDag,
    idx: usize,
    shift: u16,
    cutoff: u16,
    memo: &mut FxHashMap<(usize, u16, u16), usize>,
) -> (usize, bool) {
    if let Some(&core_idx) = memo.get(&(idx, shift, cutoff)) {
        return (core_idx, false);
    }

    let expr = *dag.exprs.get_index(idx).unwrap();
    let nlbv = dag.expr_nlbv[idx];

    // Fast path: no free bvars above cutoff — shift doesn't affect this expression
    if nlbv <= cutoff {
        memo.insert((idx, shift, cutoff), idx);
        return (idx, false);
    }

    let (core_idx, was_new) = match expr {
        Expr::Var { dbj_idx, .. } => {
            let new_idx = if dbj_idx >= cutoff { dbj_idx - shift } else { dbj_idx };
            let hash = hash64!(VAR_HASH, new_idx);
            let new_var = Expr::Var {
                dbj_idx: new_idx,
                hash,
                fvar_lb: new_idx,
            };
            let (vi, inserted) = dag.exprs.insert_full(new_var);
            if inserted {
                dag.expr_nlbv.push(new_idx + 1);
            }
            (vi, inserted)
        }
        Expr::App { fun, arg, num_loose_bvars: _, has_fvars, .. } => {
            let (fun_core, _) = compute_core(dag, fun.idx(), shift, cutoff, memo);
            let (arg_core, _) = compute_core(dag, arg.idx(), shift, cutoff, memo);
            let fun_ptr: ExprPtr = Ptr::from(DagMarker::ExportFile, fun_core);
            let arg_ptr: ExprPtr = Ptr::from(DagMarker::ExportFile, arg_core);
            let fun_nlbv = dag.expr_nlbv[fun_core];
            let arg_nlbv = dag.expr_nlbv[arg_core];
            let new_nlbv = fun_nlbv.max(arg_nlbv);
            let fun_expr = dag.exprs.get_index(fun_core).unwrap();
            let arg_expr = dag.exprs.get_index(arg_core).unwrap();
            let hash = hash64!(APP_HASH, fun_ptr, arg_ptr);
            let fvar_lb = if new_nlbv == 0 { 0 } else {
                if fun_nlbv == 0 { arg_expr.get_fvar_lb() }
                else if arg_nlbv == 0 { fun_expr.get_fvar_lb() }
                else { fun_expr.get_fvar_lb().min(arg_expr.get_fvar_lb()) }
            };
            let app = Expr::App {
                fun: fun_ptr, arg: arg_ptr, num_loose_bvars: new_nlbv,
                has_fvars, hash, fvar_lb,
            };
            let (ai, inserted) = dag.exprs.insert_full(app);
            if inserted { dag.expr_nlbv.push(new_nlbv); }
            (ai, inserted)
        }
        Expr::Lambda { binder_name, binder_style, binder_type, body, has_fvars, .. } => {
            let (ty_core, _) = compute_core(dag, binder_type.idx(), shift, cutoff, memo);
            let (body_core, _) = compute_core(dag, body.idx(), shift, cutoff + 1, memo);
            make_binder_core(dag, true, binder_name, binder_style, ty_core, body_core, has_fvars)
        }
        Expr::Pi { binder_name, binder_style, binder_type, body, has_fvars, .. } => {
            let (ty_core, _) = compute_core(dag, binder_type.idx(), shift, cutoff, memo);
            let (body_core, _) = compute_core(dag, body.idx(), shift, cutoff + 1, memo);
            make_binder_core(dag, false, binder_name, binder_style, ty_core, body_core, has_fvars)
        }
        Expr::Let { binder_name, binder_type, val, body, nondep, has_fvars, .. } => {
            let (ty_core, _) = compute_core(dag, binder_type.idx(), shift, cutoff, memo);
            let (val_core, _) = compute_core(dag, val.idx(), shift, cutoff, memo);
            let (body_core, _) = compute_core(dag, body.idx(), shift, cutoff + 1, memo);
            let ty_ptr: ExprPtr = Ptr::from(DagMarker::ExportFile, ty_core);
            let val_ptr: ExprPtr = Ptr::from(DagMarker::ExportFile, val_core);
            let body_ptr: ExprPtr = Ptr::from(DagMarker::ExportFile, body_core);
            let ty_e = dag.exprs.get_index(ty_core).unwrap();
            let val_e = dag.exprs.get_index(val_core).unwrap();
            let body_e = dag.exprs.get_index(body_core).unwrap();
            let ty_nlbv = dag.expr_nlbv[ty_core];
            let val_nlbv = dag.expr_nlbv[val_core];
            let body_nlbv = dag.expr_nlbv[body_core];
            let new_nlbv = ty_nlbv.max(val_nlbv.max(body_nlbv.saturating_sub(1)));
            let hash = hash64!(LET_HASH, binder_name, ty_ptr, val_ptr, body_ptr, nondep);
            let fvar_lb = if new_nlbv == 0 { 0 } else {
                let mut lb = u16::MAX;
                if ty_nlbv > 0 { lb = lb.min(ty_e.get_fvar_lb()); }
                if val_nlbv > 0 { lb = lb.min(val_e.get_fvar_lb()); }
                if body_nlbv > 1 || (body_nlbv == 1 && body_e.get_fvar_lb() > 0) {
                    lb = lb.min(body_e.get_fvar_lb().saturating_sub(1));
                }
                if lb == u16::MAX { 0 } else { lb }
            };
            let let_e = Expr::Let {
                binder_name, binder_type: ty_ptr, val: val_ptr, body: body_ptr,
                num_loose_bvars: new_nlbv, has_fvars, hash, nondep,
                fvar_lb,
            };
            let (li, inserted) = dag.exprs.insert_full(let_e);
            if inserted { dag.expr_nlbv.push(new_nlbv); }
            (li, inserted)
        }
        Expr::Proj { ty_name, idx: proj_idx, structure, has_fvars, .. } => {
            let (struct_core, _) = compute_core(dag, structure.idx(), shift, cutoff, memo);
            let struct_ptr: ExprPtr = Ptr::from(DagMarker::ExportFile, struct_core);
            let struct_e = dag.exprs.get_index(struct_core).unwrap();
            let struct_nlbv = dag.expr_nlbv[struct_core];
            let hash = hash64!(PROJ_HASH, ty_name, proj_idx, struct_ptr);
            let fvar_lb = struct_e.get_fvar_lb();
            let proj = Expr::Proj {
                ty_name, idx: proj_idx, structure: struct_ptr,
                num_loose_bvars: struct_nlbv, has_fvars, hash,
                fvar_lb,
            };
            let (pi, inserted) = dag.exprs.insert_full(proj);
            if inserted { dag.expr_nlbv.push(struct_nlbv); }
            (pi, inserted)
        }
        // Closed expressions — already handled by nlbv <= cutoff fast path
        Expr::Sort { .. } | Expr::Const { .. } | Expr::NatLit { .. }
        | Expr::StringLit { .. } | Expr::Local { .. } => (idx, false),
        Expr::Shift { inner, amount, .. } => {
            // OSNF Shift nodes from parse-time normalization: recurse into inner with combined shift
            let (core_idx, was_new) = compute_core(dag, inner.idx(), shift + amount as u16, cutoff, memo);
            (core_idx, was_new)
        }
    };

    memo.insert((idx, shift, cutoff), core_idx);
    (core_idx, was_new)
}

/// Helper: construct a Lambda or Pi core expression from already-computed children.
fn make_binder_core<'a>(
    dag: &mut LeanDag<'a>,
    is_lambda: bool,
    binder_name: crate::util::NamePtr<'a>,
    binder_style: crate::expr::BinderStyle,
    ty_core: usize,
    body_core: usize,
    has_fvars: bool,
) -> (usize, bool) {
    let ty_ptr: ExprPtr<'a> = Ptr::from(DagMarker::ExportFile, ty_core);
    let body_ptr: ExprPtr<'a> = Ptr::from(DagMarker::ExportFile, body_core);
    let ty_e = dag.exprs.get_index(ty_core).unwrap();
    let body_e = dag.exprs.get_index(body_core).unwrap();
    let ty_nlbv = dag.expr_nlbv[ty_core];
    let body_nlbv = dag.expr_nlbv[body_core];
    let new_nlbv = ty_nlbv.max(body_nlbv.saturating_sub(1));
    let tag = if is_lambda { LAMBDA_HASH } else { PI_HASH };
    let hash = hash64!(tag, binder_name, binder_style, ty_ptr, body_ptr);
    let fvar_lb = if new_nlbv == 0 { 0 } else {
        let b_nlbv = body_nlbv;
        let b_lb = body_e.get_fvar_lb().saturating_sub(1);
        if ty_nlbv == 0 && b_nlbv <= 1 { 0 }
        else if ty_nlbv == 0 { b_lb }
        else if b_nlbv <= 1 { ty_e.get_fvar_lb() }
        else { ty_e.get_fvar_lb().min(b_lb) }
    };
    let expr = if is_lambda {
        Expr::Lambda {
            binder_name, binder_style, binder_type: ty_ptr, body: body_ptr,
            num_loose_bvars: new_nlbv, has_fvars, hash,
            fvar_lb,
        }
    } else {
        Expr::Pi {
            binder_name, binder_style, binder_type: ty_ptr, body: body_ptr,
            num_loose_bvars: new_nlbv, has_fvars, hash,
            fvar_lb,
        }
    };
    let (bi, inserted) = dag.exprs.insert_full(expr);
    if inserted { dag.expr_nlbv.push(new_nlbv); }
    (bi, inserted)
}
