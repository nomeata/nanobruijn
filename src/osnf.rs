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
use crate::util::{ExportFile, FxHashMap, LeanDag};

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
        Expr::Shift { .. } => {
            panic!("Shift nodes should not appear in export file DAG")
        }
    };

    memo.insert((idx, shift, cutoff), h);
    h
}
