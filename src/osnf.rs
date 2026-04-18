//! Outermost-Shift Normal Form (OSNF) — now handled by ExprPtr at parse time.
//!
//! With the ExprPtr refactoring, OSNF normalization is performed during parsing
//! by the parser itself. There are no Shift nodes in the DAG. Each expression
//! in the DAG is already a core, and shifts are carried in ExprPtr values.
//!
//! These stub functions remain for API compatibility.

use crate::util::ExportFile;

/// Print OSNF stats. With ExprPtr, all expressions are already OSNF-normalized at parse time.
pub fn compute_osnf_stats(export_file: &ExportFile) {
    let dag = &export_file.dag;
    let n = dag.exprs.len();
    let open = dag.expr_nlbv.iter().filter(|&&nlbv| nlbv > 0).count();
    eprintln!("OSNF stats: DAG has {} exprs ({} open, {} closed). ExprPtr handles OSNF automatically.",
        n, open, n - open);
}

/// OSNF normalize. With ExprPtr, this is a no-op — OSNF is enforced at parse time.
pub fn osnf_normalize(_export_file: &mut ExportFile) {
    // No-op: ExprPtr refactoring eliminates the need for post-parse OSNF normalization.
}
