use crate::core::expr::Expr;
use crate::solver::{LinearDiagnostics, LinearResult, NonLinearStatus, SolveResult};
use num_traits::Zero;

use super::pretty;

/// Render a `SolveResult` into human-readable lines for CLI/examples.
pub fn solve_summary(result: &SolveResult) -> Vec<String> {
    match result {
        SolveResult::Linear(linear) => pretty_linear_result(linear),
        SolveResult::NonLinear(info) => {
            let mut lines =
                vec!["Non-linear system detected; analytic solver not yet applied.".to_string()];
            if !info.nonlinear_equations.is_empty() {
                lines.push(format!(
                    "Non-linear equations (0-based indices): {:?}",
                    info.nonlinear_equations
                ));
            }
            let status = match info.status {
                NonLinearStatus::Detected => "Detected",
                NonLinearStatus::NotImplemented => "NotImplemented",
            };
            lines.push(format!("Status: {status}"));
            lines
        }
    }
}

fn pretty_linear_result(result: &LinearResult) -> Vec<String> {
    match result {
        LinearResult::Unique(sol) => {
            let mut lines = vec!["Unique solution:".to_string()];
            for (var, value) in sol.variables.iter().zip(sol.values.iter()) {
                lines.push(format!("{var} = {}", pretty(value)));
            }
            push_diag(&mut lines, &sol.diagnostics);
            lines
        }
        LinearResult::Infinite(family) => {
            let mut lines = vec![format!(
                "Infinite solutions (params: {}):",
                family.params.join(", ")
            )];
            for (i, var) in family.variables.iter().enumerate() {
                let mut parts = vec![pretty(&family.particular[i])];
                for (param, basis_vec) in family.params.iter().zip(family.basis.iter()) {
                    let coeff = &basis_vec[i];
                    if coeff_nonzero(coeff) {
                        parts.push(format!("{}*{}", pretty(coeff), param));
                    }
                }
                lines.push(format!("{var} = {}", parts.join(" + ")));
            }
            push_diag(&mut lines, &family.diagnostics);
            lines
        }
        LinearResult::Inconsistent(info) => {
            let mut lines = vec!["No solution (inconsistent system).".to_string()];
            if let Some(row) = info.diagnostics.inconsistent_row {
                lines.push(format!("Inconsistent reduced row index: {row}"));
            }
            push_diag(&mut lines, &info.diagnostics);
            lines
        }
    }
}

fn coeff_nonzero(expr: &Expr) -> bool {
    match expr {
        Expr::Constant(r) => !r.is_zero(),
        _ => true,
    }
}

fn push_diag(lines: &mut Vec<String>, diag: &LinearDiagnostics) {
    lines.push(format!("Rank: {}", diag.rank));
    if let Some(det) = &diag.determinant {
        lines.push(format!("Determinant: {}", det));
    }
    if !diag.pivot_columns.is_empty() {
        lines.push(format!("Pivot columns: {:?}", diag.pivot_columns));
    }
    if !diag.free_columns.is_empty() {
        lines.push(format!("Free columns: {:?}", diag.free_columns));
    }
}
