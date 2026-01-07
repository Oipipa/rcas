use crate::calculus::risch::{risch, risch_lite};
use crate::core::expr::Expr;

pub(super) fn analyze_lite_with_retry(
    expr: &Expr,
    original_expr: &Expr,
    var: &str,
) -> risch_lite::RischLiteOutcome {
    let mut outcome = risch_lite::analyze(expr, var);
    if matches!(outcome, risch_lite::RischLiteOutcome::Indeterminate { .. }) {
        let retry = risch_lite::analyze(original_expr, var);
        if !matches!(retry, risch_lite::RischLiteOutcome::Indeterminate { .. }) {
            outcome = retry;
        }
    }
    outcome
}

pub(super) fn analyze_full(expr: &Expr, var: &str) -> risch::RischOutcome {
    risch::analyze(expr, var)
}
