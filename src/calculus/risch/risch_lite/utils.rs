use crate::calculus::risch::expr_utils::expr_any;
use crate::core::expr::Expr;

pub(super) fn contains_subexpr(expr: &Expr, target: &Expr) -> bool {
    expr_any(expr, &mut |node| node == target)
}
