use crate::core::expr::Expr;

use super::classify::is_rational_like;
use super::rational;

pub(super) fn integrate_partial_fractions(expr: &Expr, var: &str) -> Option<Expr> {
    if !is_rational_like(expr, var) {
        return None;
    }
    rational::integrate(expr, var)
}
