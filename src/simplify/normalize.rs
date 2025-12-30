use crate::expr::Expr;
use crate::simplify::simplify;

/// Basic normalization wrapper; extend with ordering/factoring rules as the CAS grows.
pub fn normalize(expr: Expr) -> Expr {
    simplify(expr)
}
