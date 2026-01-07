use num_bigint::BigInt;
use num_traits::One;

use crate::core::expr::{Expr, Rational};

pub(super) fn extract_rational_const(expr: &Expr) -> Option<Rational> {
    match expr {
        Expr::Constant(c) => Some(c.clone()),
        Expr::Neg(inner) => extract_rational_const(inner).map(|c| -c),
        _ => None,
    }
}

pub(super) fn pow_expr_signed(base: &Expr, exp: i64) -> Expr {
    if exp == 0 {
        Expr::Constant(Rational::one())
    } else {
        Expr::Pow(
            base.clone().boxed(),
            Expr::Constant(Rational::from_integer(BigInt::from(exp))).boxed(),
        )
    }
}
