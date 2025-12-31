use crate::expr::{Expr, Rational};
use num_traits::Zero;

use super::{linear_parts, log_abs};

pub fn is_log(expr: &Expr) -> bool {
    match expr {
        Expr::Div(a, b) => matches!(
            (&**a, &**b),
            (Expr::Constant(r), Expr::Variable(_))
                if *r == Rational::from_integer(1.into())
        ),
        Expr::Log(_) => true,
        _ => false,
    }
}

pub fn integrate(expr: &Expr, var: &str) -> Option<Expr> {
    match expr {
        Expr::Div(a, b) => match (&**a, &**b) {
            (Expr::Constant(r), Expr::Variable(v))
                if *r == Rational::from_integer(1.into()) && v == var =>
            {
                Some(log_abs(Expr::Variable(v.clone())))
            }
            _ => None,
        },
        Expr::Log(u) => {
            if let Some((coef, _, v)) = linear_parts(u) {
                if v == var && !coef.is_zero() {
                    let u_expr = *u.clone();
                    let u_log = Expr::Mul(u_expr.clone().boxed(), log_abs(u_expr.clone()).boxed());
                    let numerator = Expr::Sub(u_log.boxed(), u_expr.clone().boxed());
                    return Some(Expr::Div(numerator.boxed(), Expr::Constant(coef).boxed()));
                }
            }
            None
        }
        _ => None,
    }
}
