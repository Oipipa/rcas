use crate::expr::{Expr, Rational};
use crate::simplify::{simplify, simplify_fully};
use num_traits::{One, Zero};

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
            let (coef, _) = linear_parts(u, var)?;
            if is_const_zero(&coef) {
                return None;
            }
            let u_expr = *u.clone();
            let u_log = Expr::Mul(u_expr.clone().boxed(), log_abs(u_expr.clone()).boxed());
            let numerator = Expr::Sub(u_log.boxed(), u_expr.clone().boxed());
            Some(scale_by_coeff(numerator, coef))
        }
        _ => None,
    }
}

fn is_const_zero(expr: &Expr) -> bool {
    matches!(simplify_fully(expr.clone()), Expr::Constant(c) if c.is_zero())
}

fn invert_coeff(expr: Expr) -> Expr {
    match expr {
        Expr::Constant(c) => Expr::Constant(Rational::one() / c),
        Expr::Neg(inner) => Expr::Neg(invert_coeff(*inner).boxed()),
        Expr::Div(num, den) => Expr::Div(den, num),
        Expr::Pow(base, exp) => match &*exp {
            Expr::Constant(k) => Expr::Pow(base, Expr::Constant(-k.clone()).boxed()),
            _ => Expr::Div(
                Expr::Constant(Rational::one()).boxed(),
                Expr::Pow(base, exp).boxed(),
            ),
        },
        other => Expr::Div(Expr::Constant(Rational::one()).boxed(), other.boxed()),
    }
}

fn scale_by_coeff(expr: Expr, coeff: Expr) -> Expr {
    simplify(Expr::Mul(expr.boxed(), invert_coeff(coeff).boxed()))
}
