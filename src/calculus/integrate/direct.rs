use crate::core::expr::{Expr, Rational};
use num_traits::{One, Zero};

use super::substitution::integrate_log_derivative;
use super::{
    apply_constant_factor, exponential, is_constant_wrt, is_one_expr, is_zero_expr,
    logarithmic, polynomial, rational, rebuild_product, split_constant_factors, trig,
};

fn integrate_known(expr: &Expr, var: &str, include_log_derivative: bool) -> Option<Expr> {
    let direct = polynomial::integrate(expr, var)
        .or_else(|| rational::integrate(expr, var))
        .or_else(|| trig::integrate(expr, var))
        .or_else(|| exponential::integrate(expr, var))
        .or_else(|| logarithmic::integrate(expr, var));
    if include_log_derivative {
        direct.or_else(|| integrate_log_derivative(expr, var))
    } else {
        direct
    }
}

fn integrate_linear_ops(expr: &Expr, var: &str, include_log_derivative: bool) -> Option<Expr> {
    if is_constant_wrt(expr, var) {
        return Some(Expr::Mul(
            expr.clone().boxed(),
            Expr::Variable(var.to_string()).boxed(),
        ));
    }

    let direct = match expr {
        Expr::Add(a, b) => Some(Expr::Add(
            integrate_linear_ops(a, var, include_log_derivative)?.boxed(),
            integrate_linear_ops(b, var, include_log_derivative)?.boxed(),
        )),
        Expr::Sub(a, b) => Some(Expr::Sub(
            integrate_linear_ops(a, var, include_log_derivative)?.boxed(),
            integrate_linear_ops(b, var, include_log_derivative)?.boxed(),
        )),
        Expr::Neg(inner) => integrate_linear_ops(inner, var, include_log_derivative)
            .map(|r| Expr::Neg(r.boxed())),
        Expr::Div(num, den) => match (&**num, &**den) {
            (other, Expr::Constant(c)) => integrate_linear_ops(other, var, include_log_derivative)
                .map(|r| Expr::Div(r.boxed(), Expr::Constant(c.clone()).boxed())),
            _ => integrate_known(expr, var, include_log_derivative),
        },
        Expr::Mul(a, b) => match (&**a, &**b) {
            (Expr::Constant(c), other) | (other, Expr::Constant(c)) => {
                integrate_linear_ops(other, var, include_log_derivative)
                    .map(|r| Expr::Mul(Expr::Constant(c.clone()).boxed(), r.boxed()))
            }
            _ => integrate_known(expr, var, include_log_derivative),
        },
        _ => integrate_known(expr, var, include_log_derivative),
    };

    if direct.is_some() {
        return direct;
    }

    let (const_expr, factors) = split_constant_factors(expr, var);
    if is_zero_expr(&const_expr) {
        return Some(Expr::Constant(Rational::zero()));
    }
    if !is_one_expr(&const_expr) {
        let rest = rebuild_product(Rational::one(), factors);
        if let Some(result) = integrate_linear_ops(&rest, var, include_log_derivative) {
            return Some(apply_constant_factor(const_expr, result));
        }
    }

    None
}

pub(super) fn integrate_direct(expr: &Expr, var: &str) -> Option<Expr> {
    integrate_linear_ops(expr, var, true)
}

pub(super) fn integrate_basic(expr: &Expr, var: &str) -> Option<Expr> {
    integrate_linear_ops(expr, var, false)
}
