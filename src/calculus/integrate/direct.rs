use crate::calculus::differentiate;
use crate::core::expr::{Expr, Rational};
use crate::simplify::simplify_fully;
use num_traits::{One, Zero};

use super::limits::TRANSFORM_SIZE_LIMIT;
use super::parts::extract_log_linear;
use super::substitution::integrate_log_derivative;
use super::{
    apply_constant_factor, distribute_product_with_addition, exponential, expr_size,
    flatten_product, is_constant_wrt, is_one_expr, is_zero_expr, log_abs, logarithmic,
    polynomial, rational, rebuild_product, split_constant_factors, trig,
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

fn distribute_for_log_linear(expr: &Expr, var: &str) -> Expr {
    match expr {
        Expr::Add(a, b) => Expr::Add(
            distribute_for_log_linear(a, var).boxed(),
            distribute_for_log_linear(b, var).boxed(),
        ),
        Expr::Sub(a, b) => Expr::Sub(
            distribute_for_log_linear(a, var).boxed(),
            distribute_for_log_linear(b, var).boxed(),
        ),
        _ => {
            let (const_factor, factors) = flatten_product(expr);
            if factors.len() > 1 {
                if let Some(distributed) =
                    distribute_product_with_addition(const_factor, factors, var)
                {
                    let base_size = expr_size(expr);
                    let dist_size = expr_size(&distributed);
                    if dist_size <= TRANSFORM_SIZE_LIMIT && dist_size <= base_size + 8 {
                        return distribute_for_log_linear(&distributed, var);
                    }
                }
            }
            expr.clone()
        }
    }
}

fn is_inv_var_factor(expr: &Expr, var: &str) -> bool {
    matches!(
        expr,
        Expr::Pow(base, exp)
            if matches!(&**base, Expr::Variable(name) if name == var)
                && matches!(&**exp, Expr::Constant(k) if k == &(-Rational::one()))
    )
}

fn strip_single_inv_var(factors: Vec<Expr>, var: &str) -> (bool, Vec<Expr>) {
    let mut removed = false;
    let mut kept = Vec::new();
    for factor in factors {
        if !removed && is_inv_var_factor(&factor, var) {
            removed = true;
            continue;
        }
        kept.push(factor);
    }
    (removed, kept)
}

fn log_linear_candidate(remainder: &Expr, var: &str) -> Expr {
    let (const_factor, factors) = flatten_product(remainder);
    let (removed, new_factors) = strip_single_inv_var(factors, var);
    if removed {
        rebuild_product(const_factor, new_factors)
    } else {
        simplify_fully(Expr::Mul(
            Expr::Variable(var.to_string()).boxed(),
            remainder.clone().boxed(),
        ))
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
        Expr::Add(a, b) => {
            let left = integrate_linear_ops(a, var, include_log_derivative);
            let right = integrate_linear_ops(b, var, include_log_derivative);
            match (left, right) {
                (Some(l), Some(r)) => Some(Expr::Add(l.boxed(), r.boxed())),
                _ => None,
            }
        }
        Expr::Sub(a, b) => {
            let left = integrate_linear_ops(a, var, include_log_derivative);
            let right = integrate_linear_ops(b, var, include_log_derivative);
            match (left, right) {
                (Some(l), Some(r)) => Some(Expr::Sub(l.boxed(), r.boxed())),
                _ => None,
            }
        }
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

    let mut distributed_candidate = None;
    let (dist_const, dist_factors) = flatten_product(expr);
    if dist_factors.len() > 1 {
        if let Some(distributed) =
            distribute_product_with_addition(dist_const, dist_factors, var)
        {
            let base_size = expr_size(expr);
            let dist_size = expr_size(&distributed);
            if dist_size <= TRANSFORM_SIZE_LIMIT && dist_size <= base_size + 8 {
                if let Some(result) =
                    integrate_linear_ops(&distributed, var, include_log_derivative)
                {
                    return Some(result);
                }
                distributed_candidate = Some(distributed);
            }
        }
    }

    if include_log_derivative {
        let log_source = distributed_candidate.as_ref().unwrap_or(expr);
        let log_source = distribute_for_log_linear(log_source, var);
        let extracted = extract_log_linear(&log_source, var);
        if let Some((log_coeff, remainder)) = extracted {
            let candidate = log_linear_candidate(&remainder, var);
            if expr_size(&candidate) <= TRANSFORM_SIZE_LIMIT {
                let candidate_derivative = simplify_fully(differentiate(var, &candidate));
                let diff = Expr::Sub(candidate_derivative.boxed(), log_coeff.boxed());
                if is_zero_expr(&diff) {
                    let log_term = log_abs(Expr::Variable(var.to_string()));
                    return Some(Expr::Mul(log_term.boxed(), candidate.boxed()));
                }
            }
        }
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
