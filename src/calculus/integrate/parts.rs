use std::collections::HashMap;

use num_traits::{One, Zero};

use crate::calculus::differentiate;
use crate::core::expr::{Expr, Rational};
use crate::simplify::{simplify, simplify_fully};
use crate::ui::pretty;

use super::limits::{IBP_RECURSION_LIMIT, TABULAR_STEP_LIMIT, TRANSFORM_SIZE_LIMIT};
use super::polynomial;
use super::{
    combine_algebraic_factors, combine_var_powers, distribute_product_with_addition, expr_size,
    flatten_product, integrate_basic, integrate_direct, is_one_expr, is_zero_expr, linear_parts,
    log_abs, rebuild_product, split_constant_factors, to_rational_candidate,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum LiateRank {
    Log,
    InverseTrig,
    Algebraic,
    Trig,
    Exponential,
}

fn factor_rank(expr: &Expr, var: &str) -> Option<LiateRank> {
    match expr {
        Expr::Log(_) => Some(LiateRank::Log),
        Expr::Atan(_)
        | Expr::Asin(_)
        | Expr::Acos(_)
        | Expr::Asec(_)
        | Expr::Acsc(_)
        | Expr::Acot(_)
        | Expr::Asinh(_)
        | Expr::Acosh(_)
        | Expr::Atanh(_) => Some(LiateRank::InverseTrig),
        e if polynomial::is_polynomial(e, var) => Some(LiateRank::Algebraic),
        Expr::Sin(_)
        | Expr::Cos(_)
        | Expr::Tan(_)
        | Expr::Sec(_)
        | Expr::Csc(_)
        | Expr::Cot(_)
        | Expr::Sinh(_)
        | Expr::Cosh(_)
        | Expr::Tanh(_) => Some(LiateRank::Trig),
        Expr::Exp(_) => Some(LiateRank::Exponential),
        Expr::Pow(base, _) => factor_rank(base, var),
        _ => None,
    }
}

pub(super) fn integration_by_parts(expr: &Expr, var: &str) -> Option<(Expr, String)> {
    if let Some(result) = integration_by_parts_tabular(expr, var) {
        return Some(result);
    }
    let mut memo = HashMap::new();
    let mut best_size = usize::MAX;
    integrate_by_parts_recursive(expr, var, &mut memo, 0, &mut best_size)
}

fn integrate_by_parts_recursive(
    expr: &Expr,
    var: &str,
    memo: &mut HashMap<Expr, Option<Expr>>,
    depth: usize,
    best_size: &mut usize,
) -> Option<(Expr, String)> {
    if depth >= IBP_RECURSION_LIMIT {
        return None;
    }
    if let Some(result) = memo.get(expr) {
        return result.clone().map(|r| (r, String::new()));
    }

    if let Some((result, note)) = integration_by_parts_tabular(expr, var) {
        memo.insert(expr.clone(), Some(result.clone()));
        return Some((result, note));
    }

    let (const_expr, factors) = split_constant_factors(expr, var);
    if is_zero_expr(&const_expr) {
        let zero = Expr::Constant(Rational::zero());
        memo.insert(expr.clone(), Some(zero.clone()));
        return Some((zero, String::new()));
    }
    if !is_one_expr(&const_expr) {
        memo.insert(expr.clone(), None);
        let rest_expr = rebuild_product(Rational::one(), factors.clone());
        if let Some((res, note)) =
            integrate_by_parts_recursive(&rest_expr, var, memo, depth + 1, best_size)
        {
            let scaled = simplify(Expr::Mul(const_expr.boxed(), res.boxed()));
            memo.insert(expr.clone(), Some(scaled.clone()));
            return Some((scaled, note));
        }
        return None;
    }

    let factors = combine_algebraic_factors(factors, var);
    if factors.len() < 2 {
        let direct = integrate_basic(expr, var);
        if let Some(res) = direct.clone() {
            memo.insert(expr.clone(), Some(res.clone()));
            return Some((res, String::new()));
        }
        memo.insert(expr.clone(), None);
        return None;
    }
    memo.insert(expr.clone(), None);
    let expr_size_current = expr_size(expr);
    if expr_size_current >= *best_size {
        return None;
    }
    *best_size = expr_size_current.min(*best_size);

    let mut candidates: Vec<(usize, LiateRank)> = factors
        .iter()
        .enumerate()
        .filter_map(|(i, f)| factor_rank(f, var).map(|r| (i, r)))
        .collect();
    candidates.sort_by_key(|(_, rank)| *rank);

    for (u_idx, u_kind) in candidates {
        let u = factors[u_idx].clone();
        let dv_factors: Vec<Expr> = factors
            .iter()
            .enumerate()
            .filter_map(|(i, f)| if i == u_idx { None } else { Some(f.clone()) })
            .collect();
        let dv_expr = rebuild_product(Rational::one(), dv_factors);
        let Some(v) = integrate_basic(&dv_expr, var) else {
            continue;
        };
        let du = simplify_fully(differentiate(var, &u));
        let u_term = match u.clone() {
            Expr::Log(inner) => log_abs(*inner),
            other => other,
        };
        let uv = Expr::Mul(u_term.boxed(), v.clone().boxed());
        let vdu = Expr::Mul(v.boxed(), du.boxed());
        let (vdu_const_raw, vdu_factors_raw) = super::flatten_product(&vdu);
        let (vdu_const, vdu_factors) = combine_var_powers(vdu_const_raw, vdu_factors_raw, var);
        let vdu_normalized = rebuild_product(vdu_const.clone(), vdu_factors.clone());
        let vdu_simplified = simplify_fully(vdu_normalized.clone());
        let mut vdu_candidates = vec![vdu_normalized, vdu_simplified];
        if let Some(distributed) =
            distribute_product_with_addition(vdu_const.clone(), vdu_factors.clone(), var)
        {
            vdu_candidates.push(distributed);
        }
        if let Some(rationalized) = to_rational_candidate(vdu_const, &vdu_factors) {
            vdu_candidates.push(rationalized);
        }
        vdu_candidates.sort_by_key(|e| expr_size(e));
        let mut integral_vdu = None;
        for candidate in vdu_candidates {
            if let Some(res) = integrate_direct(&candidate, var) {
                integral_vdu = Some(res);
                break;
            }
            let candidate_size = expr_size(&candidate);
            if candidate_size > TRANSFORM_SIZE_LIMIT || candidate_size > expr_size_current + 8 {
                continue;
            }
            if let Some(res) =
                integrate_by_parts_recursive(&candidate, var, memo, depth + 1, best_size)
                    .map(|r| r.0)
            {
                integral_vdu = Some(res);
                break;
            }
        }
        let Some(integral_vdu) = integral_vdu else {
            continue;
        };
        let result = simplify(Expr::Sub(uv.boxed(), integral_vdu.boxed()));
        let note = format!(
            "u={} ({u_kind:?}), dv={}",
            pretty(&u),
            pretty(&dv_expr)
        );
        memo.insert(expr.clone(), Some(result.clone()));
        return Some((result, note));
    }

    None
}

pub(super) fn integration_by_parts_tabular(expr: &Expr, var: &str) -> Option<(Expr, String)> {
    let (const_expr, factors) = split_constant_factors(expr, var);
    if is_zero_expr(&const_expr) {
        return Some((Expr::Constant(Rational::zero()), String::from("tabular-ibp")));
    }
    if !is_one_expr(&const_expr) {
        let rest = rebuild_product(Rational::one(), factors.clone());
        if let Some((result, note)) = integration_by_parts_tabular(&rest, var) {
            let scaled = simplify(Expr::Mul(const_expr.boxed(), result.boxed()));
            return Some((scaled, note));
        }
        return None;
    }

    let factors = combine_algebraic_factors(factors, var);
    if factors.len() != 2 {
        return None;
    }

    let (poly_factor, other_factor) = if polynomial::is_polynomial(&factors[0], var) {
        (factors[0].clone(), factors[1].clone())
    } else if polynomial::is_polynomial(&factors[1], var) {
        (factors[1].clone(), factors[0].clone())
    } else {
        return None;
    };

    let degree = polynomial::degree(&poly_factor, var)?;
    if degree == 0 || degree > TABULAR_STEP_LIMIT {
        return None;
    }

    if polynomial::is_polynomial(&other_factor, var) {
        return None;
    }

    if let Expr::Log(arg) = &other_factor {
        let result = integrate_polynomial_times_log(&poly_factor, arg, var)?;
        return Some((result, String::from("tabular-ibp-log")));
    }

    if !matches!(
        other_factor,
        Expr::Exp(_) | Expr::Sin(_) | Expr::Cos(_) | Expr::Sinh(_) | Expr::Cosh(_)
    ) {
        return None;
    }

    let mut derivatives = Vec::new();
    let mut current = poly_factor.clone();
    for _ in 0..=degree {
        if is_zero_expr(&current) {
            break;
        }
        derivatives.push(simplify_fully(current.clone()));
        current = simplify_fully(differentiate(var, &current));
    }
    if derivatives.is_empty() || derivatives.len() > TABULAR_STEP_LIMIT {
        return None;
    }

    let mut integrals = Vec::new();
    let mut kernel = other_factor.clone();
    for _ in 0..derivatives.len() {
        let next = integrate_basic(&kernel, var)?;
        if expr_size(&next) > TRANSFORM_SIZE_LIMIT {
            return None;
        }
        integrals.push(simplify(next.clone()));
        kernel = next;
    }

    let mut terms = Vec::new();
    for (idx, deriv) in derivatives.into_iter().enumerate() {
        let term = Expr::Mul(deriv.boxed(), integrals[idx].clone().boxed());
        let signed = if idx % 2 == 1 {
            Expr::Neg(term.boxed())
        } else {
            term
        };
        terms.push(signed);
    }
    let result = simplify(
        terms
            .into_iter()
            .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
            .unwrap(),
    );

    if expr_size(&result) > TRANSFORM_SIZE_LIMIT {
        return None;
    }

    Some((result, String::from("tabular-ibp")))
}

fn integrate_polynomial_times_log(poly: &Expr, log_arg: &Expr, var: &str) -> Option<Expr> {
    let base = match log_arg {
        Expr::Abs(inner) => inner.as_ref().clone(),
        _ => log_arg.clone(),
    };
    let (coef, _) = linear_parts(&base, var)?;
    if is_zero_expr(&coef) {
        return None;
    }

    let poly_integral = polynomial::integrate(poly, var)?;
    let log_term = Expr::Mul(poly_integral.clone().boxed(), log_abs(base.clone()).boxed());
    let ratio = simplify(Expr::Div(coef.boxed(), base.boxed()));
    let vdu = simplify(Expr::Mul(poly_integral.boxed(), ratio.boxed()));
    let vdu_integral = integrate_direct(&vdu, var)?;
    Some(simplify(Expr::Sub(log_term.boxed(), vdu_integral.boxed())))
}

fn is_log_var(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Log(inner) => match &**inner {
            Expr::Variable(name) if name == var => true,
            Expr::Abs(inner) => matches!(&**inner, Expr::Variable(name) if name == var),
            _ => false,
        },
        _ => false,
    }
}

fn contains_log_var(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Log(inner) => match &**inner {
            Expr::Variable(name) if name == var => true,
            Expr::Abs(inner) => matches!(&**inner, Expr::Variable(name) if name == var),
            _ => false,
        },
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => contains_log_var(a, var) || contains_log_var(b, var),
        Expr::Neg(inner)
        | Expr::Sin(inner)
        | Expr::Cos(inner)
        | Expr::Tan(inner)
        | Expr::Sec(inner)
        | Expr::Csc(inner)
        | Expr::Cot(inner)
        | Expr::Atan(inner)
        | Expr::Asin(inner)
        | Expr::Acos(inner)
        | Expr::Asec(inner)
        | Expr::Acsc(inner)
        | Expr::Acot(inner)
        | Expr::Sinh(inner)
        | Expr::Cosh(inner)
        | Expr::Tanh(inner)
        | Expr::Asinh(inner)
        | Expr::Acosh(inner)
        | Expr::Atanh(inner)
        | Expr::Exp(inner)
        | Expr::Abs(inner) => contains_log_var(inner, var),
        Expr::Variable(_) | Expr::Constant(_) => false,
    }
}

fn extract_log_linear_inner(expr: &Expr, var: &str) -> Option<(Option<Expr>, Expr)> {
    match expr {
        Expr::Add(a, b) => {
            let (coeff_a, rem_a) = extract_log_linear_inner(a, var)?;
            let (coeff_b, rem_b) = extract_log_linear_inner(b, var)?;
            let coeff = match (coeff_a, coeff_b) {
                (Some(ca), Some(cb)) => Some(simplify(Expr::Add(ca.boxed(), cb.boxed()))),
                (Some(ca), None) => Some(ca),
                (None, Some(cb)) => Some(cb),
                (None, None) => None,
            };
            let remainder = simplify(Expr::Add(rem_a.boxed(), rem_b.boxed()));
            Some((coeff, remainder))
        }
        Expr::Sub(a, b) => {
            let (coeff_a, rem_a) = extract_log_linear_inner(a, var)?;
            let (coeff_b, rem_b) = extract_log_linear_inner(b, var)?;
            let coeff = match (coeff_a, coeff_b) {
                (Some(ca), Some(cb)) => Some(simplify(Expr::Sub(ca.boxed(), cb.boxed()))),
                (Some(ca), None) => Some(ca),
                (None, Some(cb)) => Some(simplify(Expr::Neg(cb.boxed()))),
                (None, None) => None,
            };
            let remainder = simplify(Expr::Sub(rem_a.boxed(), rem_b.boxed()));
            Some((coeff, remainder))
        }
        Expr::Mul(_, _) => {
            let (const_factor, factors) = flatten_product(expr);
            let mut log_count = 0;
            let mut others = Vec::new();
            for factor in factors {
                if is_log_var(&factor, var) {
                    log_count += 1;
                } else if contains_log_var(&factor, var) {
                    return None;
                } else {
                    others.push(factor);
                }
            }
            match log_count {
                0 => Some((None, expr.clone())),
                1 => {
                    let coeff = rebuild_product(const_factor, others);
                    Some((Some(coeff), Expr::Constant(Rational::zero())))
                }
                _ => None,
            }
        }
        Expr::Log(_) if is_log_var(expr, var) => Some((
            Some(Expr::Constant(Rational::one())),
            Expr::Constant(Rational::zero()),
        )),
        _ => {
            if contains_log_var(expr, var) {
                None
            } else {
                Some((None, expr.clone()))
            }
        }
    }
}

pub(super) fn extract_log_linear(expr: &Expr, var: &str) -> Option<(Expr, Expr)> {
    let (coeff, remainder) = extract_log_linear_inner(expr, var)?;
    let coeff = coeff?;
    if is_zero_expr(&coeff) {
        return None;
    }
    Some((coeff, remainder))
}
