use num_bigint::BigInt;

use crate::core::expr::Expr;

use super::cache::{IS_POLY_CACHE, NON_ELEM_CACHE, POLY_CACHE};
use super::exponential;
use super::logarithmic;
use super::polynomial;
use super::rational;
use super::trig;
use super::types::{IntegrandKind, NonElementaryKind};
use super::{constant_ratio, is_constant_wrt, split_constant_factors};
use super::substitution::integrate_by_substitution;

pub(super) fn classify_integrand(expr: &Expr, var: &str) -> IntegrandKind {
    if let Some(non_elem) = detect_non_elementary(expr, var) {
        return IntegrandKind::NonElementary(non_elem);
    }
    if let Expr::Mul(a, b) = expr {
        if matches!(&**a, Expr::Constant(_)) {
            let inner = classify_integrand(b, var);
            if !matches!(inner, IntegrandKind::Unknown | IntegrandKind::Sum) {
                return inner;
            }
        }
        if matches!(&**b, Expr::Constant(_)) {
            let inner = classify_integrand(a, var);
            if !matches!(inner, IntegrandKind::Unknown | IntegrandKind::Sum) {
                return inner;
            }
        }
    }
    if let Some(linear) = rational::rational_kind(expr, var) {
        return IntegrandKind::Rational { linear };
    }
    if polynomial::is_polynomial(expr, var) {
        return IntegrandKind::Polynomial;
    }
    if is_rational_like(expr, var) {
        return IntegrandKind::Rational { linear: false };
    }
    if trig::is_trig(expr) {
        return IntegrandKind::Trig;
    }
    if exponential::is_exp(expr) {
        return IntegrandKind::Exponential;
    }
    if logarithmic::is_log(expr) {
        return IntegrandKind::Logarithmic;
    }
    match expr {
        Expr::Mul(a, b) => IntegrandKind::Product(
            Box::new(classify_integrand(a, var)),
            Box::new(classify_integrand(b, var)),
        ),
        Expr::Add(_, _) | Expr::Sub(_, _) => IntegrandKind::Sum,
        _ => IntegrandKind::Unknown,
    }
}

pub(crate) fn detect_non_elementary(expr: &Expr, var: &str) -> Option<NonElementaryKind> {
    if is_constant_wrt(expr, var) {
        return None;
    }
    let key = (expr.clone(), var.to_string());
    if let Some(cached) = NON_ELEM_CACHE.with(|c| c.borrow().get(&key).cloned()) {
        return cached;
    }
    let result = detect_non_elementary_uncached(expr, var);
    NON_ELEM_CACHE.with(|c| {
        let mut map = c.borrow_mut();
        if map.len() > 1024 {
            map.clear();
        }
        map.insert(key, result.clone());
    });
    result
}

fn detect_non_elementary_uncached(expr: &Expr, var: &str) -> Option<NonElementaryKind> {
    if is_constant_wrt(expr, var) {
        return None;
    }

    if exponential::is_exp_poly_product(expr, var) {
        return None;
    }

    if integrate_by_substitution(expr, var).is_some() {
        return None;
    }

    if let Some(kind) = fast_non_elementary(expr, var) {
        return Some(kind);
    }

    match expr {
        Expr::Mul(_, _) | Expr::Div(_, _) | Expr::Neg(_) => {
            let (_, var_factors) = split_constant_factors(expr, var);
            if let Some(kind) = detect_power_self_log(&var_factors, var) {
                return Some(kind);
            }
            for factor in &var_factors {
                if is_radical_pow(factor) {
                    if is_special_function_radical(factor, &var_factors, var) {
                        return Some(NonElementaryKind::SpecialFunctionNeeded);
                    }
                    continue;
                }
                if let Some(kind) = detect_non_elementary_core(factor, var) {
                    return Some(kind);
                }
            }
        }
        _ => {}
    }

    detect_non_elementary_core(expr, var)
}

fn fast_non_elementary(expr: &Expr, var: &str) -> Option<NonElementaryKind> {
    match expr {
        Expr::Exp(arg) => {
            if polynomial_degree_gt(arg, var, 1) {
                return Some(NonElementaryKind::ExpOfPolynomial);
            }
        }
        Expr::Pow(base, exp) => {
            if is_pow_self(base, exp, var) {
                return Some(NonElementaryKind::PowerSelf);
            }
            if is_half_integer_exp(exp) && polynomial_degree_gt(base, var, 2) {
                return Some(NonElementaryKind::SpecialFunctionNeeded);
            }
        }
        Expr::Div(num, den) => {
            if let Some(kind) = trig_over_argument_kind(num, den, var) {
                return Some(kind);
            }
        }
        _ => {}
    }
    None
}

fn is_special_function_radical(factor: &Expr, factors: &[Expr], var: &str) -> bool {
    let Expr::Pow(base, exp) = factor else {
        return false;
    };
    let exponent = match &**exp {
        Expr::Constant(k) => k.clone(),
        Expr::Neg(inner) => match &**inner {
            Expr::Constant(k) => -k.clone(),
            _ => return false,
        },
        _ => return false,
    };
    if exponent.is_integer() {
        return false;
    }
    let deg = match polynomial_degree(base, var) {
        Some(deg) if deg >= 2 => deg,
        _ => return false,
    };
    if deg <= 2 {
        return false;
    }
    if exponent.denom() == &BigInt::from(2) && deg > 2 {
        let has_odd_poly = factors.iter().any(|f| {
            if f == factor {
                return false;
            }
            polynomial_degree(f, var).map_or(false, |d| d % 2 == 1)
        });
        return !has_odd_poly;
    }
    false
}

fn is_radical_pow(factor: &Expr) -> bool {
    let Expr::Pow(_, exp) = factor else {
        return false;
    };
    match &**exp {
        Expr::Constant(k) => !k.is_integer(),
        Expr::Neg(inner) => matches!(&**inner, Expr::Constant(k) if !k.is_integer()),
        _ => false,
    }
}

fn detect_non_elementary_core(expr: &Expr, var: &str) -> Option<NonElementaryKind> {
    match expr {
        Expr::Exp(arg) => {
            if polynomial_degree_gt(arg, var, 1) {
                return Some(NonElementaryKind::ExpOfPolynomial);
            }
        }
        Expr::Pow(base, exp) => {
            if is_pow_self(base, exp, var) {
                return Some(NonElementaryKind::PowerSelf);
            }
        }
        Expr::Div(num, den) => {
            if let Some(kind) = trig_over_argument_kind(num, den, var) {
                return Some(kind);
            }
        }
        _ => {}
    }
    None
}

fn trig_over_argument_kind(num: &Expr, den: &Expr, var: &str) -> Option<NonElementaryKind> {
    let arg = match num {
        Expr::Sin(arg) | Expr::Cos(arg) | Expr::Tan(arg) => arg,
        _ => return None,
    };
    if constant_ratio(den, arg, var).is_none() {
        return None;
    }
    let degree = polynomial_degree(arg, var)?;
    if degree > 1 {
        Some(NonElementaryKind::TrigOverPolynomialArgument)
    } else if degree == 1 {
        Some(NonElementaryKind::TrigOverArgument)
    } else {
        None
    }
}

fn detect_power_self_log(factors: &[Expr], var: &str) -> Option<NonElementaryKind> {
    let mut saw_pow_self = false;
    let mut saw_log = false;

    for factor in factors {
        if is_pow_self_expr(factor, var) {
            saw_pow_self = true;
            continue;
        }
        if is_log_var(factor, var) {
            saw_log = true;
            continue;
        }
        if !is_constant_wrt(factor, var) {
            return None;
        }
    }

    if saw_pow_self && saw_log {
        Some(NonElementaryKind::PowerSelfLog)
    } else {
        None
    }
}

fn is_pow_self(base: &Expr, exp: &Expr, var: &str) -> bool {
    matches!(base, Expr::Variable(name) if name == var)
        && matches!(exp, Expr::Variable(name) if name == var)
}

fn is_pow_self_expr(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Pow(base, exp) => is_pow_self(base, exp, var),
        _ => false,
    }
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

fn polynomial_degree_gt(expr: &Expr, var: &str, threshold: usize) -> bool {
    matches!(polynomial_degree(expr, var), Some(deg) if deg > threshold)
}

fn is_half_integer_exp(exp: &Expr) -> bool {
    matches!(
        exp,
        Expr::Constant(k) if !k.is_integer() && k.denom() == &BigInt::from(2)
    )
}

fn polynomial_degree(expr: &Expr, var: &str) -> Option<usize> {
    let key = (expr.clone(), var.to_string());
    if let Some(cached) = POLY_CACHE.with(|c| c.borrow().get(&key).cloned()) {
        return cached;
    }
    let result = polynomial::degree(expr, var);
    POLY_CACHE.with(|c| {
        let mut map = c.borrow_mut();
        if map.len() > 2048 {
            map.clear();
        }
        map.insert(key, result);
    });
    result
}

pub(super) fn is_rational_like(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Div(num, den) => is_polynomial_cached(num, var) && is_polynomial_cached(den, var),
        _ => false,
    }
}

fn is_polynomial_cached(expr: &Expr, var: &str) -> bool {
    let key = (expr.clone(), var.to_string());
    if let Some(cached) = IS_POLY_CACHE.with(|c| c.borrow().get(&key).cloned()) {
        return cached;
    }
    let result = polynomial::is_polynomial(expr, var);
    IS_POLY_CACHE.with(|c| {
        let mut map = c.borrow_mut();
        if map.len() > 2048 {
            map.clear();
        }
        map.insert(key, result);
    });
    result
}
