use std::collections::HashSet;

use num_traits::{One, ToPrimitive};

use crate::calculus::risch::expr_utils::expr_any;
use crate::core::error::{CasError, Result};
use crate::core::expr::{Expr, Rational};

pub(super) fn expr_contains_var(expr: &Expr, var: &str) -> bool {
    expr_any(expr, &mut |node| matches!(node, Expr::Variable(name) if name == var))
}

pub(super) fn expr_depends_on(expr: &Expr, base_var: &str, symbols: &HashSet<String>) -> bool {
    expr_any(expr, &mut |node| {
        matches!(node, Expr::Variable(name) if name == base_var || symbols.contains(name))
    })
}

pub(super) fn expr_in_field(expr: &Expr, base_var: &str, symbols: &HashSet<String>) -> bool {
    if !expr_depends_on(expr, base_var, symbols) {
        return true;
    }
    match expr {
        Expr::Variable(_) => true,
        Expr::Constant(_) => true,
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b) => expr_in_field(a, base_var, symbols) && expr_in_field(b, base_var, symbols),
        Expr::Neg(inner) => expr_in_field(inner, base_var, symbols),
        Expr::Pow(base, exp) => extract_integer(exp).is_some() && expr_in_field(base, base_var, symbols),
        _ => false,
    }
}

pub(super) fn extract_integer(exp: &Expr) -> Option<i64> {
    match exp {
        Expr::Constant(c) if c.is_integer() => c.to_integer().to_i64(),
        Expr::Neg(inner) => extract_integer(inner).map(|value| -value),
        _ => None,
    }
}

pub(super) fn abs_i64_to_usize(value: i64) -> Result<usize> {
    value
        .checked_abs()
        .and_then(|abs| usize::try_from(abs).ok())
        .ok_or_else(|| CasError::Unsupported("exponent overflow".to_string()))
}

pub(super) fn expr_is_negative_one(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(c) if *c == -Rational::one())
}

pub(super) fn extract_rational_exp(expr: &Expr) -> Option<Rational> {
    match expr {
        Expr::Constant(c) => Some(c.clone()),
        Expr::Neg(inner) => extract_rational_exp(inner).map(|c| -c),
        _ => None,
    }
}
