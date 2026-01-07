use std::collections::HashSet;

use num_traits::{One, ToPrimitive};

use crate::core::error::{CasError, Result};
use crate::core::expr::{Expr, Rational};

pub(super) fn expr_contains_var(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Variable(name) => name == var,
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => expr_contains_var(a, var) || expr_contains_var(b, var),
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
        | Expr::Abs(inner)
        | Expr::Exp(inner)
        | Expr::Log(inner) => expr_contains_var(inner, var),
        Expr::Constant(_) => false,
    }
}

pub(super) fn expr_depends_on(expr: &Expr, base_var: &str, symbols: &HashSet<String>) -> bool {
    match expr {
        Expr::Variable(name) => name == base_var || symbols.contains(name),
        Expr::Constant(_) => false,
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => expr_depends_on(a, base_var, symbols) || expr_depends_on(b, base_var, symbols),
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
        | Expr::Abs(inner)
        | Expr::Exp(inner)
        | Expr::Log(inner) => expr_depends_on(inner, base_var, symbols),
    }
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
