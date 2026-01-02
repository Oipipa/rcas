//! String-based UI helpers for quick usage and rendering.

mod integration;
mod pretty;
mod solve;

use crate::calculus::{differentiate as differentiate_expr, integrate as integrate_expr};
use crate::core::error::{CasError, Result};
use crate::core::expr::Expr;
use crate::core::parser::parse_expr;
use crate::simplify::{normalize as normalize_expr, simplify_fully};
use crate::solver::{solve_system as solve_system_expr, SolveResult};

pub use integration::integration_summary;
pub use pretty::pretty;
pub use solve::solve_summary;

pub fn parse(input: &str) -> Result<Expr> {
    parse_expr(input)
}

pub fn differentiate(input: &str, var: &str) -> Result<Expr> {
    let expr = parse_expr(input)?;
    Ok(simplify_fully(differentiate_expr(var, &expr)))
}

pub fn diff(input: &str, var: &str) -> Result<String> {
    Ok(pretty(&differentiate(input, var)?))
}

pub fn integrate(input: &str, var: &str) -> Result<crate::calculus::integrate::IntegrationResult> {
    let expr = parse_expr(input)?;
    Ok(integrate_expr(var, &expr))
}

pub fn inte(input: &str, var: &str) -> Result<String> {
    let result = integrate(input, var)?;
    Ok(integration_summary(&result))
}

pub fn simplify(input: &str) -> Result<Expr> {
    let expr = parse_expr(input)?;
    Ok(simplify_fully(expr))
}

pub fn simp(input: &str) -> Result<String> {
    Ok(pretty(&simplify(input)?))
}

pub fn normalize(input: &str) -> Result<Expr> {
    let expr = parse_expr(input)?;
    Ok(normalize_expr(expr))
}

pub fn norm(input: &str) -> Result<String> {
    Ok(pretty(&normalize(input)?))
}

pub fn solve_system(vars: &[&str], equations: &[(&str, &str)]) -> Result<SolveResult> {
    let parsed: Vec<(Expr, Expr)> = equations
        .iter()
        .map(|(lhs, rhs)| Ok((parse_expr(lhs)?, parse_expr(rhs)?)))
        .collect::<Result<Vec<_>>>()?;

    Ok(solve_system_expr(vars.iter().copied().collect(), parsed))
}

pub fn solve(vars: &[&str], equations: &[(&str, &str)]) -> Result<Vec<String>> {
    let result = solve_system(vars, equations)?;
    Ok(solve_summary(&result))
}

pub fn solve_system_eqs(vars: &[&str], equations: &[&str]) -> Result<SolveResult> {
    let parsed: Vec<(Expr, Expr)> = equations
        .iter()
        .map(|eq| parse_equation(eq))
        .collect::<Result<Vec<_>>>()?;

    Ok(solve_system_expr(vars.iter().copied().collect(), parsed))
}

pub fn solve_eqs(vars: &[&str], equations: &[&str]) -> Result<Vec<String>> {
    let result = solve_system_eqs(vars, equations)?;
    Ok(solve_summary(&result))
}

fn parse_equation(input: &str) -> Result<(Expr, Expr)> {
    let (lhs, rhs) = input.split_once('=').ok_or_else(|| {
        CasError::Parse("equation must contain '='".to_string())
    })?;
    Ok((parse_expr(lhs.trim())?, parse_expr(rhs.trim())?))
}
