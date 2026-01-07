use std::collections::{BTreeMap, HashSet};

use num_traits::One;

use crate::core::error::{CasError, Result};
use crate::core::expr::{Expr, Rational};
use crate::simplify::simplify_fully;

use super::derive::derive_expr_inner;
use super::poly::{
    expr_poly_derivative_t, expr_poly_is_one, expr_poly_is_zero, expr_poly_mod,
    expr_poly_mod_inverse, poly_from_coeff, poly_to_expr, simplify_poly_coeffs,
};
use super::tower::Tower;
use super::ExprPoly;

pub(super) fn algebraic_minimal_poly(base_symbol: &Expr, degree: usize) -> ExprPoly {
    let mut coeffs = BTreeMap::new();
    coeffs.insert(degree, Expr::Constant(Rational::one()));
    coeffs.insert(0, simplify_fully(Expr::Neg(base_symbol.clone().boxed())));
    simplify_poly_coeffs(ExprPoly { coeffs })
}

pub(super) fn algebraic_derivative(
    minimal: &ExprPoly,
    tower: &Tower,
    symbol: &str,
    symbols: &HashSet<String>,
) -> Result<Expr> {
    let m_t = expr_poly_derivative_t(minimal);
    if expr_poly_is_zero(&m_t) {
        return Err(CasError::Unsupported(
            "algebraic minimal polynomial derivative is zero".to_string(),
        ));
    }
    let m_x = algebraic_coeff_derivative(minimal, tower, symbols)?;
    let inv_m_t = expr_poly_mod_inverse(&m_t, minimal).ok_or_else(|| {
        CasError::Unsupported("algebraic minimal polynomial not squarefree".to_string())
    })?;
    let deriv_poly = expr_poly_mod(
        &simplify_poly_coeffs(m_x * inv_m_t.scale(&Expr::Constant(-Rational::one()))),
        minimal,
    );
    Ok(poly_to_expr(&deriv_poly, symbol))
}

fn algebraic_coeff_derivative(
    poly: &ExprPoly,
    tower: &Tower,
    symbols: &HashSet<String>,
) -> Result<ExprPoly> {
    let mut result = ExprPoly::zero();
    for (exp, coeff) in poly.coeff_entries() {
        let coeff_deriv = derive_expr_inner(&coeff, tower, symbols)?;
        if !coeff_deriv.is_zero() {
            result = result + poly_from_coeff(exp, coeff_deriv);
        }
    }
    Ok(simplify_poly_coeffs(result))
}

pub(super) fn reduce_algebraic_rational(
    numer: &ExprPoly,
    denom: &ExprPoly,
    minimal: &ExprPoly,
) -> Result<(ExprPoly, ExprPoly)> {
    let numer = simplify_poly_coeffs(numer.clone());
    let denom = simplify_poly_coeffs(denom.clone());
    let numer_mod = expr_poly_mod(&numer, minimal);
    let denom_mod = expr_poly_mod(&denom, minimal);
    if expr_poly_is_zero(&denom_mod) {
        return Err(CasError::Unsupported("division by zero".to_string()));
    }
    if expr_poly_is_one(&denom_mod) {
        return Ok((numer_mod, ExprPoly::one()));
    }
    let inv = expr_poly_mod_inverse(&denom_mod, minimal)
        .ok_or_else(|| CasError::Unsupported("non-invertible denominator".to_string()))?;
    let reduced = expr_poly_mod(&simplify_poly_coeffs(numer_mod * inv), minimal);
    Ok((reduced, ExprPoly::one()))
}
