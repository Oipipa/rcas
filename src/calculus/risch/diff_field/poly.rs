use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::One;

use crate::core::error::{CasError, Result};
use crate::core::expr::{Expr, Rational, one, zero};
use crate::simplify::simplify_fully;

use super::utils::{
    abs_i64_to_usize, expr_contains_var, expr_is_negative_one, extract_integer,
};
use super::ExprPoly;

pub(super) fn expr_to_rational_polys(expr: &Expr, var: &str) -> Result<(ExprPoly, ExprPoly)> {
    if !expr_contains_var(expr, var) {
        return Ok((ExprPoly::from_constant(expr.clone()), ExprPoly::one()));
    }
    match expr {
        Expr::Variable(name) if name == var => {
            let mut coeffs = BTreeMap::new();
            coeffs.insert(1, one());
            Ok((ExprPoly { coeffs }, ExprPoly::one()))
        }
        Expr::Constant(_) => Ok((ExprPoly::from_constant(expr.clone()), ExprPoly::one())),
        Expr::Add(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            let numer = an * bd.clone() + bn * ad.clone();
            let denom = ad * bd;
            Ok((numer, denom))
        }
        Expr::Sub(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            let numer = an * bd.clone() - bn * ad.clone();
            let denom = ad * bd;
            Ok((numer, denom))
        }
        Expr::Mul(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            Ok((an * bn, ad * bd))
        }
        Expr::Div(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            Ok((an * bd, ad * bn))
        }
        Expr::Neg(inner) => {
            let (n, d) = expr_to_rational_polys(inner, var)?;
            Ok((-n, d))
        }
        Expr::Pow(base, exp) => {
            let power = extract_integer(exp).ok_or_else(|| {
                CasError::Unsupported("non-integer exponent in rational expression".to_string())
            })?;
            let (bn, bd) = expr_to_rational_polys(base, var)?;
            if power == 0 {
                return Ok((ExprPoly::one(), ExprPoly::one()));
            }
            let abs_power = abs_i64_to_usize(power)?;
            let mut numer = bn.pow(abs_power);
            let mut denom = bd.pow(abs_power);
            if power < 0 {
                std::mem::swap(&mut numer, &mut denom);
            }
            Ok((numer, denom))
        }
        _ => Err(CasError::Unsupported(
            "non-rational expression in conversion".to_string(),
        )),
    }
}

pub(super) fn simplify_poly_coeffs(poly: ExprPoly) -> ExprPoly {
    let mut coeffs = BTreeMap::new();
    for (exp, coeff) in poly.coeff_entries() {
        let simplified = simplify_fully(coeff);
        if !simplified.is_zero() {
            coeffs.insert(exp, simplified);
        }
    }
    ExprPoly { coeffs }
}

pub(super) fn poly_from_power(exp: usize) -> ExprPoly {
    let mut coeffs = BTreeMap::new();
    coeffs.insert(exp, one());
    ExprPoly { coeffs }
}

pub(super) fn poly_from_coeff(exp: usize, coeff: Expr) -> ExprPoly {
    if coeff.is_zero() {
        return ExprPoly::zero();
    }
    let mut coeffs = BTreeMap::new();
    coeffs.insert(exp, coeff);
    ExprPoly { coeffs }
}

pub(super) fn poly_to_expr(poly: &ExprPoly, var: &str) -> Expr {
    if poly.is_zero() {
        return zero();
    }
    let mut terms = Vec::new();
    for (exp, coeff) in poly.coeff_entries() {
        let term = if exp == 0 {
            coeff
        } else {
            let pow = if exp == 1 {
                Expr::Variable(var.to_string())
            } else {
                Expr::Pow(
                    Expr::Variable(var.to_string()).boxed(),
                    Expr::Constant(Rational::from_integer(BigInt::from(exp as i64))).boxed(),
                )
            };
            if coeff.is_one() {
                pow
            } else if expr_is_negative_one(&coeff) {
                Expr::Neg(pow.boxed())
            } else {
                Expr::Mul(coeff.boxed(), pow.boxed())
            }
        };
        terms.push(term);
    }
    terms.sort();
    terms
        .into_iter()
        .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
        .unwrap_or_else(zero)
}

pub(super) fn expr_poly_is_zero(poly: &ExprPoly) -> bool {
    simplify_poly_coeffs(poly.clone()).is_zero()
}

pub(super) fn expr_poly_is_one(poly: &ExprPoly) -> bool {
    let simplified = simplify_poly_coeffs(poly.clone());
    simplified.degree() == Some(0) && simplify_fully(simplified.coeff(0)).is_one()
}

fn expr_poly_div_rem(dividend: &ExprPoly, divisor: &ExprPoly) -> Option<(ExprPoly, ExprPoly)> {
    if expr_poly_is_zero(divisor) {
        return None;
    }
    let mut remainder = simplify_poly_coeffs(dividend.clone());
    let mut quotient = ExprPoly::zero();
    let divisor_degree = divisor.degree()?;
    let divisor_lc = simplify_fully(divisor.leading_coeff());
    if divisor_lc.is_zero() {
        return None;
    }
    if divisor_degree == 0 {
        let scale = Expr::Div(
            Expr::Constant(Rational::one()).boxed(),
            divisor_lc.boxed(),
        );
        let scaled = simplify_poly_coeffs(dividend.scale(&scale));
        return Some((scaled, ExprPoly::zero()));
    }

    while let Some(r_deg) = remainder.degree() {
        if r_deg < divisor_degree {
            break;
        }
        let power = r_deg - divisor_degree;
        let coeff = simplify_fully(Expr::Div(
            remainder.leading_coeff().boxed(),
            divisor_lc.clone().boxed(),
        ));
        let term = poly_from_coeff(power, coeff);
        quotient = simplify_poly_coeffs(quotient + term.clone());
        remainder = simplify_poly_coeffs(remainder - term * divisor.clone());
    }

    Some((simplify_poly_coeffs(quotient), simplify_poly_coeffs(remainder)))
}

pub(super) fn expr_poly_mod(poly: &ExprPoly, modulus: &ExprPoly) -> ExprPoly {
    if expr_poly_is_zero(modulus) {
        return poly.clone();
    }
    let (_, remainder) = expr_poly_div_rem(poly, modulus).unwrap_or((ExprPoly::zero(), poly.clone()));
    remainder
}

fn expr_poly_extended_gcd(
    a: &ExprPoly,
    b: &ExprPoly,
) -> Option<(ExprPoly, ExprPoly, ExprPoly)> {
    let mut r0 = a.clone();
    let mut r1 = b.clone();
    let mut s0 = ExprPoly::one();
    let mut s1 = ExprPoly::zero();
    let mut t0 = ExprPoly::zero();
    let mut t1 = ExprPoly::one();

    while !expr_poly_is_zero(&r1) {
        let (q, r) = expr_poly_div_rem(&r0, &r1)?;
        r0 = r1;
        r1 = r;
        let s2 = simplify_poly_coeffs(s0.clone() - q.clone() * s1.clone());
        let t2 = simplify_poly_coeffs(t0.clone() - q * t1.clone());
        s0 = s1;
        s1 = s2;
        t0 = t1;
        t1 = t2;
    }

    if expr_poly_is_zero(&r0) {
        return None;
    }
    let lc = simplify_fully(r0.leading_coeff());
    if lc.is_zero() {
        return None;
    }
    let scale = Expr::Div(Expr::Constant(Rational::one()).boxed(), lc.boxed());
    Some((
        simplify_poly_coeffs(r0.scale(&scale)),
        simplify_poly_coeffs(s0.scale(&scale)),
        simplify_poly_coeffs(t0.scale(&scale)),
    ))
}

pub(super) fn expr_poly_mod_inverse(value: &ExprPoly, modulus: &ExprPoly) -> Option<ExprPoly> {
    if expr_poly_is_zero(modulus) {
        return None;
    }
    let (gcd, _s, t) = expr_poly_extended_gcd(modulus, value)?;
    if expr_poly_is_one(&gcd) {
        return Some(expr_poly_mod(&t, modulus));
    }
    if gcd.degree() == Some(0) {
        let coeff = simplify_fully(gcd.coeff(0));
        if coeff.is_zero() {
            return None;
        }
        let scale = Expr::Div(Expr::Constant(Rational::one()).boxed(), coeff.boxed());
        return Some(expr_poly_mod(&simplify_poly_coeffs(t.scale(&scale)), modulus));
    }
    None
}

pub(super) fn expr_poly_derivative_t(poly: &ExprPoly) -> ExprPoly {
    let mut coeffs = BTreeMap::new();
    for (exp, coeff) in poly.coeff_entries() {
        if exp == 0 {
            continue;
        }
        let factor = Rational::from_integer(BigInt::from(exp as i64));
        let scaled = simplify_fully(Expr::Mul(
            coeff.boxed(),
            Expr::Constant(factor).boxed(),
        ));
        if !scaled.is_zero() {
            coeffs.insert(exp - 1, scaled);
        }
    }
    ExprPoly { coeffs }
}
