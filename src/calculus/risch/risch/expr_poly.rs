use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};

use crate::calculus::integrate::contains_var;
use crate::core::expr::{Expr, Rational};
use crate::core::polynomial::Poly;
use crate::simplify::simplify_fully;

use super::ExprPoly;

pub(super) fn expr_poly_as_monomial(poly: &ExprPoly) -> Option<(usize, Expr)> {
    let simplified = simplify_expr_poly(poly.clone());
    let mut iter = simplified
        .coeff_entries()
        .filter(|(_, coeff)| !simplify_fully(coeff.clone()).is_zero());
    let (exp, coeff) = iter.next()?;
    if iter.next().is_some() {
        return None;
    }
    Some((exp, coeff))
}

pub(super) fn expr_poly_is_zero(poly: &ExprPoly) -> bool {
    simplify_expr_poly(poly.clone()).is_zero()
}

pub(super) fn expr_poly_is_one(poly: &ExprPoly) -> bool {
    let simplified = simplify_expr_poly(poly.clone());
    simplified.degree() == Some(0) && simplify_fully(simplified.coeff(0)).is_one()
}

pub(super) fn simplify_expr_poly(poly: ExprPoly) -> ExprPoly {
    let mut coeffs = BTreeMap::new();
    for (exp, coeff) in poly.coeff_entries() {
        let simplified = simplify_fully(coeff);
        if !simplified.is_zero() {
            coeffs.insert(exp, simplified);
        }
    }
    ExprPoly { coeffs }
}

pub(super) fn expr_poly_to_expr(poly: &ExprPoly, var: &str) -> Expr {
    if expr_poly_is_zero(poly) {
        return Expr::Constant(Rational::zero());
    }
    let mut terms = Vec::new();
    for (exp, coeff) in poly.coeff_entries() {
        let coeff = simplify_fully(coeff);
        if coeff.is_zero() {
            continue;
        }
        let term = if exp == 0 {
            coeff
        } else {
            let pow = if exp == 1 {
                Expr::Variable(var.to_string())
            } else {
                Expr::Pow(
                    Expr::Variable(var.to_string()).boxed(),
                    Expr::integer(exp as i64).boxed(),
                )
            };
            if coeff.is_one() {
                pow
            } else if is_negative_one_expr(&coeff) {
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
        .unwrap_or_else(|| Expr::Constant(Rational::zero()))
}

pub(super) fn expr_to_rational_polys(expr: &Expr, var: &str) -> Option<(ExprPoly, ExprPoly)> {
    if !contains_var(expr, var) {
        return Some((ExprPoly::from_constant(expr.clone()), ExprPoly::one()));
    }
    match expr {
        Expr::Variable(name) if name == var => {
            let mut coeffs = BTreeMap::new();
            coeffs.insert(1, Expr::Constant(Rational::one()));
            Some((ExprPoly { coeffs }, ExprPoly::one()))
        }
        Expr::Constant(_) => Some((ExprPoly::from_constant(expr.clone()), ExprPoly::one())),
        Expr::Add(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            let numer = an * bd.clone() + bn * ad.clone();
            let denom = ad * bd;
            Some((simplify_expr_poly(numer), simplify_expr_poly(denom)))
        }
        Expr::Sub(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            let numer = an * bd.clone() - bn * ad.clone();
            let denom = ad * bd;
            Some((simplify_expr_poly(numer), simplify_expr_poly(denom)))
        }
        Expr::Mul(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            Some((simplify_expr_poly(an * bn), simplify_expr_poly(ad * bd)))
        }
        Expr::Div(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            Some((simplify_expr_poly(an * bd), simplify_expr_poly(ad * bn)))
        }
        Expr::Neg(inner) => {
            let (n, d) = expr_to_rational_polys(inner, var)?;
            Some((simplify_expr_poly(-n), d))
        }
        Expr::Pow(base, exp) => {
            let power = extract_integer_expr(exp)?;
            if power == 0 {
                return Some((ExprPoly::one(), ExprPoly::one()));
            }
            let abs_power = abs_i64_to_usize(power)?;
            let (bn, bd) = expr_to_rational_polys(base, var)?;
            let mut numer = bn.pow(abs_power);
            let mut denom = bd.pow(abs_power);
            if power < 0 {
                std::mem::swap(&mut numer, &mut denom);
            }
            Some((simplify_expr_poly(numer), simplify_expr_poly(denom)))
        }
        _ => None,
    }
}

pub(super) fn expr_to_rational_polys_rational(expr: &Expr, var: &str) -> Option<(Poly, Poly)> {
    match expr {
        Expr::Variable(name) if name == var => {
            let mut coeffs = BTreeMap::new();
            coeffs.insert(1, Rational::one());
            Some((Poly { coeffs }, Poly::one()))
        }
        Expr::Constant(_) => Some((Poly::from_constant(expr_rational(expr)?), Poly::one())),
        Expr::Add(a, b) => {
            let (an, ad) = expr_to_rational_polys_rational(a, var)?;
            let (bn, bd) = expr_to_rational_polys_rational(b, var)?;
            Some((an * bd.clone() + bn * ad.clone(), ad * bd))
        }
        Expr::Sub(a, b) => {
            let (an, ad) = expr_to_rational_polys_rational(a, var)?;
            let (bn, bd) = expr_to_rational_polys_rational(b, var)?;
            Some((an * bd.clone() - bn * ad.clone(), ad * bd))
        }
        Expr::Mul(a, b) => {
            let (an, ad) = expr_to_rational_polys_rational(a, var)?;
            let (bn, bd) = expr_to_rational_polys_rational(b, var)?;
            Some((an * bn, ad * bd))
        }
        Expr::Div(a, b) => {
            let (an, ad) = expr_to_rational_polys_rational(a, var)?;
            let (bn, bd) = expr_to_rational_polys_rational(b, var)?;
            Some((an * bd, ad * bn))
        }
        Expr::Neg(inner) => {
            let (n, d) = expr_to_rational_polys_rational(inner, var)?;
            Some((-n, d))
        }
        Expr::Pow(base, exp) => {
            let power = extract_integer_expr(exp)?;
            if power == 0 {
                return Some((Poly::one(), Poly::one()));
            }
            let abs_power = abs_i64_to_usize(power)?;
            let (bn, bd) = expr_to_rational_polys_rational(base, var)?;
            let mut numer = bn.pow(abs_power);
            let mut denom = bd.pow(abs_power);
            if power < 0 {
                std::mem::swap(&mut numer, &mut denom);
            }
            Some((numer, denom))
        }
        _ => None,
    }
}

fn expr_rational(expr: &Expr) -> Option<Rational> {
    match expr {
        Expr::Constant(c) => Some(c.clone()),
        Expr::Neg(inner) => expr_rational(inner).map(|c| -c),
        _ => None,
    }
}

pub(super) fn expr_poly_div_rem(dividend: &ExprPoly, divisor: &ExprPoly) -> Option<(ExprPoly, ExprPoly)> {
    if expr_poly_is_zero(divisor) {
        return None;
    }
    let mut remainder = simplify_expr_poly(dividend.clone());
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
        let scaled = simplify_expr_poly(dividend.scale(&scale));
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
        let term = expr_poly_monomial(coeff, power);
        quotient = simplify_expr_poly(quotient + term.clone());
        remainder = simplify_expr_poly(remainder - term * divisor.clone());
    }

    Some((simplify_expr_poly(quotient), simplify_expr_poly(remainder)))
}

pub(super) fn expr_poly_div_exact(dividend: &ExprPoly, divisor: &ExprPoly) -> Option<ExprPoly> {
    let (q, r) = expr_poly_div_rem(dividend, divisor)?;
    if expr_poly_is_zero(&r) {
        Some(q)
    } else {
        None
    }
}

pub(super) fn expr_poly_gcd(a: &ExprPoly, b: &ExprPoly) -> Option<ExprPoly> {
    if expr_poly_is_zero(a) {
        return Some(expr_poly_monic(b));
    }
    if expr_poly_is_zero(b) {
        return Some(expr_poly_monic(a));
    }
    if a.degree().unwrap_or(0) == 0 || b.degree().unwrap_or(0) == 0 {
        return Some(ExprPoly::one());
    }
    let mut r0 = simplify_expr_poly(a.clone());
    let mut r1 = simplify_expr_poly(b.clone());
    while !expr_poly_is_zero(&r1) {
        let (_, r) = expr_poly_div_rem(&r0, &r1)?;
        r0 = r1;
        r1 = r;
    }
    Some(expr_poly_monic(&r0))
}

pub(super) fn expr_poly_monic(poly: &ExprPoly) -> ExprPoly {
    if expr_poly_is_zero(poly) {
        return poly.clone();
    }
    let lc = simplify_fully(poly.leading_coeff());
    if lc.is_zero() {
        return poly.clone();
    }
    let scale = Expr::Div(
        Expr::Constant(Rational::one()).boxed(),
        lc.boxed(),
    );
    simplify_expr_poly(poly.scale(&scale))
}

fn expr_poly_derivative_t(poly: &ExprPoly) -> ExprPoly {
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

fn expr_poly_squarefree_decomposition(poly: &ExprPoly) -> Option<Vec<(ExprPoly, usize)>> {
    if expr_poly_is_zero(poly) || poly.degree().unwrap_or(0) == 0 {
        return Some(Vec::new());
    }
    let mut result = Vec::new();
    let mut i = 1;
    let derivative = expr_poly_derivative_t(poly);
    let mut g = expr_poly_gcd(poly, &derivative)?;
    let mut y = expr_poly_div_exact(poly, &g)?;

    while !expr_poly_is_one(&y) {
        let z = expr_poly_gcd(&y, &g)?;
        let factor = expr_poly_div_exact(&y, &z)?;
        if !expr_poly_is_one(&factor) {
            result.push((factor, i));
        }
        y = z.clone();
        g = expr_poly_div_exact(&g, &z)?;
        i += 1;
    }

    if !expr_poly_is_one(&g) {
        let g_sqrt = expr_poly_squarefree_decomposition(&g)?;
        for (part, mult) in g_sqrt {
            result.push((part, mult + i - 1));
        }
    }

    Some(result)
}

pub(super) fn hermite_reduce_expr(
    remainder: &ExprPoly,
    denominator: &ExprPoly,
    t_symbol: &str,
) -> Option<(Vec<Expr>, Vec<(ExprPoly, ExprPoly)>)> {
    let parts = expr_poly_squarefree_decomposition(denominator)?;
    if parts.is_empty() {
        return Some((Vec::new(), Vec::new()));
    }

    let mut terms: Vec<Expr> = Vec::new();
    let mut reduced_terms: Vec<(ExprPoly, ExprPoly)> = Vec::new();

    for (squarefree, multiplicity) in parts {
        let denom_part = squarefree.pow(multiplicity);
        let other = expr_poly_div_exact(denominator, &denom_part)?;
        let inv_other = if expr_poly_is_one(&other) {
            ExprPoly::one()
        } else {
            expr_poly_mod_inverse(&other, &denom_part)?
        };
        let num_part = expr_poly_mod(&(remainder.clone() * inv_other), &denom_part);
        let (mut hermite_terms, reduced_num) =
            hermite_reduce_factor_expr(num_part, &squarefree, multiplicity, t_symbol)?;
        terms.append(&mut hermite_terms);
        if !expr_poly_is_zero(&reduced_num) {
            reduced_terms.push((reduced_num, squarefree));
        }
    }

    Some((terms, reduced_terms))
}

fn hermite_reduce_factor_expr(
    mut numerator: ExprPoly,
    squarefree: &ExprPoly,
    multiplicity: usize,
    t_symbol: &str,
) -> Option<(Vec<Expr>, ExprPoly)> {
    if multiplicity == 0 {
        return None;
    }
    if multiplicity == 1 {
        return Some((Vec::new(), numerator));
    }

    let derivative = expr_poly_derivative_t(squarefree);
    if expr_poly_is_zero(&derivative) {
        return None;
    }
    let inv_derivative = expr_poly_mod_inverse(&derivative, squarefree)?;
    let mut terms: Vec<Expr> = Vec::new();
    let mut power = multiplicity;

    while power > 1 {
        let k_minus_one = Rational::from_integer(BigInt::from((power - 1) as i64));
        let remainder = expr_poly_mod(&numerator, squarefree);
        let u = if expr_poly_is_zero(&remainder) {
            ExprPoly::zero()
        } else {
            let scaled = simplify_expr_poly(remainder * inv_derivative.clone());
            let scaled = simplify_expr_poly(scaled.scale(&Expr::Constant(
                Rational::one() / k_minus_one.clone(),
            )));
            let scaled = simplify_expr_poly(
                scaled.scale(&Expr::Constant(Rational::from_integer((-1).into()))),
            );
            expr_poly_mod(&scaled, squarefree)
        };

        if !expr_poly_is_zero(&u) {
            let term = expr_rational_power_term(&u, squarefree, power - 1, t_symbol);
            terms.push(simplify_fully(term));
            let u_prime = expr_poly_derivative_t(&u);
            let u_scaled = simplify_expr_poly(u.scale(&Expr::Constant(k_minus_one.clone())));
            let numerator_adjust =
                simplify_expr_poly(u_prime * squarefree.clone() - u_scaled * derivative.clone());
            let reduced = simplify_expr_poly(numerator - numerator_adjust);
            numerator = expr_poly_div_exact(&reduced, squarefree)?;
        } else {
            numerator = expr_poly_div_exact(&numerator, squarefree)?;
        }

        power -= 1;
    }

    Some((terms, numerator))
}

fn expr_rational_power_term(num: &ExprPoly, den: &ExprPoly, power: usize, var: &str) -> Expr {
    let numerator = expr_poly_to_expr(num, var);
    let exponent = Rational::from_integer(BigInt::from(-(power as i64)));
    let pow = Expr::Pow(
        expr_poly_to_expr(den, var).boxed(),
        Expr::Constant(exponent).boxed(),
    );
    Expr::Mul(numerator.boxed(), pow.boxed())
}

fn expr_poly_mod(poly: &ExprPoly, modulus: &ExprPoly) -> ExprPoly {
    if expr_poly_is_zero(modulus) {
        return poly.clone();
    }
    let (_, remainder) = expr_poly_div_rem(poly, modulus).unwrap_or((ExprPoly::zero(), poly.clone()));
    remainder
}

fn expr_poly_mod_inverse(value: &ExprPoly, modulus: &ExprPoly) -> Option<ExprPoly> {
    if expr_poly_is_zero(modulus) {
        return None;
    }
    let (gcd, _s, t) = expr_poly_extended_gcd(modulus, value)?;
    if !expr_poly_is_one(&gcd) {
        return None;
    }
    Some(expr_poly_mod(&t, modulus))
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
        let s2 = simplify_expr_poly(s0.clone() - q.clone() * s1.clone());
        let t2 = simplify_expr_poly(t0.clone() - q * t1.clone());
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
    let scale = Expr::Div(
        Expr::Constant(Rational::one()).boxed(),
        lc.boxed(),
    );
    Some((
        simplify_expr_poly(r0.scale(&scale)),
        simplify_expr_poly(s0.scale(&scale)),
        simplify_expr_poly(t0.scale(&scale)),
    ))
}

fn expr_poly_monomial(coeff: Expr, exp: usize) -> ExprPoly {
    if simplify_fully(coeff.clone()).is_zero() {
        return ExprPoly::zero();
    }
    let mut coeffs = BTreeMap::new();
    coeffs.insert(exp, coeff);
    ExprPoly { coeffs }
}

fn extract_integer_expr(exp: &Expr) -> Option<i64> {
    match exp {
        Expr::Constant(c) if c.is_integer() => c.to_integer().to_i64(),
        Expr::Neg(inner) => extract_integer_expr(inner).map(|value| -value),
        _ => None,
    }
}

fn abs_i64_to_usize(value: i64) -> Option<usize> {
    value
        .checked_abs()
        .and_then(|abs| usize::try_from(abs).ok())
}

fn is_negative_one_expr(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(c) if *c == -Rational::one())
}
