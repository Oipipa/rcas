use std::collections::BTreeSet;

use num_traits::{One, Zero};

use crate::core::expr::{Expr, Rational};
use crate::core::factor::Poly;
use crate::core::polynomial::Polynomial;
use crate::simplify::{simplify, simplify_fully};

use super::polynomial;

type ExprPoly = Polynomial<Expr>;

pub(crate) fn constant_ratio(expr: &Expr, target: &Expr, var: &str) -> Option<Expr> {
    let expr_norm = simplify_fully(expr.clone());
    let target_norm = simplify_fully(target.clone());

    if expr_norm == target_norm {
        return Some(Expr::Constant(Rational::one()));
    }

    if let Expr::Mul(a, b) = &expr_norm {
        match (&**a, &**b) {
            (Expr::Constant(c), other) if other == &target_norm => {
                return Some(Expr::Constant(c.clone()))
            }
            (other, Expr::Constant(c)) if other == &target_norm => {
                return Some(Expr::Constant(c.clone()))
            }
            (other, expr_const) if other == &target_norm && is_constant_wrt(expr_const, var) => {
                return Some(expr_const.clone());
            }
            (expr_const, other) if other == &target_norm && is_constant_wrt(expr_const, var) => {
                return Some(expr_const.clone());
            }
            _ => {}
        }
    }
    if let Some(ratio) = rational_constant_ratio(&expr_norm, &target_norm, var) {
        return Some(ratio);
    }
    if let Some(ratio) = algebraic_constant_ratio(&expr_norm, &target_norm, var) {
        return Some(ratio);
    }
    let quotient = simplify_fully(Expr::Div(
        expr_norm.clone().boxed(),
        target_norm.clone().boxed(),
    ));
    if is_constant_wrt(&quotient, var) {
        return Some(quotient);
    }
    let (expr_const, mut expr_factors) = split_constant_factors(&expr_norm, var);
    let (target_const, mut target_factors) = split_constant_factors(&target_norm, var);
    expr_factors.sort();
    target_factors.sort();
    if expr_factors == target_factors {
        return Some(simplify(Expr::Div(
            expr_const.boxed(),
            target_const.boxed(),
        )));
    }
    None
}

fn rational_constant_ratio(expr: &Expr, target: &Expr, var: &str) -> Option<Expr> {
    let (expr_num, expr_den) = as_rational_polys(expr, var)?;
    let (target_num, target_den) = as_rational_polys(target, var)?;

    if target_num.is_zero() {
        return None;
    }

    let numerator = expr_num * target_den;
    let denominator = expr_den * target_num;
    if denominator.is_zero() {
        return None;
    }

    if numerator.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let numerator_deg = numerator.degree()?;
    let denominator_deg = denominator.degree()?;
    if numerator_deg != denominator_deg {
        return None;
    }

    let scale = numerator.leading_coeff() / denominator.leading_coeff();
    if numerator == denominator.scale(&scale) {
        Some(Expr::Constant(scale))
    } else {
        None
    }
}

fn algebraic_constant_ratio(expr: &Expr, target: &Expr, var: &str) -> Option<Expr> {
    let (expr_num, expr_den) = as_rational_expr_polys(expr, var)?;
    let (target_num, target_den) = as_rational_expr_polys(target, var)?;

    if poly_expr_is_zero(&target_num) {
        return None;
    }

    let numerator = expr_num * target_den;
    let denominator = expr_den * target_num;
    if poly_expr_is_zero(&denominator) {
        return None;
    }

    if poly_expr_is_zero(&numerator) {
        return Some(Expr::Constant(Rational::zero()));
    }

    let numerator_deg = poly_expr_degree(&numerator)?;
    let denominator_deg = poly_expr_degree(&denominator)?;
    if numerator_deg != denominator_deg {
        return None;
    }

    let numerator_lc = poly_expr_leading_coeff(&numerator)?;
    let denominator_lc = poly_expr_leading_coeff(&denominator)?;
    let ratio = simplify_fully(Expr::Div(numerator_lc.boxed(), denominator_lc.boxed()));
    if !is_constant_wrt(&ratio, var) {
        return None;
    }

    let scaled = denominator.scale(&ratio);
    if poly_expr_eq(&numerator, &scaled) {
        Some(ratio)
    } else {
        None
    }
}

fn as_rational_polys(expr: &Expr, var: &str) -> Option<(Poly, Poly)> {
    let (num_expr, den_expr) = as_rational_expr(expr);
    let num_poly = Poly::from_expr(&num_expr, var)?;
    let den_poly = Poly::from_expr(&den_expr, var)?;
    if den_poly.is_zero() {
        return None;
    }
    Some((num_poly, den_poly))
}

pub(super) fn as_rational_expr(expr: &Expr) -> (Expr, Expr) {
    let (const_factor, factors) = flatten_product(expr);
    if const_factor.is_zero() {
        return (
            Expr::Constant(Rational::zero()),
            Expr::Constant(Rational::one()),
        );
    }

    let (num_factors, den_factors) = split_negative_powers(factors);

    let numerator = rebuild_product(const_factor, num_factors);
    let denominator = if den_factors.is_empty() {
        Expr::Constant(Rational::one())
    } else {
        rebuild_product(Rational::one(), den_factors)
    };

    (numerator, denominator)
}

fn split_negative_powers<I>(factors: I) -> (Vec<Expr>, Vec<Expr>)
where
    I: IntoIterator<Item = Expr>,
{
    let mut num_factors = Vec::new();
    let mut den_factors = Vec::new();

    for factor in factors {
        match factor {
            Expr::Pow(base, exp) => match &*exp {
                Expr::Constant(k) if k < &Rational::zero() => {
                    den_factors.push(Expr::Pow(
                        base.clone().boxed(),
                        Expr::Constant(-k.clone()).boxed(),
                    ));
                }
                Expr::Neg(inner) if matches!(**inner, Expr::Constant(_)) => {
                    if let Expr::Constant(k) = &**inner {
                        den_factors.push(Expr::Pow(
                            base.clone().boxed(),
                            Expr::Constant(k.clone()).boxed(),
                        ));
                    } else {
                        num_factors.push(Expr::Pow(base.clone(), exp.clone()));
                    }
                }
                _ => num_factors.push(Expr::Pow(base.clone(), exp.clone())),
            },
            other => num_factors.push(other),
        }
    }

    (num_factors, den_factors)
}

pub(crate) fn log_abs(expr: Expr) -> Expr {
    Expr::Log(Expr::Abs(expr.boxed()).boxed())
}

pub(crate) fn flatten_product(expr: &Expr) -> (Rational, Vec<Expr>) {
    match expr {
        Expr::Constant(c) => (c.clone(), Vec::new()),
        Expr::Neg(inner) => {
            let (c, factors) = flatten_product(inner);
            (-c, factors)
        }
        Expr::Mul(a, b) => {
            let (ca, mut fa) = flatten_product(a);
            let (cb, mut fb) = flatten_product(b);
            fa.append(&mut fb);
            (ca * cb, fa)
        }
        Expr::Div(a, b) => {
            let (ca, mut fa) = flatten_product(a);
            let (cb, fb) = flatten_product(b);
            for factor in fb {
                if let Expr::Pow(base, exp) = &factor
                    && let Expr::Constant(k) = &**exp
                {
                    fa.push(Expr::Pow(
                        base.clone(),
                        Expr::Constant(-k.clone()).boxed(),
                    ));
                    continue;
                }
                fa.push(Expr::Pow(
                    factor.boxed(),
                    Expr::Constant(-Rational::one()).boxed(),
                ));
            }
            (ca / cb, fa)
        }
        other => (Rational::one(), vec![other.clone()]),
    }
}

fn as_rational_expr_polys(expr: &Expr, var: &str) -> Option<(ExprPoly, ExprPoly)> {
    let (num_expr, den_expr) = as_rational_expr(expr);
    let num_poly = ExprPoly::from_expr(&num_expr, var)?;
    let den_poly = ExprPoly::from_expr(&den_expr, var)?;
    if poly_expr_is_zero(&den_poly) {
        return None;
    }
    Some((num_poly, den_poly))
}

fn poly_expr_degree(poly: &ExprPoly) -> Option<usize> {
    let mut degree = None;
    for (exp, coeff) in poly.coeff_entries() {
        if !is_zero_expr(&coeff) {
            degree = Some(exp);
        }
    }
    degree
}

fn poly_expr_leading_coeff(poly: &ExprPoly) -> Option<Expr> {
    let degree = poly_expr_degree(poly)?;
    Some(poly.coeff(degree))
}

fn poly_expr_is_zero(poly: &ExprPoly) -> bool {
    poly_expr_degree(poly).is_none()
}

fn poly_expr_eq(lhs: &ExprPoly, rhs: &ExprPoly) -> bool {
    let mut exps = BTreeSet::new();
    for (exp, _) in lhs.coeff_entries() {
        exps.insert(exp);
    }
    for (exp, _) in rhs.coeff_entries() {
        exps.insert(exp);
    }
    if exps.is_empty() {
        return true;
    }
    for exp in exps {
        let lhs_coeff = lhs.coeff(exp);
        let rhs_coeff = rhs.coeff(exp);
        let diff = Expr::Sub(lhs_coeff.boxed(), rhs_coeff.boxed());
        if !is_zero_expr(&diff) {
            return false;
        }
    }
    true
}

pub(crate) fn rebuild_product(constant: Rational, mut factors: Vec<Expr>) -> Expr {
    if constant.is_zero() {
        return Expr::Constant(Rational::zero());
    }
    let mut terms: Vec<Expr> = Vec::new();
    if !constant.is_one() {
        terms.push(Expr::Constant(constant));
    }
    terms.append(&mut factors);

    if terms.is_empty() {
        return Expr::Constant(Rational::one());
    }
    terms
        .into_iter()
        .reduce(|a, b| Expr::Mul(a.boxed(), b.boxed()))
        .unwrap()
}

pub(crate) fn split_constant_factors(expr: &Expr, var: &str) -> (Expr, Vec<Expr>) {
    let (const_factor, factors) = flatten_product(expr);
    let mut const_factors = Vec::new();
    let mut var_factors = Vec::new();
    for factor in factors {
        if is_constant_wrt(&factor, var) {
            const_factors.push(factor);
        } else {
            var_factors.push(factor);
        }
    }
    (rebuild_product(const_factor, const_factors), var_factors)
}

pub(super) fn combine_algebraic_factors(factors: Vec<Expr>, var: &str) -> Vec<Expr> {
    let mut algebraic = Vec::new();
    let mut others = Vec::new();
    for factor in factors {
        if polynomial::is_polynomial(&factor, var) {
            algebraic.push(factor);
        } else {
            others.push(factor);
        }
    }
    if algebraic.is_empty() {
        return others;
    }
    if algebraic.len() == 1 {
        others.push(algebraic.pop().unwrap());
        return others;
    }
    let combined = algebraic
        .into_iter()
        .reduce(|a, b| Expr::Mul(a.boxed(), b.boxed()))
        .unwrap();
    others.push(simplify(combined));
    others
}

pub(crate) fn apply_constant_factor(const_factor: Expr, expr: Expr) -> Expr {
    if is_one_expr(&const_factor) {
        expr
    } else {
        simplify(Expr::Mul(const_factor.boxed(), expr.boxed()))
    }
}

pub(crate) fn scale_by_coeff(expr: Expr, coeff: Expr) -> Expr {
    if is_one_expr(&coeff) {
        expr
    } else {
        simplify(Expr::Mul(expr.boxed(), invert_coeff(coeff).boxed()))
    }
}

fn invert_coeff(expr: Expr) -> Expr {
    match expr {
        Expr::Constant(c) => Expr::Constant(Rational::one() / c),
        Expr::Neg(inner) => Expr::Neg(invert_coeff(*inner).boxed()),
        Expr::Div(num, den) => Expr::Div(den, num),
        Expr::Pow(base, exp) => match &*exp {
            Expr::Constant(k) => Expr::Pow(base, Expr::Constant(-k.clone()).boxed()),
            _ => Expr::Div(
                Expr::Constant(Rational::one()).boxed(),
                Expr::Pow(base, exp).boxed(),
            ),
        },
        other => Expr::Div(Expr::Constant(Rational::one()).boxed(), other.boxed()),
    }
}

pub(super) fn is_zero_expr(expr: &Expr) -> bool {
    matches!(simplify_fully(expr.clone()), Expr::Constant(c) if c.is_zero())
}

pub(super) fn is_one_expr(expr: &Expr) -> bool {
    matches!(simplify_fully(expr.clone()), Expr::Constant(c) if c.is_one())
}

pub(super) fn combine_var_powers(
    constant: Rational,
    factors: Vec<Expr>,
    var: &str,
) -> (Rational, Vec<Expr>) {
    let mut exponent = Rational::zero();
    let mut others = Vec::new();

    for factor in factors {
        match factor {
            Expr::Variable(name) if name == var => exponent += Rational::one(),
            Expr::Pow(base, exp) => match (&*base, &*exp) {
                (Expr::Variable(name), Expr::Constant(k)) if name == var => {
                    exponent += k.clone();
                }
                (Expr::Variable(name), Expr::Neg(inner)) if name == var => {
                    if let Expr::Constant(k) = &**inner {
                        exponent -= k.clone();
                    } else {
                        others.push(Expr::Pow(base.clone(), exp.clone()));
                    }
                }
                _ => others.push(Expr::Pow(base.clone(), exp.clone())),
            },
            other => others.push(other),
        }
    }

    if !exponent.is_zero() {
        if exponent == Rational::one() {
            others.push(Expr::Variable(var.to_string()));
        } else {
            others.push(Expr::Pow(
                Expr::Variable(var.to_string()).boxed(),
                Expr::Constant(exponent).boxed(),
            ));
        }
    }

    (constant, others)
}

fn multiply_and_normalize(base: &Expr, term: &Expr, var: &str) -> Expr {
    let (c_base, mut f_base) = flatten_product(base);
    let (c_term, mut f_term) = flatten_product(term);
    f_base.append(&mut f_term);
    let (combined_const, combined_factors) = combine_var_powers(c_base * c_term, f_base, var);
    let rebuilt = rebuild_product(combined_const, combined_factors.clone());
    let simplified = simplify_fully(rebuilt.clone());
    if expr_size(&simplified) <= expr_size(&rebuilt) {
        simplified
    } else {
        rebuilt
    }
}

pub(super) fn distribute_product_with_addition(
    constant: Rational,
    factors: Vec<Expr>,
    var: &str,
) -> Option<Expr> {
    let add_index = factors
        .iter()
        .position(|f| matches!(f, Expr::Add(_, _) | Expr::Sub(_, _)))?;
    let additive = factors[add_index].clone();
    let remaining: Vec<Expr> = factors
        .into_iter()
        .enumerate()
        .filter_map(|(i, f)| if i == add_index { None } else { Some(f) })
        .collect();
    let (rest_const, rest_factors) = combine_var_powers(constant, remaining, var);
    let rest_product = rebuild_product(rest_const, rest_factors);

    match additive {
        Expr::Add(a, b) => Some(Expr::Add(
            multiply_and_normalize(&rest_product, &a, var).boxed(),
            multiply_and_normalize(&rest_product, &b, var).boxed(),
        )),
        Expr::Sub(a, b) => Some(Expr::Sub(
            multiply_and_normalize(&rest_product, &a, var).boxed(),
            multiply_and_normalize(&rest_product, &b, var).boxed(),
        )),
        _ => None,
    }
}

pub(crate) fn to_rational_candidate(constant: Rational, factors: &[Expr]) -> Option<Expr> {
    let (num_factors, den_factors) = split_negative_powers(factors.iter().cloned());

    if den_factors.is_empty() {
        return None;
    }

    let numerator = rebuild_product(constant, num_factors);
    let denominator = rebuild_product(Rational::one(), den_factors);
    Some(Expr::Div(numerator.boxed(), denominator.boxed()))
}

pub(super) fn expr_size(expr: &Expr) -> usize {
    1 + match expr {
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) | Expr::Pow(a, b) => {
            expr_size(a) + expr_size(b)
        }
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
        | Expr::Log(inner)
        | Expr::Abs(inner) => expr_size(inner),
        Expr::Variable(_) | Expr::Constant(_) => 0,
    }
}

pub(crate) fn contains_var(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Variable(v) => v == var,
        Expr::Add(a, b) | Expr::Sub(a, b) => contains_var(a, var) || contains_var(b, var),
        Expr::Mul(a, b) => {
            if is_zero_constant(a) || is_zero_constant(b) {
                false
            } else {
                contains_var(a, var) || contains_var(b, var)
            }
        }
        Expr::Div(a, b) => {
            if is_zero_constant(a) {
                false
            } else {
                contains_var(a, var) || contains_var(b, var)
            }
        }
        Expr::Pow(base, exp) => {
            if is_zero_constant(exp) {
                false
            } else {
                contains_var(base, var) || contains_var(exp, var)
            }
        }
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
        | Expr::Log(inner)
        | Expr::Abs(inner) => contains_var(inner, var),
        Expr::Constant(_) => false,
    }
}

pub(crate) fn fresh_var_name(expr: &Expr, var: &str, base: &str) -> String {
    if base != var && !contains_var(expr, base) {
        return base.to_string();
    }
    for idx in 1..64 {
        let candidate = format!("{base}{idx}");
        if candidate != var && !contains_var(expr, &candidate) {
            return candidate;
        }
    }
    format!("{base}_sub")
}

fn is_zero_constant(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(c) if c.is_zero())
}

pub(super) fn is_constant_wrt(expr: &Expr, var: &str) -> bool {
    if !contains_var(expr, var) {
        return true;
    }
    let simplified = simplify_fully(expr.clone());
    !contains_var(&simplified, var)
}
