use std::collections::{BTreeMap, HashMap, HashSet};

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::calculus::integrate::{contains_var, flatten_product, log_abs, rebuild_product};
use crate::core::expr::{Expr, Rational};
use crate::core::polynomial::Poly;
use crate::simplify::{normalize, simplify_fully, substitute};

use super::integrate::integrate_in_base;
use super::utils::{extract_rational_const, pow_expr_signed};
use super::RischOutcome;

pub(super) fn analyze_algebraic(expr: &Expr, var: &str) -> Option<RischOutcome> {
    let base = find_sqrt_base(expr, var)?;
    let base_poly = Poly::from_expr(&base, var)?;
    let degree = base_poly.degree().unwrap_or(0);
    if degree <= 1 {
        if let Some(result) = integrate_linear_sqrt_substitution(expr, var, &base, &base_poly) {
            return Some(RischOutcome::Integrated {
                result: simplify_fully(result),
                note: "algebraic linear sqrt substitution".to_string(),
            });
        }
        return None;
    }
    if degree > 2 {
        if let Some(result) = integrate_even_base_odd_substitution(expr, var, &base_poly) {
            return Some(RischOutcome::Integrated {
                result: simplify_fully(result),
                note: "algebraic even-base reduction".to_string(),
            });
        }
        return Some(RischOutcome::NonElementary {
            kind: crate::calculus::integrate::NonElementaryKind::SpecialFunctionNeeded,
            note: "algebraic sqrt degree > 2".to_string(),
        });
    }

    if degree == 2 {
        if let Some(result) = integrate_sqrt_quadratic_over_x(expr, var, &base_poly) {
            return Some(RischOutcome::Integrated {
                result: simplify_fully(result),
                note: "algebraic quadratic sqrt/x substitution".to_string(),
            });
        }
        if let Some(result) = integrate_quadratic_sqrt_substitution(expr, var, &base_poly) {
            return Some(RischOutcome::Integrated {
                result: simplify_fully(result),
                note: "algebraic quadratic sqrt substitution".to_string(),
            });
        }
    }

    if let Some(result) = integrate_algebraic_expr(expr, var, &base, &base_poly) {
        return Some(RischOutcome::Integrated {
            result: simplify_fully(result),
            note: "algebraic sqrt reduction".to_string(),
        });
    }

    Some(RischOutcome::Indeterminate {
        note: "algebraic sqrt not reducible".to_string(),
    })
}

fn integrate_even_base_odd_substitution(expr: &Expr, var: &str, base_poly: &Poly) -> Option<Expr> {
    let reduced_poly = even_poly_to_u(base_poly)?;
    if reduced_poly.degree().unwrap_or(0) > 2 {
        return None;
    }
    let rest = factor_out_var(expr, var)?;
    let u_var = "__u";
    let sqrt_u = Expr::Pow(
        Expr::Variable(u_var.to_string()).boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
            .boxed(),
    );
    let rest_u = simplify_fully(crate::simplify::normalize(crate::simplify::substitute(
        &rest, var, &sqrt_u,
    )));
    let base_expr_u = simplify_fully(reduced_poly.to_expr(u_var));
    let result_u = integrate_algebraic_expr(&rest_u, u_var, &base_expr_u, &reduced_poly)?;
    let half = Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()));
    let scaled = simplify_fully(Expr::Mul(half.boxed(), result_u.boxed()));
    let x_sq = Expr::Pow(
        Expr::Variable(var.to_string()).boxed(),
        Expr::integer(2).boxed(),
    );
    Some(simplify_fully(crate::simplify::substitute(
        &scaled, u_var, &x_sq,
    )))
}

fn integrate_linear_sqrt_substitution(
    expr: &Expr,
    var: &str,
    base_expr: &Expr,
    base_poly: &Poly,
) -> Option<Expr> {
    if base_poly.degree()? != 1 {
        return None;
    }
    let a = base_poly.coeff(1);
    if a.is_zero() {
        return None;
    }
    let b = base_poly.coeff(0);
    let base_norm = normalize(base_expr.clone());

    let u_name = fresh_symbol(expr, "__u");
    let u_expr = Expr::Variable(u_name.clone());
    let rewritten = rewrite_linear_sqrt_expr(expr, &base_norm, &u_expr)?;

    let u_sq = Expr::Pow(u_expr.clone().boxed(), Expr::integer(2).boxed());
    let x_sub = Expr::Div(
        Expr::Sub(u_sq.clone().boxed(), Expr::Constant(b.clone()).boxed()).boxed(),
        Expr::Constant(a.clone()).boxed(),
    );
    let rewritten = simplify_fully(substitute(&rewritten, var, &x_sub));
    let dx_du = Expr::Div(
        Expr::Mul(
            Expr::Constant(Rational::from_integer(2.into())).boxed(),
            u_expr.clone().boxed(),
        )
        .boxed(),
        Expr::Constant(a.clone()).boxed(),
    );
    let integrand_u = simplify_fully(Expr::Mul(rewritten.boxed(), dx_du.boxed()));
    let result_u = integrate_in_base(&integrand_u, &u_name)?;

    let sqrt_expr = Expr::Pow(
        base_norm.boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
            .boxed(),
    );
    let restored = substitute(&result_u, &u_name, &sqrt_expr);
    Some(simplify_fully(restored))
}

fn integrate_sqrt_quadratic_over_x(expr: &Expr, var: &str, base_poly: &Poly) -> Option<Expr> {
    if base_poly.degree()? != 2 {
        return None;
    }
    if !base_poly.coeff(0).is_zero() {
        return None;
    }
    let a = base_poly.coeff(2);
    let b = base_poly.coeff(1);
    if !a.is_negative() || b.is_zero() || b.is_negative() {
        return None;
    }

    let (const_factor, factors) = flatten_product(expr);
    let mut sqrt_found = false;
    let mut var_power = Rational::zero();
    let mut other_factors = Vec::new();
    let half = Rational::from_integer(1.into()) / Rational::from_integer(2.into());

    for factor in factors {
        match factor {
            Expr::Variable(name) if name == var => {
                var_power += Rational::one();
            }
            Expr::Pow(base, exp) => match (&*base, &*exp) {
                (Expr::Variable(name), Expr::Constant(k)) if name == var => {
                    var_power += k.clone();
                }
                (_, Expr::Constant(k)) if *k == half => {
                    let base_poly_candidate = Poly::from_expr(&base, var)?;
                    if base_poly_candidate == *base_poly {
                        sqrt_found = true;
                    } else {
                        other_factors.push(Expr::Pow(base.clone(), exp.clone()));
                    }
                }
                _ => other_factors.push(Expr::Pow(base.clone(), exp.clone())),
            },
            other => other_factors.push(other),
        }
    }

    if !sqrt_found {
        return None;
    }
    if !other_factors.is_empty() {
        return None;
    }
    let neg_one = Rational::from_integer((-1).into());
    if var_power != neg_one {
        return None;
    }

    let sqrt_base = Expr::Pow(
        base_poly.to_expr(var).boxed(),
        Expr::Constant(half.clone()).boxed(),
    );
    let sqrt_neg_a = Expr::Pow(
        Expr::Constant(-a.clone()).boxed(),
        Expr::Constant(half.clone()).boxed(),
    );
    let asin_coeff = Expr::Div(Expr::Constant(b.clone()).boxed(), sqrt_neg_a.boxed());
    let inner_coeff = -a / b;
    let asin_arg = Expr::Pow(
        Expr::Mul(
            Expr::Constant(inner_coeff).boxed(),
            Expr::Variable(var.to_string()).boxed(),
        )
        .boxed(),
        Expr::Constant(half).boxed(),
    );
    let asin_term = Expr::Mul(asin_coeff.boxed(), Expr::Asin(asin_arg.boxed()).boxed());
    let sum = Expr::Add(sqrt_base.boxed(), asin_term.boxed());
    Some(simplify_fully(Expr::Mul(
        Expr::Constant(const_factor).boxed(),
        sum.boxed(),
    )))
}

fn integrate_quadratic_sqrt_substitution(
    expr: &Expr,
    var: &str,
    base_poly: &Poly,
) -> Option<Expr> {
    if base_poly.degree()? != 2 {
        return None;
    }
    if !base_poly.coeff(0).is_zero() {
        return None;
    }
    if !has_negative_var_power(expr, var) {
        return None;
    }

    let u_name = fresh_symbol(expr, "__u");
    let u_expr = Expr::Variable(u_name.clone());
    let x_sub = Expr::Pow(u_expr.clone().boxed(), Expr::integer(2).boxed());
    let substituted = simplify_fully(substitute(expr, var, &x_sub));
    let dx_du = Expr::Mul(
        Expr::Constant(Rational::from_integer(2.into())).boxed(),
        u_expr.clone().boxed(),
    );
    let integrand_u = simplify_fully(Expr::Mul(substituted.boxed(), dx_du.boxed()));
    let result_u = integrate_in_base(&integrand_u, &u_name)?;

    let sqrt_x = Expr::Pow(
        Expr::Variable(var.to_string()).boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
            .boxed(),
    );
    let restored = substitute(&result_u, &u_name, &sqrt_x);
    Some(simplify_fully(restored))
}

fn rewrite_linear_sqrt_expr(expr: &Expr, base_norm: &Expr, u_expr: &Expr) -> Option<Expr> {
    if normalize(expr.clone()) == *base_norm {
        return Some(Expr::Pow(
            u_expr.clone().boxed(),
            Expr::integer(2).boxed(),
        ));
    }

    match expr {
        Expr::Constant(_) | Expr::Variable(_) => Some(expr.clone()),
        Expr::Add(a, b) => Some(Expr::Add(
            rewrite_linear_sqrt_expr(a, base_norm, u_expr)?.boxed(),
            rewrite_linear_sqrt_expr(b, base_norm, u_expr)?.boxed(),
        )),
        Expr::Sub(a, b) => Some(Expr::Sub(
            rewrite_linear_sqrt_expr(a, base_norm, u_expr)?.boxed(),
            rewrite_linear_sqrt_expr(b, base_norm, u_expr)?.boxed(),
        )),
        Expr::Mul(a, b) => Some(Expr::Mul(
            rewrite_linear_sqrt_expr(a, base_norm, u_expr)?.boxed(),
            rewrite_linear_sqrt_expr(b, base_norm, u_expr)?.boxed(),
        )),
        Expr::Div(a, b) => Some(Expr::Div(
            rewrite_linear_sqrt_expr(a, base_norm, u_expr)?.boxed(),
            rewrite_linear_sqrt_expr(b, base_norm, u_expr)?.boxed(),
        )),
        Expr::Neg(inner) => rewrite_linear_sqrt_expr(inner, base_norm, u_expr)
            .map(|res| Expr::Neg(res.boxed())),
        Expr::Pow(base, exp) => {
            let exp_const = extract_rational_const(exp)?;
            let base_norm_inner = normalize((**base).clone());
            if !exp_const.is_integer() {
                if is_half_integer(&exp_const) && base_norm_inner == *base_norm {
                    let (q, r) = split_exponent(&exp_const)?;
                    let power = 2 * q + r;
                    return Some(pow_expr_signed(u_expr, power));
                }
                return None;
            }
            let base_replaced = rewrite_linear_sqrt_expr(base, base_norm, u_expr)?;
            Some(Expr::Pow(base_replaced.boxed(), exp.clone()))
        }
        _ => None,
    }
}

fn fresh_symbol(expr: &Expr, base: &str) -> String {
    let mut used = HashSet::new();
    collect_vars(expr, &mut used);
    if !used.contains(base) {
        return base.to_string();
    }
    for idx in 1.. {
        let candidate = format!("{base}{idx}");
        if !used.contains(&candidate) {
            return candidate;
        }
    }
    unreachable!("symbol generation exhausted")
}

fn collect_vars(expr: &Expr, out: &mut HashSet<String>) {
    match expr {
        Expr::Variable(name) => {
            out.insert(name.clone());
        }
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => {
            collect_vars(a, out);
            collect_vars(b, out);
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
        | Expr::Abs(inner) => collect_vars(inner, out),
        Expr::Constant(_) => {}
    }
}

fn has_negative_var_power(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Pow(base, exp) => match (&**base, &**exp) {
            (Expr::Variable(name), Expr::Constant(k)) if name == var => k.is_negative(),
            _ => has_negative_var_power(base, var) || has_negative_var_power(exp, var),
        },
        Expr::Div(_, denom) => contains_var(denom, var),
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) => {
            has_negative_var_power(a, var) || has_negative_var_power(b, var)
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
        | Expr::Abs(inner) => has_negative_var_power(inner, var),
        Expr::Variable(_) | Expr::Constant(_) => false,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SqrtBaseDetection {
    None,
    Found,
    Conflict,
}

fn find_sqrt_base(expr: &Expr, var: &str) -> Option<Expr> {
    let mut state = SqrtBaseDetection::None;
    let mut base: Option<Expr> = None;
    collect_sqrt_bases(expr, var, &mut state, &mut base);
    match state {
        SqrtBaseDetection::None => None,
        SqrtBaseDetection::Conflict => None,
        SqrtBaseDetection::Found => base,
    }
}

fn collect_sqrt_bases(
    expr: &Expr,
    var: &str,
    state: &mut SqrtBaseDetection,
    base: &mut Option<Expr>,
) {
    match expr {
        Expr::Pow(inner, exp) => {
            if let Expr::Constant(k) = &**exp {
                if is_half_integer(k) && contains_var(inner, var) {
                    let candidate = simplify_fully((**inner).clone());
                    match base {
                        None => {
                            *base = Some(candidate);
                            *state = SqrtBaseDetection::Found;
                        }
                        Some(existing) if *existing != candidate => {
                            *state = SqrtBaseDetection::Conflict;
                        }
                        _ => {}
                    }
                }
            }
            collect_sqrt_bases(inner, var, state, base);
            collect_sqrt_bases(exp, var, state, base);
        }
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b) => {
            collect_sqrt_bases(a, var, state, base);
            collect_sqrt_bases(b, var, state, base);
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
        | Expr::Abs(inner) => collect_sqrt_bases(inner, var, state, base),
        Expr::Variable(_) | Expr::Constant(_) => {}
    }
}

fn integrate_algebraic_expr(
    expr: &Expr,
    var: &str,
    base_expr: &Expr,
    base_poly: &Poly,
) -> Option<Expr> {
    match expr {
        Expr::Add(a, b) => Some(Expr::Add(
            integrate_algebraic_expr(a, var, base_expr, base_poly)?.boxed(),
            integrate_algebraic_expr(b, var, base_expr, base_poly)?.boxed(),
        )),
        Expr::Sub(a, b) => Some(Expr::Sub(
            integrate_algebraic_expr(a, var, base_expr, base_poly)?.boxed(),
            integrate_algebraic_expr(b, var, base_expr, base_poly)?.boxed(),
        )),
        Expr::Neg(inner) => integrate_algebraic_expr(inner, var, base_expr, base_poly)
            .map(|res| Expr::Neg(res.boxed())),
        _ => integrate_algebraic_term(expr, var, base_expr, base_poly),
    }
}

fn integrate_algebraic_term(
    expr: &Expr,
    var: &str,
    base_expr: &Expr,
    base_poly: &Poly,
) -> Option<Expr> {
    let (const_factor, factors) = flatten_product(expr);
    if const_factor.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let base_norm = normalize(base_expr.clone());
    let mut poly_power: i64 = 0;
    let mut sqrt_power: i64 = 0;
    let mut rest_factors = Vec::new();

    for factor in factors {
        match extract_base_powers(&factor, &base_norm) {
            Ok(Some((delta_poly, delta_sqrt))) => {
                poly_power += delta_poly;
                sqrt_power += delta_sqrt;
            }
            Ok(None) => rest_factors.push(factor),
            Err(()) => return None,
        }
    }

    let rest_expr = rebuild_product(const_factor, rest_factors);
    let mut rest_poly = Poly::from_expr(&rest_expr, var)?;
    if rest_poly.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let sqrt_q = sqrt_power / 2;
    let sqrt_r = sqrt_power % 2;
    poly_power += sqrt_q;
    sqrt_power = sqrt_r;

    if sqrt_power == 0 {
        return None;
    }
    if sqrt_power != 1 && sqrt_power != -1 {
        return None;
    }

    if sqrt_power == -1 && poly_power < 0 {
        let denom_power = (-poly_power) as usize;
        return integrate_poly_over_sqrt_quadratic_power(&rest_poly, base_poly, var, denom_power);
    }

    if poly_power < 0 {
        let divisor = base_poly.pow((-poly_power) as usize);
        rest_poly = rest_poly.div_exact(&divisor)?;
        poly_power = 0;
    }

    let mut poly_total = rest_poly * base_poly.pow(poly_power as usize);
    if sqrt_power == 1 {
        poly_total = poly_total * base_poly.clone();
    }

    integrate_poly_over_sqrt_quadratic(&poly_total, base_poly, var)
}

fn factor_out_var(expr: &Expr, var: &str) -> Option<Expr> {
    let (const_factor, mut factors) = flatten_product(expr);
    let mut removed = false;
    let mut idx = 0;
    while idx < factors.len() {
        match &factors[idx] {
            Expr::Variable(name) if name == var => {
                factors.remove(idx);
                removed = true;
                break;
            }
            Expr::Pow(base, exp) => {
                if let Expr::Variable(name) = &**base {
                    if name == var {
                        if let Expr::Constant(power) = &**exp {
                            if power.is_integer() {
                                let int_power = power.to_integer();
                                if int_power > BigInt::from(0) {
                                    removed = true;
                                    if int_power == BigInt::from(1) {
                                        factors.remove(idx);
                                    } else {
                                        let new_exp =
                                            Rational::from_integer(int_power - BigInt::from(1));
                                        factors[idx] = Expr::Pow(
                                            base.clone(),
                                            Expr::Constant(new_exp).boxed(),
                                        );
                                    }
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        idx += 1;
    }
    if !removed {
        if let Some(divided) = divide_out_var(expr, var) {
            return Some(simplify_fully(divided));
        }
        let var_expr = Expr::Variable(var.to_string());
        let candidate = simplify_fully(Expr::Div(expr.clone().boxed(), var_expr.clone().boxed()));
        let rebuilt = simplify_fully(Expr::Mul(candidate.clone().boxed(), var_expr.boxed()));
        if simplify_fully(expr.clone()) == rebuilt {
            return Some(candidate);
        }
        return None;
    }
    Some(rebuild_product(const_factor, factors))
}

fn divide_out_var(expr: &Expr, var: &str) -> Option<Expr> {
    match expr {
        Expr::Variable(name) if name == var => Some(Expr::Constant(Rational::one())),
        Expr::Mul(a, b) => {
            if let Some(left) = divide_out_var(a, var) {
                Some(Expr::Mul(left.boxed(), b.clone().boxed()))
            } else {
                divide_out_var(b, var).map(|right| Expr::Mul(a.clone().boxed(), right.boxed()))
            }
        }
        Expr::Div(a, b) => divide_out_var(a, var)
            .map(|left| Expr::Div(left.boxed(), b.clone().boxed())),
        Expr::Pow(base, exp) => {
            if let Expr::Variable(name) = &**base {
                if name == var {
                    if let Expr::Constant(power) = &**exp {
                        if power.is_integer() {
                            let int_power = power.to_integer();
                            if int_power > BigInt::from(0) {
                                if int_power == BigInt::from(1) {
                                    return Some(Expr::Constant(Rational::one()));
                                }
                                let new_exp =
                                    Rational::from_integer(int_power - BigInt::from(1));
                                return Some(Expr::Pow(
                                    base.clone(),
                                    Expr::Constant(new_exp).boxed(),
                                ));
                            }
                        }
                    }
                }
            }
            None
        }
        Expr::Add(a, b) => {
            let left = divide_out_var(a, var)?;
            let right = divide_out_var(b, var)?;
            Some(Expr::Add(left.boxed(), right.boxed()))
        }
        Expr::Sub(a, b) => {
            let left = divide_out_var(a, var)?;
            let right = divide_out_var(b, var)?;
            Some(Expr::Sub(left.boxed(), right.boxed()))
        }
        Expr::Neg(inner) => divide_out_var(inner, var).map(|res| Expr::Neg(res.boxed())),
        _ => None,
    }
}

fn even_poly_to_u(poly: &Poly) -> Option<Poly> {
    let mut coeffs = BTreeMap::new();
    for (exp, coeff) in poly.coeff_entries() {
        if exp % 2 != 0 {
            return None;
        }
        coeffs.insert(exp / 2, coeff);
    }
    Some(Poly { coeffs })
}

#[cfg(test)]
mod algebraic_even_reduction_tests {
    use super::*;
    use crate::core::parser::parse_expr;

    #[test]
    fn reduces_quartic_even_base_odd_integrand() {
        let expr = parse_expr("x/(x^4+1)^(1/2)").unwrap();
        let base = parse_expr("x^4 + 1").unwrap();
        let base_poly = Poly::from_expr(&base, "x").unwrap();
        assert!(
            integrate_even_base_odd_substitution(&expr, "x", &base_poly).is_some(),
            "expected quartic even-base reduction to succeed"
        );
    }

    #[test]
    fn reduces_quartic_even_base_with_quadratic_term() {
        let expr = parse_expr("x/(x^4+x^2+1)^(1/2)").unwrap();
        let base = parse_expr("x^4 + x^2 + 1").unwrap();
        let base_poly = Poly::from_expr(&base, "x").unwrap();
        assert!(
            integrate_even_base_odd_substitution(&expr, "x", &base_poly).is_some(),
            "expected quartic even-base reduction with quadratic term to succeed"
        );
    }

    #[test]
    fn reduces_quartic_even_base_with_even_multiplier() {
        let expr = parse_expr("x*(x^2+1)/(x^4+x^2+1)^(1/2)").unwrap();
        let base = parse_expr("x^4 + x^2 + 1").unwrap();
        let base_poly = Poly::from_expr(&base, "x").unwrap();
        assert!(
            integrate_even_base_odd_substitution(&expr, "x", &base_poly).is_some(),
            "expected even-base reduction with even multiplier to succeed"
        );
    }
}

fn extract_base_powers(factor: &Expr, base: &Expr) -> Result<Option<(i64, i64)>, ()> {
    if factor == base {
        return Ok(Some((1, 0)));
    }
    if let Expr::Pow(inner, exp) = factor {
        let inner_norm = normalize((**inner).clone());
        if inner_norm != *base {
            return Ok(None);
        }
        let Expr::Constant(k) = &**exp else {
            return Err(());
        };
        return split_exponent(k).map(Some).ok_or(());
    }
    Ok(None)
}

fn split_exponent(exp: &Rational) -> Option<(i64, i64)> {
    if exp.is_integer() {
        return Some((exp.to_integer().to_i64()?, 0));
    }
    if !is_half_integer(exp) {
        return None;
    }
    let two = BigInt::from(2);
    let (q, r) = exp.numer().div_rem(&two);
    let q = q.to_i64()?;
    let r = r.to_i64()?;
    if r == 0 || r == 1 || r == -1 {
        Some((q, r))
    } else {
        None
    }
}

fn integrate_poly_over_sqrt_quadratic(poly: &Poly, base_poly: &Poly, var: &str) -> Option<Expr> {
    if poly.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }
    if base_poly.degree()? != 2 {
        return None;
    }
    let a = base_poly.coeff(2);
    if a.is_zero() {
        return None;
    }
    let b = base_poly.coeff(1);
    let c = base_poly.coeff(0);

    let two = Rational::from_integer(2.into());
    let four = Rational::from_integer(4.into());
    let h = b.clone() / (two.clone() * a.clone());
    let shift = -h.clone();
    let four_ac = four.clone() * a.clone() * c.clone();
    let b_sq = b.clone() * b.clone();
    let denom = four * a.clone() * a.clone();
    let d = (four_ac - b_sq) / denom;

    let shifted = poly_shift(poly, &shift);

    let u_expr = Expr::Add(
        Expr::Variable(var.to_string()).boxed(),
        Expr::Constant(h).boxed(),
    );
    let u_sq = Expr::Pow(u_expr.clone().boxed(), Expr::integer(2).boxed());
    let max_deg = shifted.degree().unwrap_or(0);

    if a.is_negative() && d.is_negative() {
        let d_pos = -d.clone();
        let u2_minus_d = Expr::Sub(
            Expr::Constant(d_pos.clone()).boxed(),
            u_sq.boxed(),
        );
        let sqrt_expr = Expr::Pow(
            u2_minus_d.boxed(),
            Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
                .boxed(),
        );
        let sqrt_d = Expr::Pow(
            Expr::Constant(d_pos.clone()).boxed(),
            Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
                .boxed(),
        );
        let asin_arg = Expr::Div(u_expr.clone().boxed(), sqrt_d.boxed());

        let mut integrals: Vec<Expr> = Vec::with_capacity(max_deg + 1);
        integrals.push(Expr::Asin(asin_arg.boxed()));
        if max_deg >= 1 {
            integrals.push(Expr::Neg(sqrt_expr.clone().boxed()));
        }
        for n in 2..=max_deg {
            let n_rat = Rational::from_integer(BigInt::from(n as i64));
            let term1 = Expr::Div(
                Expr::Mul(
                    pow_expr(&u_expr, n - 1).boxed(),
                    sqrt_expr.clone().boxed(),
                )
                .boxed(),
                Expr::Constant(n_rat.clone()).boxed(),
            );
            let coeff = Rational::from_integer(BigInt::from((n - 1) as i64)) * d_pos.clone()
                / n_rat;
            let term2 = Expr::Mul(
                Expr::Constant(coeff).boxed(),
                integrals[n - 2].clone().boxed(),
            );
            let expr = Expr::Sub(term2.boxed(), term1.boxed());
            integrals.push(simplify_fully(expr));
        }

        let mut sum: Option<Expr> = None;
        for (exp, coeff) in shifted.coeff_entries() {
            if coeff.is_zero() {
                continue;
            }
            let term = Expr::Mul(
                Expr::Constant(coeff).boxed(),
                integrals[exp].clone().boxed(),
            );
            sum = Some(match sum {
                None => term,
                Some(acc) => Expr::Add(acc.boxed(), term.boxed()),
            });
        }
        let sum = sum.unwrap_or_else(|| Expr::Constant(Rational::zero()));
        let scale = Expr::Pow(
            Expr::Constant(-a.clone()).boxed(),
            Expr::Constant(
                Rational::from_integer(BigInt::from(-1)) / Rational::from_integer(2.into()),
            )
            .boxed(),
        );
        return Some(simplify_fully(Expr::Mul(scale.boxed(), sum.boxed())));
    }

    let u2_plus_d = Expr::Add(u_sq.boxed(), Expr::Constant(d.clone()).boxed());
    let sqrt_expr = Expr::Pow(
        u2_plus_d.boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
            .boxed(),
    );

    let mut integrals: Vec<Expr> = Vec::with_capacity(max_deg + 1);
    integrals.push(log_abs(Expr::Add(
        u_expr.clone().boxed(),
        sqrt_expr.clone().boxed(),
    )));
    if max_deg >= 1 {
        integrals.push(sqrt_expr.clone());
    }
    for n in 2..=max_deg {
        let n_rat = Rational::from_integer(BigInt::from(n as i64));
        let term1 = Expr::Div(
            Expr::Mul(
                pow_expr(&u_expr, n - 1).boxed(),
                sqrt_expr.clone().boxed(),
            )
            .boxed(),
            Expr::Constant(n_rat.clone()).boxed(),
        );
        let coeff = Rational::from_integer(BigInt::from((n - 1) as i64)) * d.clone() / n_rat;
        let term2 = Expr::Mul(
            Expr::Constant(coeff).boxed(),
            integrals[n - 2].clone().boxed(),
        );
        let expr = Expr::Sub(term1.boxed(), term2.boxed());
        integrals.push(simplify_fully(expr));
    }

    let mut sum: Option<Expr> = None;
    for (exp, coeff) in shifted.coeff_entries() {
        if coeff.is_zero() {
            continue;
        }
        let term = Expr::Mul(
            Expr::Constant(coeff).boxed(),
            integrals[exp].clone().boxed(),
        );
        sum = Some(match sum {
            None => term,
            Some(acc) => Expr::Add(acc.boxed(), term.boxed()),
        });
    }
    let sum = sum.unwrap_or_else(|| Expr::Constant(Rational::zero()));
    let scale = Expr::Pow(
        Expr::Constant(a).boxed(),
        Expr::Constant(
            Rational::from_integer(BigInt::from(-1)) / Rational::from_integer(2.into()),
        )
        .boxed(),
    );
    Some(simplify_fully(Expr::Mul(scale.boxed(), sum.boxed())))
}

#[derive(Clone)]
struct QuadraticPowerContext {
    u_expr: Expr,
    u2_plus_d: Expr,
    sqrt_expr: Expr,
    log_expr: Expr,
    d: Rational,
}

fn integrate_poly_over_sqrt_quadratic_power(
    poly: &Poly,
    base_poly: &Poly,
    var: &str,
    power: usize,
) -> Option<Expr> {
    if power == 0 {
        return integrate_poly_over_sqrt_quadratic(poly, base_poly, var);
    }
    if poly.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }
    if base_poly.degree()? != 2 {
        return None;
    }
    let a = base_poly.coeff(2);
    if a.is_zero() {
        return None;
    }
    let b = base_poly.coeff(1);
    let c = base_poly.coeff(0);

    let two = Rational::from_integer(2.into());
    let four = Rational::from_integer(4.into());
    let h = b.clone() / (two.clone() * a.clone());
    let shift = -h.clone();
    let four_ac = four.clone() * a.clone() * c.clone();
    let b_sq = b.clone() * b.clone();
    let denom = four * a.clone() * a.clone();
    let d = (four_ac - b_sq) / denom;

    let shifted = poly_shift(poly, &shift);

    let u_expr = Expr::Add(
        Expr::Variable(var.to_string()).boxed(),
        Expr::Constant(h).boxed(),
    );
    let u_sq = Expr::Pow(u_expr.clone().boxed(), Expr::integer(2).boxed());
    let u2_plus_d = Expr::Add(u_sq.boxed(), Expr::Constant(d.clone()).boxed());
    let sqrt_expr = Expr::Pow(
        u2_plus_d.clone().boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
            .boxed(),
    );
    let log_expr = log_abs(Expr::Add(
        u_expr.clone().boxed(),
        sqrt_expr.clone().boxed(),
    ));

    let ctx = QuadraticPowerContext {
        u_expr,
        u2_plus_d,
        sqrt_expr,
        log_expr,
        d,
    };
    let mut memo = HashMap::new();

    let mut sum: Option<Expr> = None;
    for (exp, coeff) in shifted.coeff_entries() {
        if coeff.is_zero() {
            continue;
        }
        let integral = monomial_integral(exp, power, &ctx, &mut memo)?;
        let term = Expr::Mul(Expr::Constant(coeff).boxed(), integral.boxed());
        sum = Some(match sum {
            None => term,
            Some(acc) => Expr::Add(acc.boxed(), term.boxed()),
        });
    }

    let sum = sum.unwrap_or_else(|| Expr::Constant(Rational::zero()));
    let scale_exp = Rational::from_integer(BigInt::from(-(2 * power as i64 + 1)))
        / Rational::from_integer(2.into());
    let scale = Expr::Pow(Expr::Constant(a).boxed(), Expr::Constant(scale_exp).boxed());
    Some(simplify_fully(Expr::Mul(scale.boxed(), sum.boxed())))
}

fn monomial_integral(
    exp: usize,
    power: usize,
    ctx: &QuadraticPowerContext,
    memo: &mut HashMap<(usize, usize), Expr>,
) -> Option<Expr> {
    if let Some(cached) = memo.get(&(exp, power)) {
        return Some(cached.clone());
    }

    if ctx.d.is_zero() {
        let k = exp as i64 - (2 * power as i64 + 1);
        let result = if k == -1 {
            log_abs(ctx.u_expr.clone())
        } else {
            let new_exp = k + 1;
            let denom = Rational::from_integer(BigInt::from(new_exp));
            let pow = pow_expr_signed(&ctx.u_expr, new_exp);
            Expr::Div(pow.boxed(), Expr::Constant(denom).boxed())
        };
        memo.insert((exp, power), result.clone());
        return Some(result);
    }

    let result = match exp {
        0 => {
            if power == 0 {
                ctx.log_expr.clone()
            } else {
                integral_zero(power, ctx, memo)?
            }
        }
        1 => integral_one(power, ctx),
        _ => {
            if power == 0 {
                integral_sqrt(exp, ctx, memo)?
            } else {
                let lower = monomial_integral(exp - 2, power - 1, ctx, memo)?;
                let same = monomial_integral(exp - 2, power, ctx, memo)?;
                Expr::Sub(
                    lower.boxed(),
                    Expr::Mul(Expr::Constant(ctx.d.clone()).boxed(), same.boxed()).boxed(),
                )
            }
        }
    };

    memo.insert((exp, power), result.clone());
    Some(result)
}

fn integral_zero(
    power: usize,
    ctx: &QuadraticPowerContext,
    memo: &mut HashMap<(usize, usize), Expr>,
) -> Option<Expr> {
    if power == 0 {
        return Some(ctx.log_expr.clone());
    }
    let denom = ctx.d.clone() * Rational::from_integer(BigInt::from(2 * power as i64 - 1));
    if denom.is_zero() {
        return None;
    }
    let coeff = Rational::one() / denom.clone();
    let exponent = Rational::from_integer(1.into()) / Rational::from_integer(2.into())
        - Rational::from_integer(BigInt::from(power as i64));
    let pow = Expr::Pow(
        ctx.u2_plus_d.clone().boxed(),
        Expr::Constant(exponent).boxed(),
    );
    let term1 = Expr::Mul(
        Expr::Constant(coeff).boxed(),
        Expr::Mul(ctx.u_expr.clone().boxed(), pow.boxed()).boxed(),
    );
    let recur_coeff =
        Rational::from_integer(BigInt::from(2 * (power as i64 - 1))) / denom;
    let prev = monomial_integral(0, power - 1, ctx, memo)?;
    let term2 = Expr::Mul(Expr::Constant(recur_coeff).boxed(), prev.boxed());
    Some(simplify_fully(Expr::Add(term1.boxed(), term2.boxed())))
}

fn integral_one(power: usize, ctx: &QuadraticPowerContext) -> Expr {
    let exponent = Rational::from_integer(1.into()) / Rational::from_integer(2.into())
        - Rational::from_integer(BigInt::from(power as i64));
    let denom = Rational::from_integer(BigInt::from(1 - 2 * power as i64));
    let pow = Expr::Pow(
        ctx.u2_plus_d.clone().boxed(),
        Expr::Constant(exponent).boxed(),
    );
    let coeff = Rational::one() / denom;
    simplify_fully(Expr::Mul(Expr::Constant(coeff).boxed(), pow.boxed()))
}

fn integral_sqrt(
    exp: usize,
    ctx: &QuadraticPowerContext,
    memo: &mut HashMap<(usize, usize), Expr>,
) -> Option<Expr> {
    if exp == 0 {
        return Some(ctx.log_expr.clone());
    }
    if exp == 1 {
        return Some(ctx.sqrt_expr.clone());
    }
    let n_rat = Rational::from_integer(BigInt::from(exp as i64));
    let term1 = Expr::Div(
        Expr::Mul(
            pow_expr(&ctx.u_expr, exp - 1).boxed(),
            ctx.sqrt_expr.clone().boxed(),
        )
        .boxed(),
        Expr::Constant(n_rat.clone()).boxed(),
    );
    let coeff = Rational::from_integer(BigInt::from((exp - 1) as i64)) * ctx.d.clone() / n_rat;
    let prev = monomial_integral(exp - 2, 0, ctx, memo)?;
    let term2 = Expr::Mul(Expr::Constant(coeff).boxed(), prev.boxed());
    Some(simplify_fully(Expr::Sub(term1.boxed(), term2.boxed())))
}

fn poly_shift(poly: &Poly, shift: &Rational) -> Poly {
    let mut coeffs = BTreeMap::new();
    for (exp, coeff) in poly.coeff_entries() {
        for k in 0..=exp {
            let bin = binomial(exp, k);
            let pow = rational_pow(shift, exp - k);
            let term_coeff = coeff.clone() * Rational::from_integer(bin) * pow;
            if term_coeff.is_zero() {
                continue;
            }
            match coeffs.get_mut(&k) {
                Some(existing) => *existing += term_coeff,
                None => {
                    coeffs.insert(k, term_coeff);
                }
            }
        }
    }
    Poly { coeffs }
}

fn rational_pow(base: &Rational, exp: usize) -> Rational {
    if exp == 0 {
        return Rational::one();
    }
    let mut result = Rational::one();
    let mut power = base.clone();
    let mut n = exp;
    while n > 0 {
        if n % 2 == 1 {
            result *= power.clone();
        }
        power *= power.clone();
        n /= 2;
    }
    result
}

fn binomial(n: usize, k: usize) -> BigInt {
    let k = k.min(n - k);
    let mut numer = BigInt::one();
    let mut denom = BigInt::one();
    for i in 0..k {
        numer *= BigInt::from((n - i) as i64);
        denom *= BigInt::from((i + 1) as i64);
    }
    numer / denom
}

fn pow_expr(base: &Expr, exp: usize) -> Expr {
    if exp == 0 {
        Expr::Constant(Rational::one())
    } else if exp == 1 {
        base.clone()
    } else {
        Expr::Pow(base.clone().boxed(), Expr::integer(exp as i64).boxed())
    }
}

fn is_half_integer(exp: &Rational) -> bool {
    exp.denom() == &BigInt::from(2)
}
