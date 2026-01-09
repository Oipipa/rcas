use std::collections::HashSet;

use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};

use crate::calculus::differentiate;
use crate::core::expr::{Expr, Rational};
use crate::core::polynomial::Poly;
use crate::simplify::{normalize, simplify, simplify_fully, substitute};

use super::limits::{SUBSTITUTION_CANDIDATE_LIMIT, TRANSFORM_SIZE_LIMIT};
use super::{
    direct::integrate_basic,
    apply_constant_factor, constant_ratio, contains_var, expr_size, flatten_product,
    fresh_var_name, integrate, is_constant_wrt, is_zero_expr, log_abs, rebuild_product,
    split_constant_factors, IntegrationResult,
};

pub(super) fn integrate_by_substitution(expr: &Expr, var: &str) -> Option<Expr> {
    let (const_expr, factors) = split_constant_factors(expr, var);
    if is_zero_expr(&const_expr) {
        return Some(Expr::Constant(Rational::zero()));
    }
    if let Some(result) = integrate_log_derivative(expr, var) {
        return Some(result);
    }
    if let Some(result) = integrate_quadratic_sqrt_heuristic(expr, var) {
        return Some(result);
    }

    for (idx, factor) in factors.iter().enumerate() {
        let Some(inner) = inner_candidate(factor) else {
            continue;
        };
        let inner_derivative = simplify_fully(differentiate(var, inner));
        if inner_derivative.is_zero() {
            continue;
        }

        let remaining: Vec<Expr> = factors
            .iter()
            .enumerate()
            .filter_map(|(i, f)| if i == idx { None } else { Some(f.clone()) })
            .collect();
        let remaining_expr = simplify_fully(apply_constant_factor(
            const_expr.clone(),
            rebuild_product(Rational::one(), remaining),
        ));

        let multiplier = {
            let ratio_expr = simplify_fully(Expr::Div(
                remaining_expr.clone().boxed(),
                inner_derivative.clone().boxed(),
            ));
            if is_constant_wrt(&ratio_expr, var) {
                Some(ratio_expr)
            } else {
                constant_ratio(&remaining_expr, &inner_derivative, var)
            }
        };

        if let Some(multiplier) = multiplier {
            if let Some(inner_result) = integrate_with_respect_to_inner(factor, inner) {
                return Some(simplify(Expr::Mul(
                    multiplier.boxed(),
                    inner_result.boxed(),
                )));
            }
        }
    }

    if let Some(result) = integrate_function_of_inner(expr, var) {
        return Some(result);
    }

    None
}

pub(super) fn integrate_log_derivative(expr: &Expr, var: &str) -> Option<Expr> {
    let (num, den) = super::as_rational_expr(expr);
    let num = simplify_fully(num);
    let den = simplify_fully(den);
    if is_constant_wrt(&den, var) {
        return None;
    }
    let den_derivative = simplify_fully(differentiate(var, &den));
    if den_derivative.is_zero() {
        return None;
    }
    let ratio = constant_ratio(&num, &den_derivative, var)?;
    if !is_constant_wrt(&ratio, var) {
        return None;
    }
    Some(simplify(Expr::Mul(ratio.boxed(), log_abs(den).boxed())))
}

fn integrate_quadratic_sqrt_heuristic(expr: &Expr, var: &str) -> Option<Expr> {
    let (base_expr, base_poly) = find_quadratic_sqrt_base(expr, var)?;
    let base_norm = normalize(base_expr.clone());
    if let Some(result) =
        integrate_quadratic_trig_substitution(expr, var, &base_expr, &base_poly, &base_norm)
    {
        return Some(result);
    }
    integrate_quadratic_euler_substitution(expr, var, &base_expr, &base_poly, &base_norm)
}

fn integrate_quadratic_trig_substitution(
    expr: &Expr,
    var: &str,
    _base_expr: &Expr,
    base_poly: &Poly,
    base_norm: &Expr,
) -> Option<Expr> {
    if base_poly.degree()? != 2 {
        return None;
    }
    let a = base_poly.coeff(2);
    let b = base_poly.coeff(1);
    let c = base_poly.coeff(0);
    if !b.is_zero() || a.is_zero() || c.is_zero() {
        return None;
    }

    let u_name = fresh_var_name(expr, var, "u");
    let u_var = Expr::Variable(u_name.clone());
    let x_var = Expr::Variable(var.to_string());

    let (x_sub, sqrt_sub, dx_du, u_back) = if a < Rational::zero() && c > Rational::zero() {
        let scale_sq = c.clone() / (-a.clone());
        let scale = sqrt_rational_expr(&scale_sq);
        let x_sub = Expr::Mul(scale.clone().boxed(), Expr::Sin(u_var.clone().boxed()).boxed());
        let sqrt_c = sqrt_rational_expr(&c);
        let sqrt_sub = Expr::Mul(sqrt_c.boxed(), Expr::Cos(u_var.clone().boxed()).boxed());
        let dx_du = Expr::Mul(scale.clone().boxed(), Expr::Cos(u_var.clone().boxed()).boxed());
        let ratio = Expr::Div(x_var.boxed(), scale.boxed());
        let u_back = Expr::Asin(ratio.boxed());
        (x_sub, sqrt_sub, dx_du, u_back)
    } else if a > Rational::zero() && c > Rational::zero() {
        let scale_sq = c.clone() / a.clone();
        let scale = sqrt_rational_expr(&scale_sq);
        let x_sub = Expr::Mul(scale.clone().boxed(), Expr::Tan(u_var.clone().boxed()).boxed());
        let sqrt_c = sqrt_rational_expr(&c);
        let sqrt_sub = Expr::Mul(sqrt_c.boxed(), Expr::Sec(u_var.clone().boxed()).boxed());
        let sec_sq = Expr::Pow(
            Expr::Sec(u_var.clone().boxed()).boxed(),
            Expr::Constant(Rational::from_integer(2.into())).boxed(),
        );
        let dx_du = Expr::Mul(scale.clone().boxed(), sec_sq.boxed());
        let ratio = Expr::Div(x_var.boxed(), scale.boxed());
        let u_back = Expr::Atan(ratio.boxed());
        (x_sub, sqrt_sub, dx_du, u_back)
    } else if a > Rational::zero() && c < Rational::zero() {
        let scale_sq = (-c.clone()) / a.clone();
        let scale = sqrt_rational_expr(&scale_sq);
        let x_sub = Expr::Mul(scale.clone().boxed(), Expr::Sec(u_var.clone().boxed()).boxed());
        let sqrt_c = sqrt_rational_expr(&(-c));
        let sqrt_sub = Expr::Mul(sqrt_c.boxed(), Expr::Tan(u_var.clone().boxed()).boxed());
        let dx_du = Expr::Mul(
            scale.clone().boxed(),
            Expr::Mul(
                Expr::Sec(u_var.clone().boxed()).boxed(),
                Expr::Tan(u_var.clone().boxed()).boxed(),
            )
            .boxed(),
        );
        let ratio = Expr::Div(x_var.boxed(), scale.boxed());
        let u_back = Expr::Asec(ratio.boxed());
        (x_sub, sqrt_sub, dx_du, u_back)
    } else {
        return None;
    };

    integrate_quadratic_sqrt_substitution(
        expr,
        var,
        base_norm,
        &sqrt_sub,
        &u_name,
        &x_sub,
        &dx_du,
        &u_back,
    )
}

fn integrate_quadratic_euler_substitution(
    expr: &Expr,
    var: &str,
    base_expr: &Expr,
    base_poly: &Poly,
    base_norm: &Expr,
) -> Option<Expr> {
    if base_poly.degree()? != 2 {
        return None;
    }
    let a = base_poly.coeff(2);
    if a.is_zero() {
        return None;
    }
    let b = base_poly.coeff(1);
    let c = base_poly.coeff(0);
    let t_name = fresh_var_name(expr, var, "t");
    let t_var = Expr::Variable(t_name.clone());
    let x_var = Expr::Variable(var.to_string());
    let two = Rational::from_integer(2.into());
    let half = Rational::new(1.into(), 2.into());
    let sqrt_base = Expr::Pow(base_expr.clone().boxed(), Expr::Constant(half).boxed());

    let (x_sub, sqrt_sub, dx_dt, t_back) = if a > Rational::zero() {
        let sqrt_a = sqrt_rational_expr(&a);
        let denom = Expr::Sub(
            Expr::Constant(b.clone()).boxed(),
            Expr::Mul(
                Expr::Constant(two.clone()).boxed(),
                Expr::Mul(sqrt_a.clone().boxed(), t_var.clone().boxed()).boxed(),
            )
            .boxed(),
        );
        let t_sq = Expr::Pow(t_var.clone().boxed(), Expr::integer(2).boxed());
        let num = Expr::Sub(t_sq.clone().boxed(), Expr::Constant(c.clone()).boxed());
        let x_sub = Expr::Div(num.clone().boxed(), denom.clone().boxed());
        let sqrt_sub = Expr::Add(
            Expr::Mul(sqrt_a.clone().boxed(), x_sub.clone().boxed()).boxed(),
            t_var.clone().boxed(),
        );
        let t_denom = Expr::Mul(t_var.clone().boxed(), denom.clone().boxed());
        let s_num = Expr::Mul(sqrt_a.clone().boxed(), num.clone().boxed());
        let sum = Expr::Add(t_denom.boxed(), s_num.boxed());
        let dx_dt = Expr::Div(
            Expr::Mul(Expr::Constant(two.clone()).boxed(), sum.boxed()).boxed(),
            Expr::Pow(denom.boxed(), Expr::integer(2).boxed()).boxed(),
        );
        let t_back = Expr::Sub(
            sqrt_base.boxed(),
            Expr::Mul(sqrt_a.boxed(), x_var.boxed()).boxed(),
        );
        (x_sub, sqrt_sub, dx_dt, t_back)
    } else if c > Rational::zero() {
        let sqrt_c = sqrt_rational_expr(&c);
        let t_sq = Expr::Pow(t_var.clone().boxed(), Expr::integer(2).boxed());
        let denom = Expr::Sub(Expr::Constant(a.clone()).boxed(), t_sq.clone().boxed());
        let num = Expr::Sub(
            Expr::Mul(Expr::Constant(two.clone()).boxed(), Expr::Mul(sqrt_c.clone().boxed(), t_var.clone().boxed()).boxed()).boxed(),
            Expr::Constant(b.clone()).boxed(),
        );
        let x_sub = Expr::Div(num.clone().boxed(), denom.clone().boxed());
        let sqrt_sub = Expr::Add(
            Expr::Mul(t_var.clone().boxed(), x_sub.clone().boxed()).boxed(),
            sqrt_c.clone().boxed(),
        );
        let r_denom = Expr::Mul(sqrt_c.clone().boxed(), denom.clone().boxed());
        let t_num = Expr::Mul(t_var.clone().boxed(), num.clone().boxed());
        let sum = Expr::Add(r_denom.boxed(), t_num.boxed());
        let dx_dt = Expr::Div(
            Expr::Mul(Expr::Constant(two.clone()).boxed(), sum.boxed()).boxed(),
            Expr::Pow(denom.boxed(), Expr::integer(2).boxed()).boxed(),
        );
        let t_back = Expr::Div(
            Expr::Sub(sqrt_base.boxed(), sqrt_c.boxed()).boxed(),
            x_var.boxed(),
        );
        (x_sub, sqrt_sub, dx_dt, t_back)
    } else {
        let four = Rational::from_integer(4.into());
        let delta = b.clone() * b.clone() - four * a.clone() * c.clone();
        if delta <= Rational::zero() {
            return None;
        }
        let sqrt_delta = sqrt_rational_expr(&delta);
        let two_a = Rational::from_integer(2.into()) * a.clone();
        let r1 = Expr::Div(
            Expr::Sub(
                Expr::Constant(-b.clone()).boxed(),
                sqrt_delta.clone().boxed(),
            )
            .boxed(),
            Expr::Constant(two_a.clone()).boxed(),
        );
        let r2 = Expr::Div(
            Expr::Add(
                Expr::Constant(-b.clone()).boxed(),
                sqrt_delta.clone().boxed(),
            )
            .boxed(),
            Expr::Constant(two_a.clone()).boxed(),
        );
        let t_sq = Expr::Pow(t_var.clone().boxed(), Expr::integer(2).boxed());
        let denom = Expr::Sub(Expr::Constant(a.clone()).boxed(), t_sq.clone().boxed());
        let num = Expr::Sub(
            Expr::Mul(Expr::Constant(a.clone()).boxed(), r2.clone().boxed()).boxed(),
            Expr::Mul(t_sq.boxed(), r1.clone().boxed()).boxed(),
        );
        let x_sub = Expr::Div(num.clone().boxed(), denom.clone().boxed());
        let sqrt_sub = Expr::Mul(
            t_var.clone().boxed(),
            Expr::Sub(x_sub.clone().boxed(), r1.clone().boxed()).boxed(),
        );
        let dx_dt = Expr::Div(
            Expr::Mul(
                Expr::Mul(Expr::Constant(two.clone()).boxed(), t_var.clone().boxed()).boxed(),
                sqrt_delta.boxed(),
            )
            .boxed(),
            Expr::Pow(denom.boxed(), Expr::integer(2).boxed()).boxed(),
        );
        let t_back = Expr::Div(
            sqrt_base.boxed(),
            Expr::Sub(x_var.boxed(), r1.boxed()).boxed(),
        );
        (x_sub, sqrt_sub, dx_dt, t_back)
    };

    integrate_quadratic_sqrt_substitution(
        expr,
        var,
        base_norm,
        &sqrt_sub,
        &t_name,
        &x_sub,
        &dx_dt,
        &t_back,
    )
}

fn integrate_quadratic_sqrt_substitution(
    expr: &Expr,
    var: &str,
    base_norm: &Expr,
    sqrt_sub: &Expr,
    sub_name: &str,
    x_sub: &Expr,
    dx_dsub: &Expr,
    back_sub: &Expr,
) -> Option<Expr> {
    let rewritten = rewrite_quadratic_sqrt_expr(expr, base_norm, sqrt_sub)?;
    let substituted = simplify_fully(substitute(&rewritten, var, x_sub));
    let integrand_sub = simplify_fully(Expr::Mul(substituted.boxed(), dx_dsub.clone().boxed()));
    if expr_size(&integrand_sub) > TRANSFORM_SIZE_LIMIT {
        return None;
    }
    let result_sub = if let Some(result) = integrate_basic(&integrand_sub, sub_name) {
        result
    } else if let Some((num, den)) = rationalize_expr(&integrand_sub, sub_name) {
        let rational = simplify_fully(Expr::Div(num.boxed(), den.boxed()));
        integrate_basic(&rational, sub_name)?
    } else {
        return None;
    };
    let restored = substitute(&result_sub, sub_name, back_sub);
    Some(simplify(restored))
}

fn find_quadratic_sqrt_base(expr: &Expr, var: &str) -> Option<(Expr, Poly)> {
    let mut base = None;
    if !collect_quadratic_sqrt_base(expr, var, &mut base) {
        return None;
    }
    let base_expr = base?;
    let base_poly = Poly::from_expr(&base_expr, var)?;
    if base_poly.degree()? != 2 {
        return None;
    }
    Some((base_expr, base_poly))
}

fn collect_quadratic_sqrt_base(expr: &Expr, var: &str, base: &mut Option<Expr>) -> bool {
    match expr {
        Expr::Pow(base_expr, exp) => {
            if let Some(exp_const) = extract_rational_const(exp) {
                if is_half_integer(&exp_const) && contains_var(base_expr, var) {
                    let norm = normalize((**base_expr).clone());
                    if let Some(existing) = base {
                        if normalize(existing.clone()) != norm {
                            return false;
                        }
                    } else {
                        *base = Some((**base_expr).clone());
                    }
                }
            }
            collect_quadratic_sqrt_base(base_expr, var, base)
                && collect_quadratic_sqrt_base(exp, var, base)
        }
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b) => {
            collect_quadratic_sqrt_base(a, var, base)
                && collect_quadratic_sqrt_base(b, var, base)
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
        | Expr::Abs(inner) => collect_quadratic_sqrt_base(inner, var, base),
        Expr::Variable(_) | Expr::Constant(_) => true,
    }
}

fn rewrite_quadratic_sqrt_expr(
    expr: &Expr,
    base_norm: &Expr,
    sqrt_expr: &Expr,
) -> Option<Expr> {
    if normalize(expr.clone()) == *base_norm {
        return Some(pow_expr(sqrt_expr.clone(), Rational::from_integer(2.into())));
    }

    match expr {
        Expr::Constant(_) | Expr::Variable(_) => Some(expr.clone()),
        Expr::Add(a, b) => Some(Expr::Add(
            rewrite_quadratic_sqrt_expr(a, base_norm, sqrt_expr)?.boxed(),
            rewrite_quadratic_sqrt_expr(b, base_norm, sqrt_expr)?.boxed(),
        )),
        Expr::Sub(a, b) => Some(Expr::Sub(
            rewrite_quadratic_sqrt_expr(a, base_norm, sqrt_expr)?.boxed(),
            rewrite_quadratic_sqrt_expr(b, base_norm, sqrt_expr)?.boxed(),
        )),
        Expr::Mul(a, b) => Some(Expr::Mul(
            rewrite_quadratic_sqrt_expr(a, base_norm, sqrt_expr)?.boxed(),
            rewrite_quadratic_sqrt_expr(b, base_norm, sqrt_expr)?.boxed(),
        )),
        Expr::Div(a, b) => Some(Expr::Div(
            rewrite_quadratic_sqrt_expr(a, base_norm, sqrt_expr)?.boxed(),
            rewrite_quadratic_sqrt_expr(b, base_norm, sqrt_expr)?.boxed(),
        )),
        Expr::Neg(inner) => rewrite_quadratic_sqrt_expr(inner, base_norm, sqrt_expr)
            .map(|res| Expr::Neg(res.boxed())),
        Expr::Pow(base, exp) => {
            let exp_const = extract_rational_const(exp)?;
            let base_norm_inner = normalize((**base).clone());
            if base_norm_inner == *base_norm {
                let scaled = exp_const.clone() * Rational::from_integer(2.into());
                if !scaled.is_integer() {
                    return None;
                }
                return Some(pow_expr(sqrt_expr.clone(), scaled));
            }
            if !exp_const.is_integer() {
                return None;
            }
            let base_replaced = rewrite_quadratic_sqrt_expr(base, base_norm, sqrt_expr)?;
            Some(pow_expr(base_replaced, exp_const))
        }
        _ => None,
    }
}

fn pow_expr(base: Expr, exp: Rational) -> Expr {
    if exp.is_zero() {
        Expr::Constant(Rational::one())
    } else if exp == Rational::one() {
        base
    } else {
        Expr::Pow(base.boxed(), Expr::Constant(exp).boxed())
    }
}

fn extract_integer(exp: &Expr) -> Option<i64> {
    let exp_const = extract_rational_const(exp)?;
    if !exp_const.is_integer() {
        return None;
    }
    exp_const.to_integer().to_i64()
}

fn rationalize_expr(expr: &Expr, var: &str) -> Option<(Expr, Expr)> {
    if !contains_var(expr, var) {
        return Some((expr.clone(), Expr::Constant(Rational::one())));
    }
    match expr {
        Expr::Variable(name) if name == var => Some((
            Expr::Variable(name.clone()),
            Expr::Constant(Rational::one()),
        )),
        Expr::Constant(_) => Some((expr.clone(), Expr::Constant(Rational::one()))),
        Expr::Add(a, b) => {
            let (an, ad) = rationalize_expr(a, var)?;
            let (bn, bd) = rationalize_expr(b, var)?;
            let numer = Expr::Add(
                Expr::Mul(an.boxed(), bd.clone().boxed()).boxed(),
                Expr::Mul(bn.boxed(), ad.clone().boxed()).boxed(),
            );
            let denom = Expr::Mul(ad.boxed(), bd.boxed());
            Some((numer, denom))
        }
        Expr::Sub(a, b) => {
            let (an, ad) = rationalize_expr(a, var)?;
            let (bn, bd) = rationalize_expr(b, var)?;
            let numer = Expr::Sub(
                Expr::Mul(an.boxed(), bd.clone().boxed()).boxed(),
                Expr::Mul(bn.boxed(), ad.clone().boxed()).boxed(),
            );
            let denom = Expr::Mul(ad.boxed(), bd.boxed());
            Some((numer, denom))
        }
        Expr::Mul(a, b) => {
            let (an, ad) = rationalize_expr(a, var)?;
            let (bn, bd) = rationalize_expr(b, var)?;
            let numer = Expr::Mul(an.boxed(), bn.boxed());
            let denom = Expr::Mul(ad.boxed(), bd.boxed());
            Some((numer, denom))
        }
        Expr::Div(a, b) => {
            let (an, ad) = rationalize_expr(a, var)?;
            let (bn, bd) = rationalize_expr(b, var)?;
            let numer = Expr::Mul(an.boxed(), bd.boxed());
            let denom = Expr::Mul(ad.boxed(), bn.boxed());
            Some((numer, denom))
        }
        Expr::Neg(inner) => {
            let (n, d) = rationalize_expr(inner, var)?;
            Some((Expr::Neg(n.boxed()), d))
        }
        Expr::Pow(base, exp) => {
            let power = extract_integer(exp)?;
            if power == 0 {
                return Some((
                    Expr::Constant(Rational::one()),
                    Expr::Constant(Rational::one()),
                ));
            }
            let (n, d) = rationalize_expr(base, var)?;
            let abs_power = power.abs();
            let n_pow = pow_expr(n, Rational::from_integer(abs_power.into()));
            let d_pow = pow_expr(d, Rational::from_integer(abs_power.into()));
            if power >= 0 {
                Some((n_pow, d_pow))
            } else {
                Some((d_pow, n_pow))
            }
        }
        _ => None,
    }
}

fn extract_rational_const(expr: &Expr) -> Option<Rational> {
    match expr {
        Expr::Constant(c) => Some(c.clone()),
        Expr::Neg(inner) => extract_rational_const(inner).map(|c| -c),
        _ => {
            let simplified = simplify_fully(expr.clone());
            match simplified {
                Expr::Constant(c) => Some(c),
                Expr::Neg(inner) => extract_rational_const(&inner).map(|c| -c),
                _ => None,
            }
        }
    }
}

fn is_half_integer(exp: &Rational) -> bool {
    exp.denom() == &BigInt::from(2)
}

fn sqrt_rational_expr(value: &Rational) -> Expr {
    Expr::Pow(
        Expr::Constant(value.clone()).boxed(),
        Expr::Constant(Rational::new(1.into(), 2.into())).boxed(),
    )
}

pub(super) fn substitution_candidates(expr: &Expr, original_expr: &Expr) -> (Expr, Vec<Expr>) {
    let simplified = simplify_fully(expr.clone());
    let mut candidates = Vec::new();
    candidates.push(simplified.clone());
    if simplified != *expr {
        candidates.push(expr.clone());
    }
    if original_expr != expr && original_expr != &simplified {
        candidates.push(original_expr.clone());
    }
    (simplified, candidates)
}

fn integrate_with_respect_to_inner(outer: &Expr, inner: &Expr) -> Option<Expr> {
    match outer {
        Expr::Exp(_) => Some(Expr::Exp(inner.clone().boxed())),
        Expr::Sin(_) => Some(Expr::Neg(Expr::Cos(inner.clone().boxed()).boxed())),
        Expr::Cos(_) => Some(Expr::Sin(inner.clone().boxed())),
        Expr::Tan(_) => Some(Expr::Neg(
            log_abs(Expr::Cos(inner.clone().boxed())).boxed(),
        )),
        Expr::Sec(_) => {
            let sum = Expr::Add(
                Expr::Sec(inner.clone().boxed()).boxed(),
                Expr::Tan(inner.clone().boxed()).boxed(),
            );
            Some(log_abs(sum))
        }
        Expr::Csc(_) => {
            let diff = Expr::Sub(
                Expr::Csc(inner.clone().boxed()).boxed(),
                Expr::Cot(inner.clone().boxed()).boxed(),
            );
            Some(log_abs(diff))
        }
        Expr::Cot(_) => Some(log_abs(Expr::Sin(inner.clone().boxed()))),
        Expr::Sinh(_) => Some(Expr::Cosh(inner.clone().boxed())),
        Expr::Cosh(_) => Some(Expr::Sinh(inner.clone().boxed())),
        Expr::Tanh(_) => Some(log_abs(Expr::Cosh(inner.clone().boxed()))),
        Expr::Asec(_) => {
            let sqrt = Expr::Pow(
                Expr::Sub(
                    Expr::Pow(
                        inner.clone().boxed(),
                        Expr::Constant(Rational::from_integer(2.into())).boxed(),
                    )
                    .boxed(),
                    Expr::Constant(Rational::one()).boxed(),
                )
                .boxed(),
                Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
                    .boxed(),
            );
            let log_term = log_abs(Expr::Add(inner.clone().boxed(), sqrt.boxed()));
            Some(Expr::Sub(
                Expr::Mul(inner.clone().boxed(), Expr::Asec(inner.clone().boxed()).boxed()).boxed(),
                log_term.boxed(),
            ))
        }
        Expr::Acsc(_) => {
            let sqrt = Expr::Pow(
                Expr::Sub(
                    Expr::Pow(
                        inner.clone().boxed(),
                        Expr::Constant(Rational::from_integer(2.into())).boxed(),
                    )
                    .boxed(),
                    Expr::Constant(Rational::one()).boxed(),
                )
                .boxed(),
                Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
                    .boxed(),
            );
            let log_term = log_abs(Expr::Add(inner.clone().boxed(), sqrt.boxed()));
            Some(Expr::Add(
                Expr::Mul(inner.clone().boxed(), Expr::Acsc(inner.clone().boxed()).boxed()).boxed(),
                log_term.boxed(),
            ))
        }
        Expr::Acot(_) => {
            let log_term = log_abs(Expr::Add(
                Expr::Constant(Rational::one()).boxed(),
                Expr::Pow(
                    inner.clone().boxed(),
                    Expr::Constant(Rational::from_integer(2.into())).boxed(),
                )
                .boxed(),
            ));
            Some(Expr::Add(
                Expr::Mul(inner.clone().boxed(), Expr::Acot(inner.clone().boxed()).boxed()).boxed(),
                Expr::Div(
                    log_term.boxed(),
                    Expr::Constant(Rational::from_integer(2.into())).boxed(),
                )
                .boxed(),
            ))
        }
        Expr::Asinh(_) => {
            let sqrt = Expr::Pow(
                Expr::Add(
                    Expr::Pow(
                        inner.clone().boxed(),
                        Expr::Constant(Rational::from_integer(2.into())).boxed(),
                    )
                    .boxed(),
                    Expr::Constant(Rational::one()).boxed(),
                )
                .boxed(),
                Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
                    .boxed(),
            );
            Some(Expr::Sub(
                Expr::Mul(inner.clone().boxed(), Expr::Asinh(inner.clone().boxed()).boxed()).boxed(),
                sqrt.boxed(),
            ))
        }
        Expr::Acosh(_) => {
            let sqrt = Expr::Pow(
                Expr::Sub(
                    Expr::Pow(
                        inner.clone().boxed(),
                        Expr::Constant(Rational::from_integer(2.into())).boxed(),
                    )
                    .boxed(),
                    Expr::Constant(Rational::one()).boxed(),
                )
                .boxed(),
                Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
                    .boxed(),
            );
            Some(Expr::Sub(
                Expr::Mul(inner.clone().boxed(), Expr::Acosh(inner.clone().boxed()).boxed()).boxed(),
                sqrt.boxed(),
            ))
        }
        Expr::Atanh(_) => {
            let log_term = log_abs(Expr::Sub(
                Expr::Constant(Rational::one()).boxed(),
                Expr::Pow(
                    inner.clone().boxed(),
                    Expr::Constant(Rational::from_integer(2.into())).boxed(),
                )
                .boxed(),
            ));
            Some(Expr::Add(
                Expr::Mul(inner.clone().boxed(), Expr::Atanh(inner.clone().boxed()).boxed()).boxed(),
                Expr::Div(
                    log_term.boxed(),
                    Expr::Constant(Rational::from_integer(2.into())).boxed(),
                )
                .boxed(),
            ))
        }
        Expr::Log(_) => Some(Expr::Sub(
            Expr::Mul(
                inner.clone().boxed(),
                log_abs(inner.clone()).boxed(),
            )
            .boxed(),
            inner.clone().boxed(),
        )),
        Expr::Pow(_, exp) => {
            let exponent = match &**exp {
                Expr::Constant(n) => n.clone(),
                Expr::Neg(inner) => match &**inner {
                    Expr::Constant(n) => -n.clone(),
                    _ => return None,
                },
                _ => return None,
            };
            if exponent == -Rational::one() {
                return Some(log_abs(inner.clone()));
            }
            let new_exp = exponent + Rational::one();
            Some(Expr::Div(
                Expr::Pow(
                    inner.clone().boxed(),
                    Expr::Constant(new_exp.clone()).boxed(),
                )
                .boxed(),
                Expr::Constant(new_exp).boxed(),
            ))
        }
        _ => None,
    }
}

fn integrate_function_of_inner(expr: &Expr, var: &str) -> Option<Expr> {
    let mut candidates = collect_subexpr_candidates(expr, var);
    if candidates.is_empty() {
        return None;
    }
    candidates.sort_by(|a, b| expr_size(b).cmp(&expr_size(a)));
    if candidates.len() > SUBSTITUTION_CANDIDATE_LIMIT {
        candidates.truncate(SUBSTITUTION_CANDIDATE_LIMIT);
    }
    let u_name = fresh_var_name(expr, var, "u");
    let u_var = Expr::Variable(u_name.clone());

    for candidate in candidates {
        let deriv = simplify_fully(differentiate(var, &candidate));
        if deriv.is_zero() {
            continue;
        }
        let ratio = simplify_fully(Expr::Div(expr.clone().boxed(), deriv.clone().boxed()));
        let candidate_norm = normalize(candidate.clone());
        if expr_size(&ratio) <= TRANSFORM_SIZE_LIMIT {
            if let Some(result) = try_function_of_inner_ratio(
                &ratio,
                &candidate,
                &candidate_norm,
                &u_name,
                &u_var,
                var,
            ) {
                return Some(result);
            }
        }
        if let Some(factor_ratio) = factor_cancel_ratio(expr, &deriv, var) {
            if expr_size(&factor_ratio) <= TRANSFORM_SIZE_LIMIT {
                if let Some(result) = try_function_of_inner_ratio(
                    &factor_ratio,
                    &candidate,
                    &candidate_norm,
                    &u_name,
                    &u_var,
                    var,
                ) {
                    return Some(result);
                }
            }
            let simplified = simplify_fully(factor_ratio);
            if expr_size(&simplified) <= TRANSFORM_SIZE_LIMIT {
                if let Some(result) = try_function_of_inner_ratio(
                    &simplified,
                    &candidate,
                    &candidate_norm,
                    &u_name,
                    &u_var,
                    var,
                ) {
                    return Some(result);
                }
            }
        }
    }

    None
}

fn try_function_of_inner_ratio(
    ratio: &Expr,
    candidate: &Expr,
    candidate_norm: &Expr,
    u_name: &str,
    u_var: &Expr,
    var: &str,
) -> Option<Expr> {
    if let Some(result) = integrate_in_substitution_var(ratio, candidate, u_name, u_var, var) {
        return Some(result);
    }
    let ratio_norm = normalize(ratio.clone());
    if candidate_norm != candidate || ratio_norm != *ratio {
        if let Some(result) =
            integrate_in_substitution_var(&ratio_norm, candidate_norm, u_name, u_var, var)
        {
            return Some(result);
        }
    }
    None
}

fn integrate_in_substitution_var(
    ratio: &Expr,
    candidate: &Expr,
    u_name: &str,
    u_var: &Expr,
    var: &str,
) -> Option<Expr> {
    if matches!(candidate, Expr::Variable(name) if name == var) {
        return None;
    }
    let replaced = replace_expr(ratio, candidate, u_var);
    if contains_var(&replaced, var) {
        return None;
    }
    if expr_size(&replaced) > TRANSFORM_SIZE_LIMIT {
        return None;
    }
    match integrate(u_name, &replaced) {
        IntegrationResult::Integrated { result, .. } => {
            let restored = substitute(&result, u_name, candidate);
            Some(simplify(restored))
        }
        _ => None,
    }
}

fn factor_cancel_ratio(expr: &Expr, target: &Expr, var: &str) -> Option<Expr> {
    let (expr_const, mut expr_factors) = flatten_product(expr);
    let (target_const, target_factors) = flatten_product(target);
    if target_const.is_zero() {
        return None;
    }

    let ratio_const = expr_const / target_const;
    let mut ratio_factors: Vec<Expr> = Vec::new();
    let mut expr_norms: Vec<Expr> = expr_factors.iter().map(|f| normalize(f.clone())).collect();

    for target_factor in target_factors {
        let target_norm = normalize(target_factor.clone());
        if let Some(idx) = expr_norms.iter().position(|f| *f == target_norm) {
            expr_factors.remove(idx);
            expr_norms.remove(idx);
            continue;
        }
        let mut matched = None;
        for (idx, factor) in expr_factors.iter().enumerate() {
            if let Some(coeff) = constant_ratio(factor, &target_factor, var) {
                if is_constant_wrt(&coeff, var) {
                    matched = Some((idx, coeff));
                    break;
                }
            }
        }
        if let Some((idx, coeff)) = matched {
            expr_factors.remove(idx);
            expr_norms.remove(idx);
            ratio_factors.push(coeff);
        } else {
            return None;
        }
    }

    ratio_factors.append(&mut expr_factors);
    if ratio_const.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }
    if ratio_const.is_one() {
        return Some(rebuild_product(Rational::one(), ratio_factors));
    }
    ratio_factors.insert(0, Expr::Constant(ratio_const));
    Some(rebuild_product(Rational::one(), ratio_factors))
}

fn collect_subexpr_candidates(expr: &Expr, var: &str) -> Vec<Expr> {
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    collect_subexpr_candidates_inner(expr, var, &mut seen, &mut out);
    out
}

fn collect_subexpr_candidates_inner(
    expr: &Expr,
    var: &str,
    seen: &mut HashSet<Expr>,
    out: &mut Vec<Expr>,
) {
    if !contains_var(expr, var) {
        return;
    }
    if !matches!(expr, Expr::Variable(name) if name == var) {
        if seen.insert(expr.clone()) {
            out.push(expr.clone());
        }
    }
    match expr {
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => {
            collect_subexpr_candidates_inner(a, var, seen, out);
            collect_subexpr_candidates_inner(b, var, seen, out);
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
        | Expr::Abs(inner) => {
            collect_subexpr_candidates_inner(inner, var, seen, out);
        }
        Expr::Variable(_) | Expr::Constant(_) => {}
    }
}

fn replace_expr(expr: &Expr, target: &Expr, replacement: &Expr) -> Expr {
    if expr == target {
        return replacement.clone();
    }
    match expr {
        Expr::Add(a, b) => Expr::Add(
            replace_expr(a, target, replacement).boxed(),
            replace_expr(b, target, replacement).boxed(),
        ),
        Expr::Sub(a, b) => Expr::Sub(
            replace_expr(a, target, replacement).boxed(),
            replace_expr(b, target, replacement).boxed(),
        ),
        Expr::Mul(a, b) => Expr::Mul(
            replace_expr(a, target, replacement).boxed(),
            replace_expr(b, target, replacement).boxed(),
        ),
        Expr::Div(a, b) => Expr::Div(
            replace_expr(a, target, replacement).boxed(),
            replace_expr(b, target, replacement).boxed(),
        ),
        Expr::Pow(a, b) => Expr::Pow(
            replace_expr(a, target, replacement).boxed(),
            replace_expr(b, target, replacement).boxed(),
        ),
        Expr::Neg(inner) => Expr::Neg(replace_expr(inner, target, replacement).boxed()),
        Expr::Sin(inner) => Expr::Sin(replace_expr(inner, target, replacement).boxed()),
        Expr::Cos(inner) => Expr::Cos(replace_expr(inner, target, replacement).boxed()),
        Expr::Tan(inner) => Expr::Tan(replace_expr(inner, target, replacement).boxed()),
        Expr::Sec(inner) => Expr::Sec(replace_expr(inner, target, replacement).boxed()),
        Expr::Csc(inner) => Expr::Csc(replace_expr(inner, target, replacement).boxed()),
        Expr::Cot(inner) => Expr::Cot(replace_expr(inner, target, replacement).boxed()),
        Expr::Atan(inner) => Expr::Atan(replace_expr(inner, target, replacement).boxed()),
        Expr::Asin(inner) => Expr::Asin(replace_expr(inner, target, replacement).boxed()),
        Expr::Acos(inner) => Expr::Acos(replace_expr(inner, target, replacement).boxed()),
        Expr::Asec(inner) => Expr::Asec(replace_expr(inner, target, replacement).boxed()),
        Expr::Acsc(inner) => Expr::Acsc(replace_expr(inner, target, replacement).boxed()),
        Expr::Acot(inner) => Expr::Acot(replace_expr(inner, target, replacement).boxed()),
        Expr::Sinh(inner) => Expr::Sinh(replace_expr(inner, target, replacement).boxed()),
        Expr::Cosh(inner) => Expr::Cosh(replace_expr(inner, target, replacement).boxed()),
        Expr::Tanh(inner) => Expr::Tanh(replace_expr(inner, target, replacement).boxed()),
        Expr::Asinh(inner) => Expr::Asinh(replace_expr(inner, target, replacement).boxed()),
        Expr::Acosh(inner) => Expr::Acosh(replace_expr(inner, target, replacement).boxed()),
        Expr::Atanh(inner) => Expr::Atanh(replace_expr(inner, target, replacement).boxed()),
        Expr::Exp(inner) => Expr::Exp(replace_expr(inner, target, replacement).boxed()),
        Expr::Log(inner) => Expr::Log(replace_expr(inner, target, replacement).boxed()),
        Expr::Abs(inner) => Expr::Abs(replace_expr(inner, target, replacement).boxed()),
        Expr::Variable(_) | Expr::Constant(_) => expr.clone(),
    }
}

fn inner_candidate(expr: &Expr) -> Option<&Expr> {
    match expr {
        Expr::Sin(arg)
        | Expr::Cos(arg)
        | Expr::Tan(arg)
        | Expr::Sec(arg)
        | Expr::Csc(arg)
        | Expr::Cot(arg)
        | Expr::Sinh(arg)
        | Expr::Cosh(arg)
        | Expr::Tanh(arg)
        | Expr::Atan(arg)
        | Expr::Asin(arg)
        | Expr::Acos(arg)
        | Expr::Asec(arg)
        | Expr::Acsc(arg)
        | Expr::Acot(arg)
        | Expr::Asinh(arg)
        | Expr::Acosh(arg)
        | Expr::Atanh(arg)
        | Expr::Exp(arg)
        | Expr::Log(arg) => Some(arg),
        Expr::Pow(base, exp) => match &**exp {
            Expr::Constant(_) => Some(base),
            Expr::Neg(inner) if matches!(**inner, Expr::Constant(_)) => Some(base),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod substitution_internal_tests {
    use super::*;
    use crate::core::parser::parse_expr;

    #[test]
    fn detects_basic_u_sub() {
        let expr = parse_expr("2*x*exp(x^2)").unwrap();
        let result = integrate_by_substitution(&expr, "x");
        assert!(matches!(result, Some(Expr::Exp(_))));
    }

    #[test]
    fn detects_composite_power_inner() {
        let expr = parse_expr("4*x*(x^2 + 1)*exp((x^2 + 1)^2)").unwrap();
        let result = integrate_by_substitution(&expr, "x");
        assert!(result.is_some());
    }

    #[test]
    fn detects_affine_inside_exp() {
        let expr = parse_expr("3*(2*x + 1)*exp(x^2 + x)").unwrap();
        let result = integrate_by_substitution(&expr, "x");
        assert!(result.is_some());
    }

    #[test]
    fn detects_negative_power_case() {
        let expr = parse_expr("5*(2*x + 5)*(x^2 + 5*x + 1)^-3").unwrap();
        let result = integrate_by_substitution(&expr, "x");
        assert!(result.is_some());
    }

    #[test]
    fn constant_ratio_for_negative_power() {
        let expr = parse_expr("5*(2*x + 5)*(x^2 + 5*x + 1)^-3").unwrap();
        let (c, factors) = flatten_product(&expr);
        let inner = inner_candidate(&factors[1]).unwrap();
        let inner_derivative = simplify_fully(differentiate("x", inner));
        let remaining = rebuild_product(
            c.clone(),
            factors
                .iter()
                .enumerate()
                .filter_map(|(i, f)| if i == 1 { None } else { Some(f.clone()) })
                .collect(),
        );
        assert!(constant_ratio(&remaining, &inner_derivative, "x").is_some());
    }

    #[test]
    fn integrates_negative_power_case() {
        let expr = parse_expr("5*(2*x + 5)*(x^2 + 5*x + 1)^-3").unwrap();
        let result = super::integrate("x", &expr);
        match result {
            IntegrationResult::Integrated { .. } => {}
            other => panic!("expected integration, got {other:?}"),
        }
    }

    #[test]
    fn constant_ratio_with_parameters() {
        let numerator = parse_expr("2*x + y").unwrap();
        let denom = parse_expr("x^2 + y*x + 1").unwrap();
        let derivative = simplify_fully(differentiate("x", &denom));
        assert!(
            constant_ratio(&numerator, &derivative, "x").is_some(),
            "expected constant ratio with parameter coefficients"
        );
    }

    #[test]
    fn log_derivative_with_parameters() {
        let expr = parse_expr("(2*x + y)/(x^2 + y*x + 1)").unwrap();
        assert!(
            integrate_log_derivative(&expr, "x").is_some(),
            "expected log-derivative integration with parameter coefficients"
        );
    }

    #[test]
    fn constant_detection_simplified_param_expressions() {
        let cases = vec![
            ("exp(x - x + y)", true),
            ("log(x - x + y + 1)", true),
            ("(x - x + 1)*(y + 2)", true),
            ("exp(x + y)", false),
            ("log(x + y + 1)", false),
            ("(x^2 + y)^(1/2)", false),
        ];

        for (input, expected) in cases {
            let expr = parse_expr(input).unwrap();
            assert_eq!(
                is_constant_wrt(&expr, "x"),
                expected,
                "is_constant_wrt for {input}"
            );
        }
    }

    #[test]
    fn constant_ratio_with_exp_parameters() {
        let numerator = parse_expr("exp(y*x)").unwrap();
        let target = parse_expr("exp(y*x)").unwrap();
        let derivative = simplify_fully(differentiate("x", &target));
        let coeff = constant_ratio(&numerator, &derivative, "x")
            .expect("expected constant ratio for exp parameter");
        assert_eq!(
            simplify_fully(coeff),
            simplify_fully(parse_expr("1/y").unwrap())
        );
    }

    #[test]
    fn constant_ratio_with_algebraic_parameters() {
        let numerator = parse_expr("x*(x^2 + y)^(-1/2)").unwrap();
        let target = parse_expr("(x^2 + y)^(1/2)").unwrap();
        let derivative = simplify_fully(differentiate("x", &target));
        let coeff = constant_ratio(&numerator, &derivative, "x")
            .expect("expected constant ratio for algebraic parameter");
        assert_eq!(
            simplify_fully(coeff),
            simplify_fully(parse_expr("1").unwrap())
        );
    }
}
