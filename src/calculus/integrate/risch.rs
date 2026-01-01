use std::collections::{BTreeMap, HashMap, HashSet};

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, ToPrimitive, Zero};

use crate::diff_field::{ExtensionKind, Tower};
use crate::expr::{Expr, Rational};
use crate::polynomial::{Poly, Polynomial};
use crate::simplify::simplify_fully;

use super::{NonElementaryKind, contains_var, polynomial, rational};

type ExprPoly = Polynomial<Expr>;

#[derive(Debug, Clone)]
pub enum RischOutcome {
    Integrated { result: Expr, note: String },
    NonElementary { kind: NonElementaryKind, note: String },
    Indeterminate { note: String },
}

pub fn analyze(expr: &Expr, var: &str) -> RischOutcome {
    let simplified = simplify_fully(expr.clone());
    if let Some(outcome) = analyze_algebraic(&simplified, var) {
        return outcome;
    }
    let tower = match build_tower(expr, var) {
        Ok(tower) => tower,
        Err(note) => {
            return RischOutcome::Indeterminate {
                note: format!("tower: {note}"),
            };
        }
    };

    if tower.extensions().is_empty() {
        return RischOutcome::Indeterminate {
            note: "no transcendental generators".to_string(),
        };
    }

    integrate_top_extension(expr, var, &tower).unwrap_or_else(|| RischOutcome::Indeterminate {
        note: "no applicable risch reduction".to_string(),
    })
}

fn analyze_algebraic(expr: &Expr, var: &str) -> Option<RischOutcome> {
    let base = find_sqrt_base(expr, var)?;
    let base_poly = Poly::from_expr(&base, var)?;
    let degree = base_poly.degree().unwrap_or(0);
    if degree <= 1 {
        return None;
    }
    if degree > 2 {
        return Some(RischOutcome::NonElementary {
            kind: NonElementaryKind::SpecialFunctionNeeded,
            note: "algebraic sqrt degree > 2".to_string(),
        });
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

fn integrate_top_extension(expr: &Expr, var: &str, tower: &Tower) -> Option<RischOutcome> {
    let extension = tower.extensions().last()?;
    let expr_sym = tower.replace_generators(expr);

    match extension.kind {
        ExtensionKind::Exp => integrate_exp_extension(&expr_sym, var, tower),
        ExtensionKind::Log => integrate_log_extension(&expr_sym, var, tower),
    }
}

fn integrate_exp_extension(expr_sym: &Expr, var: &str, tower: &Tower) -> Option<RischOutcome> {
    let t_symbol = tower.top_symbol();
    let lower_symbols = lower_symbol_set(tower);
    let t_deriv = tower.top_derivative_expr();
    let a_expr = exp_derivative_coeff(&t_deriv, t_symbol)?;

    if is_constant_wrt_base(&a_expr, var, &lower_symbols) {
        if let Some(result) = integrate_by_symbol_substitution(expr_sym, var, t_symbol, &t_deriv, &lower_symbols) {
            let restored = tower.expand_symbols(&result);
            return Some(RischOutcome::Integrated {
                result: simplify_fully(restored),
                note: "risch exp substitution".to_string(),
            });
        }
    }

    let p_expr = extract_linear_exp_coeff(expr_sym, t_symbol)?;
    if contains_var(&p_expr, t_symbol) {
        return None;
    }

    if let Some(solution) = solve_exp_ode_polynomial(&a_expr, &p_expr, var) {
        let result_sym = Expr::Mul(solution.boxed(), Expr::Variable(t_symbol.to_string()).boxed());
        let restored = tower.expand_symbols(&result_sym);
        return Some(RischOutcome::Integrated {
            result: simplify_fully(restored),
            note: "risch exp reduction".to_string(),
        });
    }

    if let Some(kind) = exp_non_elementary_kind(tower, var) {
        return Some(RischOutcome::NonElementary {
            kind,
            note: "risch exp reduction (no polynomial solution)".to_string(),
        });
    }

    None
}

fn integrate_log_extension(expr_sym: &Expr, var: &str, tower: &Tower) -> Option<RischOutcome> {
    let t_symbol = tower.top_symbol();
    let lower_symbols = lower_symbol_set(tower);
    let t_deriv = tower.top_derivative_expr();
    let result = integrate_by_symbol_substitution(expr_sym, var, t_symbol, &t_deriv, &lower_symbols)?;
    let restored = tower.expand_symbols(&result);
    Some(RischOutcome::Integrated {
        result: simplify_fully(restored),
        note: "risch log substitution".to_string(),
    })
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
    let (const_factor, factors) = super::flatten_product(expr);
    if const_factor.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let base_norm = simplify_fully(base_expr.clone());
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

    let rest_expr = super::rebuild_product(const_factor, rest_factors);
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

fn extract_base_powers(
    factor: &Expr,
    base: &Expr,
) -> Result<Option<(i64, i64)>, ()> {
    if factor == base {
        return Ok(Some((1, 0)));
    }
    if let Expr::Pow(inner, exp) = factor {
        let inner_norm = simplify_fully((**inner).clone());
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
    let u2_plus_d = Expr::Add(u_sq.boxed(), Expr::Constant(d.clone()).boxed());
    let sqrt_expr = Expr::Pow(
        u2_plus_d.boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
            .boxed(),
    );

    let max_deg = shifted.degree().unwrap_or(0);
    let mut integrals: Vec<Expr> = Vec::with_capacity(max_deg + 1);
    integrals.push(super::log_abs(Expr::Add(
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
    let log_expr = super::log_abs(Expr::Add(
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
            super::log_abs(ctx.u_expr.clone())
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

fn pow_expr_signed(base: &Expr, exp: i64) -> Expr {
    if exp == 0 {
        Expr::Constant(Rational::one())
    } else {
        Expr::Pow(
            base.clone().boxed(),
            Expr::Constant(Rational::from_integer(BigInt::from(exp))).boxed(),
        )
    }
}

fn is_half_integer(exp: &Rational) -> bool {
    exp.denom() == &BigInt::from(2)
}

fn integrate_by_symbol_substitution(
    expr_sym: &Expr,
    var: &str,
    t_symbol: &str,
    t_deriv: &Expr,
    lower_symbols: &HashSet<String>,
) -> Option<Expr> {
    let ratio = simplify_fully(Expr::Div(expr_sym.clone().boxed(), t_deriv.clone().boxed()));
    if contains_var(&ratio, var) || contains_any_symbol(&ratio, lower_symbols) {
        return None;
    }

    polynomial::integrate(&ratio, t_symbol)
        .or_else(|| rational::integrate(&ratio, t_symbol))
}

fn exp_derivative_coeff(t_deriv: &Expr, t_symbol: &str) -> Option<Expr> {
    let poly = ExprPoly::from_expr(t_deriv, t_symbol)?;
    if poly.degree()? != 1 {
        return None;
    }
    let constant = poly.coeff(0);
    if !constant.is_zero() {
        return None;
    }
    let coeff = poly.coeff(1);
    if contains_var(&coeff, t_symbol) {
        return None;
    }
    Some(coeff)
}

fn extract_linear_exp_coeff(expr_sym: &Expr, t_symbol: &str) -> Option<Expr> {
    let (numer_expr, denom_expr) = split_rational_expr(expr_sym);
    let numer_poly = ExprPoly::from_expr(&numer_expr, t_symbol)?;
    let denom_poly = ExprPoly::from_expr(&denom_expr, t_symbol)?;

    if denom_poly.degree().unwrap_or(0) != 0 {
        return None;
    }
    let denom_coeff = denom_poly.coeff(0);
    if denom_coeff.is_zero() {
        return None;
    }

    let mut seen = false;
    for (exp, coeff) in numer_poly.coeff_entries() {
        if exp == 1 {
            if !coeff.is_zero() {
                seen = true;
            }
            continue;
        }
        if !coeff.is_zero() {
            return None;
        }
    }
    if !seen {
        return None;
    }
    let coeff = numer_poly.coeff(1);
    let scaled = simplify_fully(Expr::Div(coeff.boxed(), denom_coeff.boxed()));
    Some(scaled)
}

fn solve_exp_ode_polynomial(a_expr: &Expr, p_expr: &Expr, var: &str) -> Option<Expr> {
    let a_poly = Poly::from_expr(a_expr, var)?;
    let p_poly = Poly::from_expr(p_expr, var)?;
    let solution = solve_linear_poly_ode(&a_poly, &p_poly)?;
    Some(solution.to_expr(var))
}

fn solve_linear_poly_ode(a: &Poly, p: &Poly) -> Option<Poly> {
    if a.is_zero() {
        return Some(poly_integral(p));
    }

    let a_deg = a.degree().unwrap_or(0);
    let a_lc = a.leading_coeff();
    let mut remainder = p.clone();
    let mut solution = Poly::zero();

    while let Some(r_deg) = remainder.degree() {
        if r_deg < a_deg {
            break;
        }
        let shift = r_deg - a_deg;
        let coeff = remainder.leading_coeff() / a_lc.clone();
        let term = poly_monomial(coeff, shift);
        solution = solution + term.clone();
        let contrib = a.clone() * term.clone() + term.derivative();
        remainder = remainder - contrib;
    }

    if remainder.is_zero() {
        Some(solution)
    } else {
        None
    }
}

fn poly_integral(poly: &Poly) -> Poly {
    let mut coeffs = BTreeMap::new();
    for (exp, coeff) in poly.coeff_entries() {
        let denom = Rational::from_integer(BigInt::from(exp as i64 + 1));
        coeffs.insert(exp + 1, coeff / denom);
    }
    Poly { coeffs }
}

fn poly_monomial(coeff: Rational, exp: usize) -> Poly {
    if coeff.is_zero() {
        return Poly::zero();
    }
    let mut coeffs = BTreeMap::new();
    coeffs.insert(exp, coeff);
    Poly { coeffs }
}

fn exp_non_elementary_kind(tower: &Tower, var: &str) -> Option<NonElementaryKind> {
    let extension = tower.extensions().last()?;
    let Expr::Exp(arg) = &extension.generator else {
        return None;
    };
    let deg = polynomial::degree(arg, var)?;
    if deg > 1 {
        Some(NonElementaryKind::ExpOfPolynomial)
    } else {
        None
    }
}

fn lower_symbol_set(tower: &Tower) -> HashSet<String> {
    let mut symbols: Vec<String> = tower.extensions().iter().map(|ext| ext.symbol.clone()).collect();
    if !symbols.is_empty() {
        symbols.pop();
    }
    symbols.into_iter().collect()
}

fn is_constant_wrt_base(expr: &Expr, var: &str, symbols: &HashSet<String>) -> bool {
    !contains_var(expr, var) && !contains_any_symbol(expr, symbols)
}

fn contains_any_symbol(expr: &Expr, symbols: &HashSet<String>) -> bool {
    match expr {
        Expr::Variable(name) => symbols.contains(name),
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => contains_any_symbol(a, symbols) || contains_any_symbol(b, symbols),
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
        | Expr::Abs(inner) => contains_any_symbol(inner, symbols),
        Expr::Constant(_) => false,
    }
}

fn split_rational_expr(expr: &Expr) -> (Expr, Expr) {
    let (const_factor, factors) = super::flatten_product(expr);
    if const_factor.is_zero() {
        return (
            Expr::Constant(Rational::zero()),
            Expr::Constant(Rational::one()),
        );
    }

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
                _ => num_factors.push(Expr::Pow(base.clone(), exp.clone())),
            },
            other => num_factors.push(other),
        }
    }

    let numerator = super::rebuild_product(const_factor, num_factors);
    let denominator = if den_factors.is_empty() {
        Expr::Constant(Rational::one())
    } else {
        super::rebuild_product(Rational::one(), den_factors)
    };

    (numerator, denominator)
}

fn build_tower(expr: &Expr, var: &str) -> Result<Tower, String> {
    let mut generators = HashSet::new();
    let mut saw_abs_log = false;
    collect_generators(expr, var, &mut generators, &mut saw_abs_log);
    if saw_abs_log {
        return Err("log(abs(..)) not supported".to_string());
    }

    if generators.is_empty() {
        return Ok(Tower::new(var));
    }

    let mut gens_vec: Vec<Expr> = generators.into_iter().collect();
    gens_vec.sort();

    let mut deps: HashMap<Expr, Vec<Expr>> = HashMap::new();
    for gen_expr in &gens_vec {
        let arg = match gen_expr {
            Expr::Exp(inner) | Expr::Log(inner) => inner.as_ref(),
            _ => continue,
        };
        let mut dep_list = Vec::new();
        for other in &gens_vec {
            if other == gen_expr {
                continue;
            }
            if contains_subexpr(arg, other) {
                dep_list.push(other.clone());
            }
        }
        deps.insert(gen_expr.clone(), dep_list);
    }

    let mut ordered = Vec::new();
    let mut remaining = gens_vec.clone();
    while !remaining.is_empty() {
        let mut next_index = None;
        for (idx, gen_expr) in remaining.iter().enumerate() {
            let ready = deps
                .get(gen_expr)
                .map(|items| items.iter().all(|dep| ordered.contains(dep)))
                .unwrap_or(true);
            if ready {
                next_index = Some(idx);
                break;
            }
        }
        let Some(idx) = next_index else {
            return Err("cyclic generator dependencies".to_string());
        };
        ordered.push(remaining.remove(idx));
    }

    let mut tower = Tower::new(var);
    for gen_expr in ordered {
        match gen_expr {
            Expr::Exp(inner) => {
                tower
                    .push_exp((*inner).clone())
                    .map_err(|err| err.to_string())?;
            }
            Expr::Log(inner) => match &*inner {
                Expr::Abs(_) => return Err("log(abs(..)) not supported".to_string()),
                _ => {
                    tower
                        .push_log((*inner).clone())
                        .map_err(|err| err.to_string())?;
                }
            },
            _ => {}
        }
    }

    Ok(tower)
}

fn collect_generators(expr: &Expr, var: &str, out: &mut HashSet<Expr>, saw_abs_log: &mut bool) {
    match expr {
        Expr::Exp(inner) => {
            if contains_var(inner, var) {
                out.insert(expr.clone());
            }
            collect_generators(inner, var, out, saw_abs_log);
        }
        Expr::Log(inner) => {
            if matches!(&**inner, Expr::Abs(_)) {
                *saw_abs_log = true;
            }
            if contains_var(inner, var) {
                out.insert(expr.clone());
            }
            collect_generators(inner, var, out, saw_abs_log);
        }
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => {
            collect_generators(a, var, out, saw_abs_log);
            collect_generators(b, var, out, saw_abs_log);
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
        | Expr::Abs(inner) => {
            collect_generators(inner, var, out, saw_abs_log);
        }
        Expr::Variable(_) | Expr::Constant(_) => {}
    }
}

fn contains_subexpr(expr: &Expr, target: &Expr) -> bool {
    if expr == target {
        return true;
    }
    match expr {
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => contains_subexpr(a, target) || contains_subexpr(b, target),
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
        | Expr::Abs(inner) => contains_subexpr(inner, target),
        Expr::Variable(_) | Expr::Constant(_) => false,
    }
}
