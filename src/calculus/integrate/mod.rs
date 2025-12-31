mod common;
mod exponential;
mod logarithmic;
mod polynomial;
mod rational;
mod trig;

use crate::calculus::differentiate;
use crate::expr::{Expr, Rational};
use crate::format::expr::pretty;
use crate::simplify::{simplify, simplify_fully};
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::collections::HashMap;
use std::f64::consts::PI;

pub(crate) use common::{coeff_of_var, linear_parts};
pub use exponential::is_exp;
pub use logarithmic::is_log;
pub use polynomial::is_polynomial;
pub use rational::is_rational;
pub use trig::is_trig;

const TRANSFORM_SIZE_LIMIT: usize = 96;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntegrandKind {
    Polynomial,
    Rational { linear: bool },
    Trig,
    Exponential,
    Logarithmic,
    Product(Box<IntegrandKind>, Box<IntegrandKind>),
    Sum,
    NonElementary(NonElementaryKind),
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NonElementaryKind {
    ExpOfPolynomial,
    TrigOverArgument,
    SpecialFunctionNeeded,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReasonCode {
    NonRational,
    NonPolynomialTrig,
    NonElementary(NonElementaryKind),
    UnknownStructure,
    SizeLimit(usize),
    StrategyNotAvailable(&'static str),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Strategy {
    Direct,
    Substitution,
    IntegrationByParts,
    PartialFractions,
    RischLite,
    MeijerG,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttemptStatus {
    Succeeded,
    NotApplicable,
    Failed(ReasonCode),
    HitLimit { size: usize, limit: usize },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegrationAttempt {
    pub strategy: Strategy,
    pub status: AttemptStatus,
    pub note: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegrandReport {
    pub kind: IntegrandKind,
    pub reason: Option<ReasonCode>,
    pub attempts: Vec<IntegrationAttempt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntegrationResult {
    Integrated {
        result: Expr,
        report: IntegrandReport,
    },
    NotIntegrable(IntegrandReport),
}

pub fn integrate(var: &str, expr: &Expr) -> IntegrationResult {
    let mut attempts = Vec::new();
    let mut kind = classify_integrand(expr, var);

    // If the chosen variable does not occur, treat the expression as a constant.
    if !contains_var(expr, var) {
        let result = simplify(Expr::Mul(
            expr.clone().boxed(),
            Expr::Variable(var.to_string()).boxed(),
        ));
        attempts.push(IntegrationAttempt {
            strategy: Strategy::Direct,
            status: AttemptStatus::Succeeded,
            note: None,
        });
        return IntegrationResult::Integrated {
            result,
            report: IntegrandReport {
                kind,
                reason: None,
                attempts,
            },
        };
    }

    if let Some(non_elem) = detect_non_elementary(expr) {
        kind = IntegrandKind::NonElementary(non_elem.clone());
        let report = IntegrandReport {
            kind,
            reason: Some(ReasonCode::NonElementary(non_elem)),
            attempts,
        };
        return IntegrationResult::NotIntegrable(report);
    }

    if let Some(result) = integrate_direct(expr, var) {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::Direct,
            status: AttemptStatus::Succeeded,
            note: None,
        });
        return IntegrationResult::Integrated {
            result: simplify(result),
            report: IntegrandReport {
                kind,
                reason: None,
                attempts,
            },
        };
    }

    attempts.push(IntegrationAttempt {
        strategy: Strategy::Direct,
        status: AttemptStatus::Failed(default_reason(&kind)),
        note: None,
    });

    let size = expr_size(expr);
    let simplified_for_sub = simplify_fully(expr.clone());
    let sub_size = expr_size(&simplified_for_sub);

    // Substitution heuristics (u-sub, f'/f).
    if sub_size > TRANSFORM_SIZE_LIMIT {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::Substitution,
            status: AttemptStatus::HitLimit {
                size: sub_size,
                limit: TRANSFORM_SIZE_LIMIT,
            },
            note: None,
        });
    } else {
        let mut sub_result = None;
        for candidate in [&simplified_for_sub, expr] {
            if let Some(result) = integrate_by_substitution(candidate, var) {
                sub_result = Some(result);
                break;
            }
        }

        if let Some(result) = sub_result {
            attempts.push(IntegrationAttempt {
                strategy: Strategy::Substitution,
                status: AttemptStatus::Succeeded,
                note: None,
            });
            return IntegrationResult::Integrated {
                result: simplify(result),
                report: IntegrandReport {
                    kind,
                    reason: None,
                    attempts,
                },
            };
        } else {
            attempts.push(IntegrationAttempt {
                strategy: Strategy::Substitution,
                status: AttemptStatus::NotApplicable,
                note: None,
            });
        }
    }

    // Integration by parts for polynomial * trig/exp/log forms.
    if size > TRANSFORM_SIZE_LIMIT {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::IntegrationByParts,
            status: AttemptStatus::HitLimit {
                size,
                limit: TRANSFORM_SIZE_LIMIT,
            },
            note: None,
        });
    } else if let Some((result, note)) = integration_by_parts(expr, var) {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::IntegrationByParts,
            status: AttemptStatus::Succeeded,
            note: Some(note),
        });
        return IntegrationResult::Integrated {
            result: simplify(result),
            report: IntegrandReport {
                kind,
                reason: None,
                attempts,
            },
        };
    } else {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::IntegrationByParts,
            status: AttemptStatus::NotApplicable,
            note: None,
        });
    }

    // Partial fractions (only if rational).
    if size > TRANSFORM_SIZE_LIMIT {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::PartialFractions,
            status: AttemptStatus::HitLimit {
                size,
                limit: TRANSFORM_SIZE_LIMIT,
            },
            note: None,
        });
    } else if let Some(result) = integrate_partial_fractions(expr, var) {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::PartialFractions,
            status: AttemptStatus::Succeeded,
            note: None,
        });
        return IntegrationResult::Integrated {
            result: simplify(result),
            report: IntegrandReport {
                kind,
                reason: None,
                attempts,
            },
        };
    } else {
        let status = if rational::is_rational(expr, var) || is_rational_like(expr, var) {
            AttemptStatus::Failed(ReasonCode::NonRational)
        } else {
            AttemptStatus::NotApplicable
        };
        attempts.push(IntegrationAttempt {
            strategy: Strategy::PartialFractions,
            status,
            note: None,
        });
    }

    // Future hooks.
    attempts.push(IntegrationAttempt {
        strategy: Strategy::RischLite,
        status: AttemptStatus::Failed(ReasonCode::StrategyNotAvailable("risch-lite")),
        note: None,
    });
    attempts.push(IntegrationAttempt {
        strategy: Strategy::MeijerG,
        status: AttemptStatus::Failed(ReasonCode::StrategyNotAvailable("meijer-g expansion")),
        note: None,
    });

    let reason = Some(default_reason(&kind));
    IntegrationResult::NotIntegrable(IntegrandReport {
        kind,
        reason,
        attempts,
    })
}

fn integrate_direct(expr: &Expr, var: &str) -> Option<Expr> {
    if !contains_var(expr, var) {
        let with_var = Expr::Mul(
            expr.clone().boxed(),
            Expr::Variable(var.to_string()).boxed(),
        );
        return Some(with_var);
    }
    let (const_factor, factors) = flatten_product(expr);
    let has_var_reciprocal = factors.iter().any(|f| {
        if let Expr::Pow(base, exp) = f {
            if let Expr::Constant(e) = &**exp {
                if e.is_negative() && contains_var(base, var) {
                    return true;
                }
            }
        }
        false
    });
    if !const_factor.is_one() && !const_factor.is_zero() && !has_var_reciprocal {
        let rest = rebuild_product(Rational::one(), factors.clone());
        if let Some(result) = integrate_direct(&rest, var) {
            return Some(Expr::Mul(
                Expr::Constant(const_factor).boxed(),
                result.boxed(),
            ));
        }
    }
    match expr {
        Expr::Add(a, b) => Some(Expr::Add(
            integrate_direct(a, var)?.boxed(),
            integrate_direct(b, var)?.boxed(),
        )),
        Expr::Sub(a, b) => Some(Expr::Sub(
            integrate_direct(a, var)?.boxed(),
            integrate_direct(b, var)?.boxed(),
        )),
        Expr::Neg(inner) => integrate_direct(inner, var).map(|r| Expr::Neg(r.boxed())),
        Expr::Div(num, den) => match (&**num, &**den) {
            (other, Expr::Constant(c)) => integrate_direct(other, var).map(|r| {
                Expr::Div(r.boxed(), Expr::Constant(c.clone()).boxed())
            }),
            _ => polynomial::integrate(expr, var)
                .or_else(|| rational::integrate(expr, var))
                .or_else(|| trig::integrate(expr, var))
                .or_else(|| exponential::integrate(expr, var))
                .or_else(|| logarithmic::integrate(expr, var)),
        },
        Expr::Mul(a, b) => match (&**a, &**b) {
            (Expr::Constant(c), other) | (other, Expr::Constant(c)) => integrate_direct(other, var)
                .map(|r| Expr::Mul(Expr::Constant(c.clone()).boxed(), r.boxed())),
            _ => polynomial::integrate(expr, var)
                .or_else(|| rational::integrate(expr, var))
                .or_else(|| trig::integrate(expr, var))
                .or_else(|| exponential::integrate(expr, var))
                .or_else(|| logarithmic::integrate(expr, var)),
        },
        _ => polynomial::integrate(expr, var)
            .or_else(|| rational::integrate(expr, var))
            .or_else(|| trig::integrate(expr, var))
            .or_else(|| exponential::integrate(expr, var))
            .or_else(|| logarithmic::integrate(expr, var)),
    }
}

fn integrate_basic(expr: &Expr, var: &str) -> Option<Expr> {
    if !contains_var(expr, var) {
        return Some(Expr::Mul(
            expr.clone().boxed(),
            Expr::Variable(var.to_string()).boxed(),
        ));
    }
    let (const_factor, factors) = flatten_product(expr);
    let has_var_reciprocal = factors.iter().any(|f| {
        if let Expr::Pow(base, exp) = f {
            if let Expr::Constant(e) = &**exp {
                if e.is_negative() && contains_var(base, var) {
                    return true;
                }
            }
        }
        false
    });
    if !const_factor.is_one() && !const_factor.is_zero() && !has_var_reciprocal {
        let rest = rebuild_product(Rational::one(), factors.clone());
        if let Some(result) = integrate_basic(&rest, var) {
            return Some(Expr::Mul(
                Expr::Constant(const_factor).boxed(),
                result.boxed(),
            ));
        }
    }
    match expr {
        Expr::Add(a, b) => Some(Expr::Add(
            integrate_basic(a, var)?.boxed(),
            integrate_basic(b, var)?.boxed(),
        )),
        Expr::Sub(a, b) => Some(Expr::Sub(
            integrate_basic(a, var)?.boxed(),
            integrate_basic(b, var)?.boxed(),
        )),
        Expr::Neg(inner) => integrate_basic(inner, var).map(|r| Expr::Neg(r.boxed())),
        Expr::Div(num, den) => match (&**num, &**den) {
            (other, Expr::Constant(c)) => integrate_basic(other, var).map(|r| {
                Expr::Div(r.boxed(), Expr::Constant(c.clone()).boxed())
            }),
            _ => polynomial::integrate(expr, var)
                .or_else(|| rational::integrate(expr, var))
                .or_else(|| trig::integrate(expr, var))
                .or_else(|| exponential::integrate(expr, var))
                .or_else(|| logarithmic::integrate(expr, var)),
        },
        Expr::Mul(a, b) => match (&**a, &**b) {
            (Expr::Constant(c), other) | (other, Expr::Constant(c)) => integrate_basic(other, var)
                .map(|r| Expr::Mul(Expr::Constant(c.clone()).boxed(), r.boxed())),
            _ => polynomial::integrate(expr, var)
                .or_else(|| rational::integrate(expr, var))
                .or_else(|| trig::integrate(expr, var))
                .or_else(|| exponential::integrate(expr, var))
                .or_else(|| logarithmic::integrate(expr, var)),
        },
        _ => polynomial::integrate(expr, var)
            .or_else(|| rational::integrate(expr, var))
            .or_else(|| trig::integrate(expr, var))
            .or_else(|| exponential::integrate(expr, var))
            .or_else(|| logarithmic::integrate(expr, var)),
    }
}

fn integrate_by_substitution(expr: &Expr, var: &str) -> Option<Expr> {
    let (const_factor, factors) = flatten_product(expr);
    if const_factor.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
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
        let remaining_expr = rebuild_product(const_factor.clone(), remaining.clone());
        if let Some(k) = constant_ratio(&remaining_expr, &inner_derivative, var) {
            if let Some(inner_result) = integrate_with_respect_to_inner(factor, inner) {
                return Some(simplify(Expr::Mul(
                    Expr::Constant(k).boxed(),
                    inner_result.boxed(),
                )));
            }
        }
    }

    None
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum LiateRank {
    Log,
    InverseTrig,
    Algebraic,
    Trig,
    Exponential,
}

fn factor_rank(expr: &Expr, var: &str) -> Option<LiateRank> {
    match expr {
        Expr::Log(_) => Some(LiateRank::Log),
        Expr::Atan(_) | Expr::Asin(_) | Expr::Acos(_) => Some(LiateRank::InverseTrig),
        e if polynomial::is_polynomial(e, var) => Some(LiateRank::Algebraic),
        Expr::Sin(_) | Expr::Cos(_) | Expr::Tan(_) => Some(LiateRank::Trig),
        Expr::Exp(_) => Some(LiateRank::Exponential),
        Expr::Pow(base, _) => factor_rank(base, var),
        _ => None,
    }
}

fn integrate_with_respect_to_inner(outer: &Expr, inner: &Expr) -> Option<Expr> {
    match outer {
        Expr::Exp(_) => Some(Expr::Exp(inner.clone().boxed())),
        Expr::Sin(_) => Some(Expr::Neg(Expr::Cos(inner.clone().boxed()).boxed())),
        Expr::Cos(_) => Some(Expr::Sin(inner.clone().boxed())),
        Expr::Tan(_) => Some(Expr::Neg(
            log_abs(Expr::Cos(inner.clone().boxed())).boxed(),
        )),
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

fn constant_ratio(expr: &Expr, target: &Expr, var: &str) -> Option<Rational> {
    if expr == target {
        return Some(Rational::one());
    }
    if let Expr::Mul(a, b) = expr {
        match (&**a, &**b) {
            (Expr::Constant(c), other) if other == target => return Some(c.clone()),
            (other, Expr::Constant(c)) if other == target => return Some(c.clone()),
            _ => {}
        }
    }
    let quotient = simplify_fully(Expr::Div(expr.clone().boxed(), target.clone().boxed()));
    if let Expr::Constant(k) = quotient {
        return Some(k);
    }
    if !contains_var(&quotient, var) {
        if let Expr::Constant(k) = simplify_fully(quotient.clone()) {
            return Some(k);
        }
    }
    numeric_constant_ratio(expr, target, var)
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

fn combine_var_powers(
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
    let (combined_const, combined_factors) =
        combine_var_powers(c_base * c_term, f_base, var);
    let rebuilt = rebuild_product(combined_const, combined_factors.clone());
    let simplified = simplify_fully(rebuilt.clone());
    if expr_size(&simplified) <= expr_size(&rebuilt) {
        simplified
    } else {
        rebuilt
    }
}

fn distribute_product_with_addition(
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

fn to_rational_candidate(constant: Rational, factors: &[Expr]) -> Option<Expr> {
    let mut num_factors = Vec::new();
    let mut den_factors = Vec::new();

    for f in factors {
        match f {
            Expr::Pow(base, exp) => match &**exp {
                Expr::Constant(k) if k < &Rational::zero() => {
                    den_factors.push(Expr::Pow(
                        base.clone().boxed(),
                        Expr::Constant(-k.clone()).boxed(),
                    ));
                }
                Expr::Neg(inner) => {
                    if let Expr::Constant(k) = &**inner {
                        den_factors.push(Expr::Pow(
                            base.clone().boxed(),
                            Expr::Constant(k.clone()).boxed(),
                        ));
                    } else {
                        num_factors.push(f.clone());
                    }
                }
                _ => num_factors.push(f.clone()),
            },
            _ => num_factors.push(f.clone()),
        }
    }

    if den_factors.is_empty() {
        return None;
    }

    let numerator = rebuild_product(constant, num_factors);
    let denominator = rebuild_product(Rational::one(), den_factors);
    Some(Expr::Div(numerator.boxed(), denominator.boxed()))
}

fn inner_candidate(expr: &Expr) -> Option<&Expr> {
    match expr {
        Expr::Sin(arg) | Expr::Cos(arg) | Expr::Tan(arg) | Expr::Exp(arg) | Expr::Log(arg) => {
            Some(arg)
        }
        Expr::Pow(base, exp) => match &**exp {
            Expr::Constant(_) => Some(base),
            Expr::Neg(inner) if matches!(**inner, Expr::Constant(_)) => Some(base),
            _ => None,
        },
        _ => None,
    }
}

fn eval_expr_numeric(expr: &Expr, var: &str, x: f64) -> Option<f64> {
    match expr {
        Expr::Constant(c) => c.to_f64(),
        Expr::Variable(v) => {
            if v == var {
                Some(x)
            } else {
                Some(1.0)
            }
        }
        Expr::Add(a, b) => Some(eval_expr_numeric(a, var, x)? + eval_expr_numeric(b, var, x)?),
        Expr::Sub(a, b) => Some(eval_expr_numeric(a, var, x)? - eval_expr_numeric(b, var, x)?),
        Expr::Mul(a, b) => Some(eval_expr_numeric(a, var, x)? * eval_expr_numeric(b, var, x)?),
        Expr::Div(a, b) => {
            let denom = eval_expr_numeric(b, var, x)?;
            if denom.abs() < 1e-9 {
                None
            } else {
                Some(eval_expr_numeric(a, var, x)? / denom)
            }
        }
        Expr::Pow(base, exp) => {
            let b = eval_expr_numeric(base, var, x)?;
            match &**exp {
                Expr::Constant(c) => Some(b.powf(c.to_f64()?)),
                _ => None,
            }
        }
        Expr::Neg(inner) => eval_expr_numeric(inner, var, x).map(|v| -v),
        Expr::Sin(inner) => eval_expr_numeric(inner, var, x).map(f64::sin),
        Expr::Cos(inner) => eval_expr_numeric(inner, var, x).map(f64::cos),
        Expr::Tan(inner) => eval_expr_numeric(inner, var, x).map(f64::tan),
        Expr::Atan(inner) => eval_expr_numeric(inner, var, x).map(f64::atan),
        Expr::Asin(inner) => eval_expr_numeric(inner, var, x).map(f64::asin),
        Expr::Acos(inner) => eval_expr_numeric(inner, var, x).map(f64::acos),
        Expr::Exp(inner) => eval_expr_numeric(inner, var, x).map(f64::exp),
        Expr::Log(inner) => {
            let v = eval_expr_numeric(inner, var, x)?;
            if v.abs() < 1e-9 {
                None
            } else {
                Some(v.abs().ln())
            }
        }
        Expr::Abs(inner) => eval_expr_numeric(inner, var, x).map(f64::abs),
    }
}

fn numeric_constant_ratio(expr: &Expr, target: &Expr, var: &str) -> Option<Rational> {
    let samples = [-2.5, -1.0, -0.5, 0.5, 1.0, 2.0, PI / 3.0];
    let mut ratio: Option<f64> = None;
    for s in samples {
        let t_val = eval_expr_numeric(target, var, s)?;
        if t_val.abs() < 1e-9 {
            continue;
        }
        let e_val = eval_expr_numeric(expr, var, s)?;
        let r = e_val / t_val;
        if let Some(prev) = ratio {
            if (r - prev).abs() > 1e-6 {
                return None;
            }
        } else {
            ratio = Some(r);
        }
    }

    ratio.and_then(approximate_rational)
}

fn approximate_rational(val: f64) -> Option<Rational> {
    if !val.is_finite() {
        return None;
    }
    let max_den: i64 = 512;
    for den in 1..=max_den {
        let num = (val * den as f64).round();
        let approx = Rational::new(BigInt::from(num as i64), BigInt::from(den));
        if (approx.to_f64()? - val).abs() < 1e-9 {
            return Some(approx);
        }
    }
    Rational::from_float(val)
}

#[cfg(test)]
mod substitution_internal_tests {
    use super::*;
    use crate::parser::parse_expr;

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
}

fn integration_by_parts(expr: &Expr, var: &str) -> Option<(Expr, String)> {
    let mut memo = HashMap::new();
    integrate_by_parts_recursive(expr, var, &mut memo)
}

fn integrate_by_parts_recursive(
    expr: &Expr,
    var: &str,
    memo: &mut HashMap<Expr, Option<Expr>>,
) -> Option<(Expr, String)> {
    if let Some(result) = memo.get(expr) {
        return result.clone().map(|r| (r, String::new()));
    }

    let (const_factor, factors) = flatten_product(expr);
    if factors.len() < 2 {
        let direct = integrate_basic(expr, var);
        if let Some(res) = direct.clone() {
            memo.insert(expr.clone(), Some(res.clone()));
            return Some((res, String::new()));
        }
        memo.insert(expr.clone(), None);
        return None;
    }
    memo.insert(expr.clone(), None);

    let mut candidates: Vec<(usize, LiateRank)> = factors
        .iter()
        .enumerate()
        .filter_map(|(i, f)| factor_rank(f, var).map(|r| (i, r)))
        .collect();
    candidates.sort_by_key(|(_, rank)| *rank);

    for (u_idx, u_kind) in candidates {
        let u = factors[u_idx].clone();
        let dv_factors: Vec<Expr> = factors
            .iter()
            .enumerate()
            .filter_map(|(i, f)| if i == u_idx { None } else { Some(f.clone()) })
            .collect();
        let dv_expr = rebuild_product(const_factor.clone(), dv_factors);
        let Some(v) = integrate_basic(&dv_expr, var) else {
            continue;
        };
        let du = simplify_fully(differentiate(var, &u));
        let u_term = match u.clone() {
            Expr::Log(inner) => log_abs(*inner),
            other => other,
        };
        let uv = Expr::Mul(u_term.boxed(), v.clone().boxed());
        let vdu = Expr::Mul(v.boxed(), du.boxed());
        let (vdu_const_raw, vdu_factors_raw) = flatten_product(&vdu);
        let (vdu_const, vdu_factors) = combine_var_powers(vdu_const_raw, vdu_factors_raw, var);
        let vdu_normalized = rebuild_product(vdu_const.clone(), vdu_factors.clone());
        let vdu_simplified = simplify_fully(vdu_normalized.clone());
        let mut vdu_candidates = vec![vdu_normalized, vdu_simplified];
        if let Some(distributed) =
            distribute_product_with_addition(vdu_const.clone(), vdu_factors.clone(), var)
        {
            vdu_candidates.push(distributed);
        }
        if let Some(rationalized) = to_rational_candidate(vdu_const, &vdu_factors) {
            vdu_candidates.push(rationalized);
        }
        vdu_candidates.sort_by_key(|e| expr_size(e));
        let mut integral_vdu = None;
        for candidate in vdu_candidates {
            if let Some(res) = integrate_direct(&candidate, var) {
                integral_vdu = Some(res);
                break;
            }
            if let Some(res) = integrate_by_parts_recursive(&candidate, var, memo).map(|r| r.0) {
                integral_vdu = Some(res);
                break;
            }
        }
        let Some(integral_vdu) = integral_vdu else {
            continue;
        };
        let result = simplify(Expr::Sub(uv.boxed(), integral_vdu.boxed()));
        let note = format!(
            "u={} ({u_kind:?}), dv={}",
            pretty(&u),
            pretty(&dv_expr)
        );
        memo.insert(expr.clone(), Some(result.clone()));
        return Some((result, note));
    }

    None
}

fn integrate_partial_fractions(expr: &Expr, var: &str) -> Option<Expr> {
    if !is_rational_like(expr, var) {
        return None;
    }
    rational::integrate(expr, var)
}

fn classify_integrand(expr: &Expr, var: &str) -> IntegrandKind {
    if let Some(non_elem) = detect_non_elementary(expr) {
        return IntegrandKind::NonElementary(non_elem);
    }
    if let Expr::Mul(a, b) = expr {
        if matches!(&**a, Expr::Constant(_)) {
            let inner = classify_integrand(b, var);
            if !matches!(inner, IntegrandKind::Unknown | IntegrandKind::Sum) {
                return inner;
            }
        }
        if matches!(&**b, Expr::Constant(_)) {
            let inner = classify_integrand(a, var);
            if !matches!(inner, IntegrandKind::Unknown | IntegrandKind::Sum) {
                return inner;
            }
        }
    }
    if polynomial::is_polynomial(expr, var) {
        return IntegrandKind::Polynomial;
    }
    if let Some(linear) = rational::rational_kind(expr, var) {
        return IntegrandKind::Rational { linear };
    }
    if is_rational_like(expr, var) {
        return IntegrandKind::Rational { linear: false };
    }
    if trig::is_trig(expr) {
        return IntegrandKind::Trig;
    }
    if exponential::is_exp(expr) {
        return IntegrandKind::Exponential;
    }
    if logarithmic::is_log(expr) {
        return IntegrandKind::Logarithmic;
    }
    match expr {
        Expr::Mul(a, b) => IntegrandKind::Product(
            Box::new(classify_integrand(a, var)),
            Box::new(classify_integrand(b, var)),
        ),
        Expr::Add(_, _) | Expr::Sub(_, _) => IntegrandKind::Sum,
        _ => IntegrandKind::Unknown,
    }
}

fn detect_non_elementary(expr: &Expr) -> Option<NonElementaryKind> {
    match expr {
        Expr::Exp(arg) => {
            if let Some(deg) = polynomial_degree(arg) {
                if deg > 1 {
                    return Some(NonElementaryKind::ExpOfPolynomial);
                }
            }
        }
        Expr::Div(num, den) => {
            if matches!(&**num, Expr::Sin(_)) || matches!(&**num, Expr::Cos(_)) {
                if is_linear_match(num, den) {
                    return Some(NonElementaryKind::TrigOverArgument);
                }
            }
        }
        _ => {}
    }
    None
}

fn is_linear_match(num: &Expr, den: &Expr) -> bool {
    let inner = match num {
        Expr::Sin(arg) | Expr::Cos(arg) => arg,
        _ => return false,
    };
    match (&**inner, den) {
        (Expr::Variable(v1), Expr::Variable(v2)) => v1 == v2,
        (Expr::Variable(v1), Expr::Mul(a, b)) => match (&**a, &**b) {
            (Expr::Constant(_), Expr::Variable(v2)) | (Expr::Variable(v2), Expr::Constant(_)) => {
                v1 == v2
            }
            _ => false,
        },
        _ => false,
    }
}

fn polynomial_degree(expr: &Expr) -> Option<usize> {
    match expr {
        Expr::Constant(_) => Some(0),
        Expr::Variable(_) => Some(1),
        Expr::Add(a, b) | Expr::Sub(a, b) => {
            let da = polynomial_degree(a)?;
            let db = polynomial_degree(b)?;
            Some(da.max(db))
        }
        Expr::Mul(a, b) => {
            let da = polynomial_degree(a)?;
            let db = polynomial_degree(b)?;
            Some(da + db)
        }
        Expr::Pow(base, exp) => match (&**base, &**exp) {
            (Expr::Variable(_), Expr::Constant(k)) if k.is_integer() && k >= &Rational::zero() => {
                k.to_integer().to_usize()
            }
            (Expr::Constant(_), Expr::Constant(_)) => Some(0),
            _ => None,
        },
        Expr::Neg(inner) => polynomial_degree(inner),
        _ => None,
    }
}

fn is_rational_like(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Div(num, den) => {
            polynomial::is_polynomial(num, var) && polynomial::is_polynomial(den, var)
        }
        _ => false,
    }
}

fn expr_size(expr: &Expr) -> usize {
    1 + match expr {
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) | Expr::Pow(a, b) => {
            expr_size(a) + expr_size(b)
        }
        Expr::Neg(inner)
        | Expr::Sin(inner)
        | Expr::Cos(inner)
        | Expr::Tan(inner)
        | Expr::Atan(inner)
        | Expr::Asin(inner)
        | Expr::Acos(inner)
        | Expr::Exp(inner)
        | Expr::Log(inner)
        | Expr::Abs(inner) => expr_size(inner),
        Expr::Variable(_) | Expr::Constant(_) => 0,
    }
}

fn default_reason(kind: &IntegrandKind) -> ReasonCode {
    match kind {
        IntegrandKind::Rational { .. } => ReasonCode::NonRational,
        IntegrandKind::Trig => ReasonCode::NonPolynomialTrig,
        IntegrandKind::NonElementary(ne) => ReasonCode::NonElementary(ne.clone()),
        _ => ReasonCode::UnknownStructure,
    }
}

pub(crate) fn contains_var(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Variable(v) => v == var,
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) | Expr::Pow(a, b) => {
            contains_var(a, var) || contains_var(b, var)
        }
        Expr::Neg(inner)
        | Expr::Sin(inner)
        | Expr::Cos(inner)
        | Expr::Tan(inner)
        | Expr::Atan(inner)
        | Expr::Asin(inner)
        | Expr::Acos(inner)
        | Expr::Exp(inner)
        | Expr::Log(inner)
        | Expr::Abs(inner) => contains_var(inner, var),
        Expr::Constant(_) => false,
    }
}
