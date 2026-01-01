mod common;
mod exponential;
mod logarithmic;
mod polynomial;
mod rational;
mod risch;
mod risch_lite;
mod trig;

use crate::calculus::differentiate;
use crate::expr::{Expr, Rational};
use crate::factor::Poly;
use crate::format::expr::pretty;
use crate::polynomial::Polynomial;
use crate::simplify::{normalize, simplify, simplify_fully};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::{BTreeSet, HashMap};

pub(crate) use common::{coeff_of_var, linear_parts};
pub use exponential::is_exp;
pub use logarithmic::is_log;
pub use polynomial::is_polynomial;
pub use rational::is_rational;
pub use trig::is_trig;

const TRANSFORM_SIZE_LIMIT: usize = 96;
const TABULAR_STEP_LIMIT: usize = 8;
const IBP_RECURSION_LIMIT: usize = 12;
type ExprPoly = Polynomial<Expr>;

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
    TrigOverPolynomialArgument,
    PowerSelf,
    PowerSelfLog,
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
    Risch,
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
    if !contains_var(expr, var) {
        let kind = classify_integrand(expr, var);
        return IntegrationResult::Integrated {
            result: simplify(Expr::Mul(
                expr.clone().boxed(),
                Expr::Variable(var.to_string()).boxed(),
            )),
            report: IntegrandReport {
                kind,
                reason: None,
                attempts: vec![IntegrationAttempt {
                    strategy: Strategy::Direct,
                    status: AttemptStatus::Succeeded,
                    note: None,
                }],
            },
        };
    }
    let original_expr = expr.clone();
    let normalized = normalize(expr.clone());
    let mut attempts = Vec::new();
    let mut non_elem = detect_non_elementary(expr, var);
    let original_poly = polynomial::is_polynomial(&original_expr, var);
    let original_rat = rational::rational_kind(&original_expr, var);
    let mut kind = if original_poly {
        IntegrandKind::Polynomial
    } else if let Some(linear) = original_rat {
        IntegrandKind::Rational { linear }
    } else {
        classify_integrand(&normalized, var)
    };
    let expr_owned = match kind {
        IntegrandKind::Polynomial | IntegrandKind::Rational { .. } => original_expr.clone(),
        _ => normalized.clone(),
    };
    let expr = &expr_owned;

    if non_elem.is_none() {
        non_elem = detect_non_elementary(expr, var);
    }
    if let Some(ref detected) = non_elem {
        if !matches!(kind, IntegrandKind::NonElementary(_)) {
            kind = IntegrandKind::NonElementary(detected.clone());
        }
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

    if let Some(non_elem) = non_elem.clone() {
        let reason = ReasonCode::NonElementary(non_elem.clone());
        attempts.push(IntegrationAttempt {
            strategy: Strategy::Substitution,
            status: AttemptStatus::Failed(reason.clone()),
            note: None,
        });
        attempts.push(IntegrationAttempt {
            strategy: Strategy::IntegrationByParts,
            status: AttemptStatus::Failed(reason.clone()),
            note: None,
        });
        attempts.push(IntegrationAttempt {
            strategy: Strategy::PartialFractions,
            status: AttemptStatus::Failed(reason.clone()),
            note: None,
        });
        let mut risch_outcome = risch_lite::analyze(expr, var);
        if matches!(risch_outcome, risch_lite::RischLiteOutcome::Indeterminate { .. }) {
            let retry = risch_lite::analyze(&original_expr, var);
            if !matches!(retry, risch_lite::RischLiteOutcome::Indeterminate { .. }) {
                risch_outcome = retry;
            }
        }
        match risch_outcome {
            risch_lite::RischLiteOutcome::Integrated { result, note } => {
                attempts.push(IntegrationAttempt {
                    strategy: Strategy::RischLite,
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
            }
            risch_lite::RischLiteOutcome::NonElementary { kind, note } => {
                attempts.push(IntegrationAttempt {
                    strategy: Strategy::RischLite,
                    status: AttemptStatus::Failed(ReasonCode::NonElementary(kind)),
                    note: Some(note),
                });
            }
            risch_lite::RischLiteOutcome::Indeterminate { note } => {
                attempts.push(IntegrationAttempt {
                    strategy: Strategy::RischLite,
                    status: AttemptStatus::Failed(ReasonCode::UnknownStructure),
                    note: Some(note),
                });
            }
        }
        let risch_outcome = risch::analyze(expr, var);
        match risch_outcome {
            risch::RischOutcome::Integrated { result, note } => {
                attempts.push(IntegrationAttempt {
                    strategy: Strategy::Risch,
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
            }
            risch::RischOutcome::NonElementary { kind: ne_kind, note } => {
                attempts.push(IntegrationAttempt {
                    strategy: Strategy::Risch,
                    status: AttemptStatus::Failed(ReasonCode::NonElementary(ne_kind)),
                    note: Some(note),
                });
            }
            risch::RischOutcome::Indeterminate { note } => {
                attempts.push(IntegrationAttempt {
                    strategy: Strategy::Risch,
                    status: AttemptStatus::Failed(ReasonCode::UnknownStructure),
                    note: Some(note),
                });
            }
        }
        attempts.push(IntegrationAttempt {
            strategy: Strategy::MeijerG,
            status: AttemptStatus::Failed(ReasonCode::StrategyNotAvailable("meijer-g expansion")),
            note: None,
        });
        return IntegrationResult::NotIntegrable(IntegrandReport {
            kind: IntegrandKind::NonElementary(non_elem),
            reason: Some(reason),
            attempts,
        });
    }

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

    let mut risch_non_elem: Option<NonElementaryKind> = None;
    let mut risch_full_non_elem: Option<NonElementaryKind> = None;
    let mut risch_outcome = risch_lite::analyze(expr, var);
    if matches!(risch_outcome, risch_lite::RischLiteOutcome::Indeterminate { .. }) {
        let retry = risch_lite::analyze(&original_expr, var);
        if !matches!(retry, risch_lite::RischLiteOutcome::Indeterminate { .. }) {
            risch_outcome = retry;
        }
    }
    match risch_outcome {
        risch_lite::RischLiteOutcome::Integrated { result, note } => {
            attempts.push(IntegrationAttempt {
                strategy: Strategy::RischLite,
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
        }
        risch_lite::RischLiteOutcome::NonElementary { kind: ne_kind, note } => {
            attempts.push(IntegrationAttempt {
                strategy: Strategy::RischLite,
                status: AttemptStatus::Failed(ReasonCode::NonElementary(ne_kind.clone())),
                note: Some(note),
            });
            if !matches!(kind, IntegrandKind::NonElementary(_)) {
                kind = IntegrandKind::NonElementary(ne_kind.clone());
            }
            risch_non_elem = Some(ne_kind);
        }
        risch_lite::RischLiteOutcome::Indeterminate { note } => {
            attempts.push(IntegrationAttempt {
                strategy: Strategy::RischLite,
                status: AttemptStatus::Failed(ReasonCode::UnknownStructure),
                note: Some(note),
            });
        }
    }
    let risch_outcome = risch::analyze(expr, var);
    match risch_outcome {
        risch::RischOutcome::Integrated { result, note } => {
            attempts.push(IntegrationAttempt {
                strategy: Strategy::Risch,
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
        }
        risch::RischOutcome::NonElementary { kind: ne_kind, note } => {
            attempts.push(IntegrationAttempt {
                strategy: Strategy::Risch,
                status: AttemptStatus::Failed(ReasonCode::NonElementary(ne_kind.clone())),
                note: Some(note),
            });
            if !matches!(kind, IntegrandKind::NonElementary(_)) {
                kind = IntegrandKind::NonElementary(ne_kind.clone());
            }
            risch_full_non_elem = Some(ne_kind);
        }
        risch::RischOutcome::Indeterminate { note } => {
            attempts.push(IntegrationAttempt {
                strategy: Strategy::Risch,
                status: AttemptStatus::Failed(ReasonCode::UnknownStructure),
                note: Some(note),
            });
        }
    }
    attempts.push(IntegrationAttempt {
        strategy: Strategy::MeijerG,
        status: AttemptStatus::Failed(ReasonCode::StrategyNotAvailable("meijer-g expansion")),
        note: None,
    });

    let reason = Some(match non_elem.or(risch_full_non_elem).or(risch_non_elem) {
        Some(non_elem) => ReasonCode::NonElementary(non_elem),
        None => default_reason(&kind),
    });
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
    let direct = match expr {
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
                .or_else(|| logarithmic::integrate(expr, var))
                .or_else(|| integrate_log_derivative(expr, var)),
        },
        Expr::Mul(a, b) => match (&**a, &**b) {
            (Expr::Constant(c), other) | (other, Expr::Constant(c)) => integrate_direct(other, var)
                .map(|r| Expr::Mul(Expr::Constant(c.clone()).boxed(), r.boxed())),
            _ => polynomial::integrate(expr, var)
                .or_else(|| rational::integrate(expr, var))
                .or_else(|| trig::integrate(expr, var))
                .or_else(|| exponential::integrate(expr, var))
                .or_else(|| logarithmic::integrate(expr, var))
                .or_else(|| integrate_log_derivative(expr, var)),
        },
        _ => polynomial::integrate(expr, var)
            .or_else(|| rational::integrate(expr, var))
            .or_else(|| trig::integrate(expr, var))
            .or_else(|| exponential::integrate(expr, var))
            .or_else(|| logarithmic::integrate(expr, var))
            .or_else(|| integrate_log_derivative(expr, var)),
    };
    if direct.is_some() {
        return direct;
    }
    let (const_expr, factors) = split_constant_factors(expr, var);
    if is_zero_expr(&const_expr) {
        return Some(Expr::Constant(Rational::zero()));
    }
    if !is_one_expr(&const_expr) {
        let rest = rebuild_product(Rational::one(), factors.clone());
        if let Some(result) = integrate_direct(&rest, var) {
            return Some(apply_constant_factor(const_expr, result));
        }
    }
    None
}

fn integrate_basic(expr: &Expr, var: &str) -> Option<Expr> {
    if !contains_var(expr, var) {
        return Some(Expr::Mul(
            expr.clone().boxed(),
            Expr::Variable(var.to_string()).boxed(),
        ));
    }
    let direct = match expr {
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
    };
    if direct.is_some() {
        return direct;
    }
    let (const_expr, factors) = split_constant_factors(expr, var);
    if is_zero_expr(&const_expr) {
        return Some(Expr::Constant(Rational::zero()));
    }
    if !is_one_expr(&const_expr) {
        let rest = rebuild_product(Rational::one(), factors.clone());
        if let Some(result) = integrate_basic(&rest, var) {
            return Some(apply_constant_factor(const_expr, result));
        }
    }
    None
}

fn integrate_by_substitution(expr: &Expr, var: &str) -> Option<Expr> {
    let (const_expr, factors) = split_constant_factors(expr, var);
    if is_zero_expr(&const_expr) {
        return Some(Expr::Constant(Rational::zero()));
    }
    if let Some(result) = integrate_log_derivative(expr, var) {
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
            rebuild_product(Rational::one(), remaining.clone()),
        ));

        let multiplier = {
            let ratio_expr = simplify_fully(Expr::Div(
                remaining_expr.clone().boxed(),
                inner_derivative.clone().boxed(),
            ));
            if !contains_var(&ratio_expr, var) {
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

    None
}

fn integrate_log_derivative(expr: &Expr, var: &str) -> Option<Expr> {
    let (num, den) = as_rational_expr(expr);
    let num = simplify_fully(num);
    let den = simplify_fully(den);
    if !contains_var(&den, var) {
        return None;
    }
    let den_derivative = simplify_fully(differentiate(var, &den));
    if den_derivative.is_zero() {
        return None;
    }
    let ratio = constant_ratio(&num, &den_derivative, var)?;
    if contains_var(&ratio, var) {
        return None;
    }
    Some(simplify(Expr::Mul(ratio.boxed(), log_abs(den).boxed())))
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
        Expr::Atan(_)
        | Expr::Asin(_)
        | Expr::Acos(_)
        | Expr::Asec(_)
        | Expr::Acsc(_)
        | Expr::Acot(_)
        | Expr::Asinh(_)
        | Expr::Acosh(_)
        | Expr::Atanh(_) => Some(LiateRank::InverseTrig),
        e if polynomial::is_polynomial(e, var) => Some(LiateRank::Algebraic),
        Expr::Sin(_)
        | Expr::Cos(_)
        | Expr::Tan(_)
        | Expr::Sec(_)
        | Expr::Csc(_)
        | Expr::Cot(_)
        | Expr::Sinh(_)
        | Expr::Cosh(_)
        | Expr::Tanh(_) => Some(LiateRank::Trig),
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
                Expr::Mul(inner.clone().boxed(), Expr::Asinh(inner.clone().boxed()).boxed())
                    .boxed(),
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
                Expr::Mul(inner.clone().boxed(), Expr::Acosh(inner.clone().boxed()).boxed())
                    .boxed(),
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
                Expr::Mul(inner.clone().boxed(), Expr::Atanh(inner.clone().boxed()).boxed())
                    .boxed(),
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

fn constant_ratio(expr: &Expr, target: &Expr, var: &str) -> Option<Expr> {
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
            (other, expr_const) if other == &target_norm && !contains_var(expr_const, var) => {
                return Some(expr_const.clone());
            }
            (expr_const, other) if other == &target_norm && !contains_var(expr_const, var) => {
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
    let quotient = simplify_fully(Expr::Div(expr_norm.clone().boxed(), target_norm.clone().boxed()));
    if !contains_var(&quotient, var) {
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
    if contains_var(&ratio, var) {
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

fn as_rational_expr(expr: &Expr) -> (Expr, Expr) {
    let (const_factor, factors) = flatten_product(expr);
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

    let numerator = rebuild_product(const_factor, num_factors);
    let denominator = if den_factors.is_empty() {
        Expr::Constant(Rational::one())
    } else {
        rebuild_product(Rational::one(), den_factors)
    };

    (numerator, denominator)
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
                if let Expr::Pow(base, exp) = &factor {
                    if let Expr::Constant(k) = &**exp {
                        fa.push(Expr::Pow(
                            base.clone(),
                            Expr::Constant(-k.clone()).boxed(),
                        ));
                        continue;
                    }
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

fn split_constant_factors(expr: &Expr, var: &str) -> (Expr, Vec<Expr>) {
    let (const_factor, factors) = flatten_product(expr);
    let mut const_factors = Vec::new();
    let mut var_factors = Vec::new();
    for factor in factors {
        if contains_var(&factor, var) {
            var_factors.push(factor);
        } else {
            const_factors.push(factor);
        }
    }
    (rebuild_product(const_factor, const_factors), var_factors)
}

fn combine_algebraic_factors(factors: Vec<Expr>, var: &str) -> Vec<Expr> {
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

fn apply_constant_factor(const_factor: Expr, expr: Expr) -> Expr {
    if is_one_expr(&const_factor) {
        expr
    } else {
        simplify(Expr::Mul(const_factor.boxed(), expr.boxed()))
    }
}

fn is_zero_expr(expr: &Expr) -> bool {
    matches!(simplify_fully(expr.clone()), Expr::Constant(c) if c.is_zero())
}

fn is_one_expr(expr: &Expr) -> bool {
    matches!(simplify_fully(expr.clone()), Expr::Constant(c) if c.is_one())
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
}

fn integration_by_parts(expr: &Expr, var: &str) -> Option<(Expr, String)> {
    if let Some(result) = integration_by_parts_tabular(expr, var) {
        return Some(result);
    }
    let mut memo = HashMap::new();
    integrate_by_parts_recursive(expr, var, &mut memo, 0)
}

fn integrate_by_parts_recursive(
    expr: &Expr,
    var: &str,
    memo: &mut HashMap<Expr, Option<Expr>>,
    depth: usize,
) -> Option<(Expr, String)> {
    if depth >= IBP_RECURSION_LIMIT {
        return None;
    }
    if let Some(result) = memo.get(expr) {
        return result.clone().map(|r| (r, String::new()));
    }

    if let Some((result, note)) = integration_by_parts_tabular(expr, var) {
        memo.insert(expr.clone(), Some(result.clone()));
        return Some((result, note));
    }

    let (const_expr, factors) = split_constant_factors(expr, var);
    if is_zero_expr(&const_expr) {
        let zero = Expr::Constant(Rational::zero());
        memo.insert(expr.clone(), Some(zero.clone()));
        return Some((zero, String::new()));
    }
    if !is_one_expr(&const_expr) {
        memo.insert(expr.clone(), None);
        let rest_expr = rebuild_product(Rational::one(), factors.clone());
        if let Some((res, note)) = integrate_by_parts_recursive(&rest_expr, var, memo, depth + 1) {
            let scaled = simplify(Expr::Mul(const_expr.boxed(), res.boxed()));
            memo.insert(expr.clone(), Some(scaled.clone()));
            return Some((scaled, note));
        }
        return None;
    }

    let factors = combine_algebraic_factors(factors, var);
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
    let expr_size_current = expr_size(expr);

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
        let dv_expr = rebuild_product(Rational::one(), dv_factors);
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
            let candidate_size = expr_size(&candidate);
            if candidate_size > TRANSFORM_SIZE_LIMIT || candidate_size > expr_size_current + 8 {
                continue;
            }
            if let Some(res) =
                integrate_by_parts_recursive(&candidate, var, memo, depth + 1).map(|r| r.0)
            {
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

fn integration_by_parts_tabular(expr: &Expr, var: &str) -> Option<(Expr, String)> {
    let (const_expr, factors) = split_constant_factors(expr, var);
    if is_zero_expr(&const_expr) {
        return Some((Expr::Constant(Rational::zero()), String::from("tabular-ibp")));
    }
    if !is_one_expr(&const_expr) {
        let rest = rebuild_product(Rational::one(), factors.clone());
        if let Some((result, note)) = integration_by_parts_tabular(&rest, var) {
            let scaled = simplify(Expr::Mul(const_expr.boxed(), result.boxed()));
            return Some((scaled, note));
        }
        return None;
    }

    let factors = combine_algebraic_factors(factors, var);
    if factors.len() != 2 {
        return None;
    }

    let (poly_factor, other_factor) = if polynomial::is_polynomial(&factors[0], var) {
        (factors[0].clone(), factors[1].clone())
    } else if polynomial::is_polynomial(&factors[1], var) {
        (factors[1].clone(), factors[0].clone())
    } else {
        return None;
    };

    let degree = polynomial::degree(&poly_factor, var)?;
    if degree == 0 || degree > TABULAR_STEP_LIMIT {
        return None;
    }

    if polynomial::is_polynomial(&other_factor, var) {
        return None;
    }

    if let Expr::Log(arg) = &other_factor {
        let result = integrate_polynomial_times_log(&poly_factor, arg, var)?;
        return Some((result, String::from("tabular-ibp-log")));
    }

    if !matches!(
        other_factor,
        Expr::Exp(_)
            | Expr::Sin(_)
            | Expr::Cos(_)
            | Expr::Sinh(_)
            | Expr::Cosh(_)
    ) {
        return None;
    }

    let mut derivatives = Vec::new();
    let mut current = poly_factor.clone();
    for _ in 0..=degree {
        if is_zero_expr(&current) {
            break;
        }
        derivatives.push(simplify_fully(current.clone()));
        current = simplify_fully(differentiate(var, &current));
    }
    if derivatives.is_empty() || derivatives.len() > TABULAR_STEP_LIMIT {
        return None;
    }

    let mut integrals = Vec::new();
    let mut kernel = other_factor.clone();
    for _ in 0..derivatives.len() {
        let next = integrate_basic(&kernel, var)?;
        if expr_size(&next) > TRANSFORM_SIZE_LIMIT {
            return None;
        }
        integrals.push(simplify(next.clone()));
        kernel = next;
    }

    let mut terms = Vec::new();
    for (idx, deriv) in derivatives.into_iter().enumerate() {
        let term = Expr::Mul(deriv.boxed(), integrals[idx].clone().boxed());
        let signed = if idx % 2 == 1 {
            Expr::Neg(term.boxed())
        } else {
            term
        };
        terms.push(signed);
    }
    let result = simplify(
        terms
            .into_iter()
            .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
            .unwrap(),
    );

    if expr_size(&result) > TRANSFORM_SIZE_LIMIT {
        return None;
    }

    Some((result, String::from("tabular-ibp")))
}

fn integrate_polynomial_times_log(poly: &Expr, log_arg: &Expr, var: &str) -> Option<Expr> {
    let base = match log_arg {
        Expr::Abs(inner) => inner.as_ref().clone(),
        _ => log_arg.clone(),
    };
    let (coef, _) = linear_parts(&base, var)?;
    if is_zero_expr(&coef) {
        return None;
    }

    let poly_integral = polynomial::integrate(poly, var)?;
    let log_term = Expr::Mul(poly_integral.clone().boxed(), log_abs(base.clone()).boxed());
    let ratio = simplify(Expr::Div(coef.boxed(), base.boxed()));
    let vdu = simplify(Expr::Mul(poly_integral.boxed(), ratio.boxed()));
    let vdu_integral = integrate_direct(&vdu, var)?;
    Some(simplify(Expr::Sub(log_term.boxed(), vdu_integral.boxed())))
}

fn integrate_partial_fractions(expr: &Expr, var: &str) -> Option<Expr> {
    if !is_rational_like(expr, var) {
        return None;
    }
    rational::integrate(expr, var)
}

fn classify_integrand(expr: &Expr, var: &str) -> IntegrandKind {
    if let Some(non_elem) = detect_non_elementary(expr, var) {
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
    if let Some(linear) = rational::rational_kind(expr, var) {
        return IntegrandKind::Rational { linear };
    }
    if polynomial::is_polynomial(expr, var) {
        return IntegrandKind::Polynomial;
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

fn detect_non_elementary(expr: &Expr, var: &str) -> Option<NonElementaryKind> {
    if !contains_var(expr, var) {
        return None;
    }

    match expr {
        Expr::Mul(_, _) | Expr::Div(_, _) | Expr::Neg(_) => {
            let (_, var_factors) = split_constant_factors(expr, var);
            if var_factors.len() == 1 {
                if let Some(kind) = detect_non_elementary_core(&var_factors[0], var) {
                    return Some(kind);
                }
            }
            if let Some(kind) = detect_power_self_log(&var_factors, var) {
                return Some(kind);
            }
        }
        _ => {}
    }

    detect_non_elementary_core(expr, var)
}

fn detect_non_elementary_core(expr: &Expr, var: &str) -> Option<NonElementaryKind> {
    match expr {
        Expr::Exp(arg) => {
            if let Some(deg) = polynomial_degree(arg, var) {
                if deg > 1 {
                    return Some(NonElementaryKind::ExpOfPolynomial);
                }
            }
        }
        Expr::Pow(base, exp) => {
            if is_pow_self(base, exp, var) {
                return Some(NonElementaryKind::PowerSelf);
            }
            if let Expr::Constant(k) = &**exp {
                if !k.is_integer() {
                    if let Some(deg) = polynomial_degree(base, var) {
                        if deg >= 2 {
                            if k.denom() != &BigInt::from(2) || deg > 2 {
                                return Some(NonElementaryKind::SpecialFunctionNeeded);
                            }
                        }
                    }
                }
            }
        }
        Expr::Div(num, den) => {
            if let Some(kind) = trig_over_argument_kind(num, den, var) {
                return Some(kind);
            }
        }
        _ => {}
    }
    None
}

fn trig_over_argument_kind(num: &Expr, den: &Expr, var: &str) -> Option<NonElementaryKind> {
    let arg = match num {
        Expr::Sin(arg) | Expr::Cos(arg) | Expr::Tan(arg) => arg,
        _ => return None,
    };
    if constant_ratio(den, arg, var).is_none() {
        return None;
    }
    let degree = polynomial_degree(arg, var)?;
    if degree > 1 {
        Some(NonElementaryKind::TrigOverPolynomialArgument)
    } else if degree == 1 {
        Some(NonElementaryKind::TrigOverArgument)
    } else {
        None
    }
}

fn detect_power_self_log(factors: &[Expr], var: &str) -> Option<NonElementaryKind> {
    let mut saw_pow_self = false;
    let mut saw_log = false;

    for factor in factors {
        if is_pow_self_expr(factor, var) {
            saw_pow_self = true;
            continue;
        }
        if is_log_var(factor, var) {
            saw_log = true;
            continue;
        }
        if contains_var(factor, var) {
            return None;
        }
    }

    if saw_pow_self && saw_log {
        Some(NonElementaryKind::PowerSelfLog)
    } else {
        None
    }
}

fn is_pow_self(base: &Expr, exp: &Expr, var: &str) -> bool {
    matches!(base, Expr::Variable(name) if name == var)
        && matches!(exp, Expr::Variable(name) if name == var)
}

fn is_pow_self_expr(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Pow(base, exp) => is_pow_self(base, exp, var),
        _ => false,
    }
}

fn is_log_var(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Log(inner) => match &**inner {
            Expr::Variable(name) if name == var => true,
            Expr::Abs(inner) => matches!(&**inner, Expr::Variable(name) if name == var),
            _ => false,
        },
        _ => false,
    }
}

fn polynomial_degree(expr: &Expr, var: &str) -> Option<usize> {
    polynomial::degree(expr, var)
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
