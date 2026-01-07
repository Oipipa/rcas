mod common;
mod cache;
mod classify;
mod exponential;
mod limits;
mod logarithmic;
mod parts;
pub(crate) mod polynomial;
pub(crate) mod rational;
mod substitution;
mod trig;
mod types;
mod utils;

use crate::calculus::risch::{risch, risch_lite};
use crate::core::expr::{Expr, Rational};
use crate::simplify::{normalize, simplify, simplify_fully};
use num_traits::{One, Zero};
use classify::{classify_integrand, is_rational_like};
use limits::TRANSFORM_SIZE_LIMIT;
use parts::{integration_by_parts, integration_by_parts_tabular};
use substitution::{integrate_by_substitution, integrate_log_derivative};
use utils::{
    as_rational_expr, combine_algebraic_factors, combine_var_powers,
    distribute_product_with_addition, expr_size, is_constant_wrt, is_one_expr, is_zero_expr,
};

pub(crate) use common::{coeff_of_var, linear_parts};
pub use exponential::is_exp;
pub use logarithmic::is_log;
pub use polynomial::is_polynomial;
pub use rational::is_rational;
pub use trig::is_trig;
pub use types::{
    AttemptStatus, IntegrandKind, IntegrandReport, IntegrationAttempt, IntegrationResult,
    NonElementaryKind, ReasonCode, Strategy,
};
pub(crate) use classify::detect_non_elementary;
pub(crate) use utils::{
    apply_constant_factor, constant_ratio, contains_var, flatten_product, log_abs, rebuild_product,
    split_constant_factors, to_rational_candidate,
};

pub fn integrate(var: &str, expr: &Expr) -> IntegrationResult {
    if is_constant_wrt(expr, var) {
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
    if exponential::is_exp_poly_product(expr, var) {
        if let Some(result) = exponential::integrate(expr, var) {
            let kind = IntegrandKind::Product(
                Box::new(IntegrandKind::Polynomial),
                Box::new(IntegrandKind::Exponential),
            );
            let mut attempts = vec![
                IntegrationAttempt {
                    strategy: Strategy::Direct,
                    status: AttemptStatus::Succeeded,
                    note: None,
                },
                IntegrationAttempt {
                    strategy: Strategy::Risch,
                    status: AttemptStatus::Succeeded,
                    note: Some("exp-poly reduction".to_string()),
                },
            ];
            if let Some((_, note)) = integration_by_parts_tabular(expr, var) {
                attempts.push(IntegrationAttempt {
                    strategy: Strategy::IntegrationByParts,
                    status: AttemptStatus::Succeeded,
                    note: Some(note),
                });
            }
            return IntegrationResult::Integrated {
                result: simplify(result),
                report: IntegrandReport {
                    kind,
                    reason: None,
                    attempts,
                },
            };
        }
    }
    let original_expr = expr.clone();
    let normalized = normalize(expr.clone());
    let mut attempts = Vec::new();
    let mut non_elem = detect_non_elementary(expr, var);
    let original_poly = polynomial::is_polynomial(&original_expr, var);
    let original_rat = rational::rational_kind(&original_expr, var);
    let normalized_poly = polynomial::is_polynomial(&normalized, var);
    let normalized_rat = rational::rational_kind(&normalized, var);
    let mut kind = if original_poly {
        IntegrandKind::Polynomial
    } else if let Some(linear) = original_rat {
        IntegrandKind::Rational { linear }
    } else if normalized_poly {
        IntegrandKind::Polynomial
    } else if let Some(linear) = normalized_rat {
        IntegrandKind::Rational { linear }
    } else {
        classify_integrand(&normalized, var)
    };
    let expr_owned = match kind {
        IntegrandKind::Polynomial => {
            if original_poly {
                original_expr.clone()
            } else {
                normalized.clone()
            }
        }
        IntegrandKind::Rational { .. } => {
            if original_rat.is_some() {
                original_expr.clone()
            } else {
                normalized.clone()
            }
        }
        _ => normalized.clone(),
    };
    let expr = &expr_owned;

    if &original_expr != expr {
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
        if exponential::is_exp_poly_product(expr, var) {
            attempts.push(IntegrationAttempt {
                strategy: Strategy::Risch,
                status: AttemptStatus::Succeeded,
                note: Some("exp-poly reduction".to_string()),
            });
        }
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
        let mut skip_risch = false;
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
                skip_risch = true;
            }
            risch_lite::RischLiteOutcome::Indeterminate { note } => {
                attempts.push(IntegrationAttempt {
                    strategy: Strategy::RischLite,
                    status: AttemptStatus::Failed(ReasonCode::UnknownStructure),
                    note: Some(note),
                });
            }
        }
        if !skip_risch {
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
        } else {
            attempts.push(IntegrationAttempt {
                strategy: Strategy::Risch,
                status: AttemptStatus::Failed(ReasonCode::NonElementary(non_elem.clone())),
                note: Some("skipped (risch-lite determinate)".to_string()),
            });
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
        let mut sub_candidates: Vec<&Expr> = vec![&simplified_for_sub, expr];
        if &original_expr != expr && &original_expr != &simplified_for_sub {
            sub_candidates.push(&original_expr);
        }
        for candidate in sub_candidates {
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
            let mut final_result = result;
            if let Some((_, note)) = integration_by_parts_tabular(expr, var) {
                attempts.push(IntegrationAttempt {
                    strategy: Strategy::IntegrationByParts,
                    status: AttemptStatus::Succeeded,
                    note: Some(note),
                });
            }
            let mut risch_outcome = risch_lite::analyze(expr, var);
            if matches!(risch_outcome, risch_lite::RischLiteOutcome::Indeterminate { .. }) {
                let retry = risch_lite::analyze(&original_expr, var);
                if !matches!(retry, risch_lite::RischLiteOutcome::Indeterminate { .. }) {
                    risch_outcome = retry;
                }
            }
            if let risch_lite::RischLiteOutcome::Integrated { result, note } = risch_outcome {
                attempts.push(IntegrationAttempt {
                    strategy: Strategy::RischLite,
                    status: AttemptStatus::Succeeded,
                    note: Some(note),
                });
                final_result = result;
            }
            return IntegrationResult::Integrated {
                result: simplify(final_result),
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

fn integrate_known(expr: &Expr, var: &str, include_log_derivative: bool) -> Option<Expr> {
    let direct = polynomial::integrate(expr, var)
        .or_else(|| rational::integrate(expr, var))
        .or_else(|| trig::integrate(expr, var))
        .or_else(|| exponential::integrate(expr, var))
        .or_else(|| logarithmic::integrate(expr, var));
    if include_log_derivative {
        direct.or_else(|| integrate_log_derivative(expr, var))
    } else {
        direct
    }
}

fn integrate_linear_ops(expr: &Expr, var: &str, include_log_derivative: bool) -> Option<Expr> {
    if is_constant_wrt(expr, var) {
        return Some(Expr::Mul(
            expr.clone().boxed(),
            Expr::Variable(var.to_string()).boxed(),
        ));
    }

    let direct = match expr {
        Expr::Add(a, b) => Some(Expr::Add(
            integrate_linear_ops(a, var, include_log_derivative)?.boxed(),
            integrate_linear_ops(b, var, include_log_derivative)?.boxed(),
        )),
        Expr::Sub(a, b) => Some(Expr::Sub(
            integrate_linear_ops(a, var, include_log_derivative)?.boxed(),
            integrate_linear_ops(b, var, include_log_derivative)?.boxed(),
        )),
        Expr::Neg(inner) => integrate_linear_ops(inner, var, include_log_derivative)
            .map(|r| Expr::Neg(r.boxed())),
        Expr::Div(num, den) => match (&**num, &**den) {
            (other, Expr::Constant(c)) => integrate_linear_ops(other, var, include_log_derivative)
                .map(|r| Expr::Div(r.boxed(), Expr::Constant(c.clone()).boxed())),
            _ => integrate_known(expr, var, include_log_derivative),
        },
        Expr::Mul(a, b) => match (&**a, &**b) {
            (Expr::Constant(c), other) | (other, Expr::Constant(c)) => {
                integrate_linear_ops(other, var, include_log_derivative)
                    .map(|r| Expr::Mul(Expr::Constant(c.clone()).boxed(), r.boxed()))
            }
            _ => integrate_known(expr, var, include_log_derivative),
        },
        _ => integrate_known(expr, var, include_log_derivative),
    };

    if direct.is_some() {
        return direct;
    }

    let (const_expr, factors) = split_constant_factors(expr, var);
    if is_zero_expr(&const_expr) {
        return Some(Expr::Constant(Rational::zero()));
    }
    if !is_one_expr(&const_expr) {
        let rest = rebuild_product(Rational::one(), factors);
        if let Some(result) = integrate_linear_ops(&rest, var, include_log_derivative) {
            return Some(apply_constant_factor(const_expr, result));
        }
    }

    None
}

fn integrate_direct(expr: &Expr, var: &str) -> Option<Expr> {
    integrate_linear_ops(expr, var, true)
}

fn integrate_basic(expr: &Expr, var: &str) -> Option<Expr> {
    integrate_linear_ops(expr, var, false)
}

fn integrate_partial_fractions(expr: &Expr, var: &str) -> Option<Expr> {
    if !is_rational_like(expr, var) {
        return None;
    }
    rational::integrate(expr, var)
}

fn default_reason(kind: &IntegrandKind) -> ReasonCode {
    match kind {
        IntegrandKind::Rational { .. } => ReasonCode::NonRational,
        IntegrandKind::Trig => ReasonCode::NonPolynomialTrig,
        IntegrandKind::NonElementary(ne) => ReasonCode::NonElementary(ne.clone()),
        _ => ReasonCode::UnknownStructure,
    }
}
