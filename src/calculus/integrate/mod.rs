mod common;
mod cache;
mod classify;
mod direct;
mod exponential;
mod limits;
mod logarithmic;
mod parts;
mod partial_fractions;
pub(crate) mod polynomial;
pub(crate) mod rational;
mod report;
mod risch_bridge;
mod substitution;
mod trig;
mod types;
mod utils;

use crate::calculus::risch::risch_lite;
use crate::core::expr::Expr;
use crate::simplify::{normalize, simplify, simplify_fully};
use classify::{classify_integrand, is_rational_like};
use limits::TRANSFORM_SIZE_LIMIT;
use parts::{integration_by_parts, integration_by_parts_tabular};
use partial_fractions::integrate_partial_fractions;
use report::{
    attempt, default_reason, finish_with_risch_attempts, handle_non_elementary_early_exit,
    push_attempt, push_failed, push_hit_limit, push_not_applicable, push_succeeded,
};
use risch_bridge::analyze_lite_with_retry;
use substitution::{integrate_by_substitution, substitution_candidates};

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
use direct::{integrate_basic, integrate_direct};
use utils::{
    as_rational_expr, combine_algebraic_factors, combine_var_powers,
    distribute_product_with_addition, expr_size, is_constant_wrt, is_one_expr, is_zero_expr,
};
pub(crate) use utils::{
    apply_constant_factor, constant_ratio, contains_var, flatten_product, fresh_var_name, log_abs,
    rebuild_product, scale_by_coeff, split_constant_factors, to_rational_candidate,
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
                attempts: vec![attempt(
                    Strategy::Direct,
                    AttemptStatus::Succeeded,
                    None,
                )],
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
                attempt(Strategy::Direct, AttemptStatus::Succeeded, None),
                attempt(
                    Strategy::Risch,
                    AttemptStatus::Succeeded,
                    Some("exp-poly reduction".to_string()),
                ),
            ];
            if let Some((_, note)) = integration_by_parts_tabular(expr, var) {
                push_succeeded(
                    &mut attempts,
                    Strategy::IntegrationByParts,
                    Some(note),
                );
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

    if &original_expr != expr && non_elem.is_none() {
        non_elem = detect_non_elementary(expr, var);
    }
    if let Some(ref detected) = non_elem {
        if !matches!(kind, IntegrandKind::NonElementary(_)) {
            kind = IntegrandKind::NonElementary(detected.clone());
        }
    }

    if let Some(result) = integrate_direct(expr, var) {
        push_succeeded(&mut attempts, Strategy::Direct, None);
        if exponential::is_exp_poly_product(expr, var) {
            push_succeeded(
                &mut attempts,
                Strategy::Risch,
                Some("exp-poly reduction".to_string()),
            );
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

    push_failed(
        &mut attempts,
        Strategy::Direct,
        default_reason(&kind),
        None,
    );

    if let Some(non_elem) = non_elem.clone() {
        return handle_non_elementary_early_exit(
            attempts,
            expr,
            &original_expr,
            var,
            non_elem,
        );
    }

    let size = expr_size(expr);
    let (simplified_for_sub, sub_candidates) =
        substitution_candidates(expr, &original_expr);
    let sub_size = expr_size(&simplified_for_sub);

    // Substitution heuristics (u-sub, f'/f).
    if sub_size > TRANSFORM_SIZE_LIMIT {
        push_hit_limit(
            &mut attempts,
            Strategy::Substitution,
            sub_size,
            TRANSFORM_SIZE_LIMIT,
        );
    } else {
        let mut sub_result = None;
        for candidate in &sub_candidates {
            if let Some(result) = integrate_by_substitution(candidate, var) {
                sub_result = Some(result);
                break;
            }
        }

        if let Some(result) = sub_result {
            push_succeeded(&mut attempts, Strategy::Substitution, None);
            let mut final_result = result;
            if let Some((_, note)) = integration_by_parts_tabular(expr, var) {
                push_succeeded(
                    &mut attempts,
                    Strategy::IntegrationByParts,
                    Some(note),
                );
            }
            let risch_outcome = analyze_lite_with_retry(expr, &original_expr, var);
            if let risch_lite::RischLiteOutcome::Integrated {
                result: risch_result,
                note,
            } = risch_outcome
            {
                push_succeeded(&mut attempts, Strategy::RischLite, Some(note));
                let diff = simplify_fully(Expr::Sub(
                    risch_result.clone().boxed(),
                    final_result.clone().boxed(),
                ));
                if !is_constant_wrt(&diff, var) {
                    final_result = risch_result;
                }
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
            push_not_applicable(&mut attempts, Strategy::Substitution);
        }
    }

    // Integration by parts for polynomial * trig/exp/log forms.
    if size > TRANSFORM_SIZE_LIMIT {
        push_hit_limit(
            &mut attempts,
            Strategy::IntegrationByParts,
            size,
            TRANSFORM_SIZE_LIMIT,
        );
    } else if let Some((result, note)) = integration_by_parts(expr, var) {
        push_succeeded(&mut attempts, Strategy::IntegrationByParts, Some(note));
        return IntegrationResult::Integrated {
            result: simplify(result),
            report: IntegrandReport {
                kind,
                reason: None,
                attempts,
            },
        };
    } else {
        push_not_applicable(&mut attempts, Strategy::IntegrationByParts);
    }

    // Partial fractions (only if rational).
    if size > TRANSFORM_SIZE_LIMIT {
        push_hit_limit(
            &mut attempts,
            Strategy::PartialFractions,
            size,
            TRANSFORM_SIZE_LIMIT,
        );
    } else if let Some(result) = integrate_partial_fractions(expr, var) {
        push_succeeded(&mut attempts, Strategy::PartialFractions, None);
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
        push_attempt(&mut attempts, Strategy::PartialFractions, status, None);
    }

    finish_with_risch_attempts(attempts, expr, &original_expr, var, kind, non_elem)
}
