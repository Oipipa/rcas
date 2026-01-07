use crate::calculus::risch::{risch, risch_lite};
use crate::core::expr::Expr;
use crate::simplify::simplify;

use super::risch_bridge::{analyze_full, analyze_lite_with_retry};
use super::{
    AttemptStatus, IntegrandKind, IntegrandReport, IntegrationAttempt, IntegrationResult,
    NonElementaryKind, ReasonCode, Strategy,
};

pub(super) fn attempt(
    strategy: Strategy,
    status: AttemptStatus,
    note: Option<String>,
) -> IntegrationAttempt {
    IntegrationAttempt {
        strategy,
        status,
        note,
    }
}

pub(super) fn push_attempt(
    attempts: &mut Vec<IntegrationAttempt>,
    strategy: Strategy,
    status: AttemptStatus,
    note: Option<String>,
) {
    attempts.push(attempt(strategy, status, note));
}

pub(super) fn push_succeeded(
    attempts: &mut Vec<IntegrationAttempt>,
    strategy: Strategy,
    note: Option<String>,
) {
    push_attempt(attempts, strategy, AttemptStatus::Succeeded, note);
}

pub(super) fn push_failed(
    attempts: &mut Vec<IntegrationAttempt>,
    strategy: Strategy,
    reason: ReasonCode,
    note: Option<String>,
) {
    push_attempt(attempts, strategy, AttemptStatus::Failed(reason), note);
}

pub(super) fn push_hit_limit(
    attempts: &mut Vec<IntegrationAttempt>,
    strategy: Strategy,
    size: usize,
    limit: usize,
) {
    push_attempt(
        attempts,
        strategy,
        AttemptStatus::HitLimit { size, limit },
        None,
    );
}

pub(super) fn push_not_applicable(
    attempts: &mut Vec<IntegrationAttempt>,
    strategy: Strategy,
) {
    push_attempt(attempts, strategy, AttemptStatus::NotApplicable, None);
}

pub(super) fn default_reason(kind: &IntegrandKind) -> ReasonCode {
    match kind {
        IntegrandKind::Rational { .. } => ReasonCode::NonRational,
        IntegrandKind::Trig => ReasonCode::NonPolynomialTrig,
        IntegrandKind::NonElementary(ne) => ReasonCode::NonElementary(ne.clone()),
        _ => ReasonCode::UnknownStructure,
    }
}

pub(super) fn handle_non_elementary_early_exit(
    mut attempts: Vec<IntegrationAttempt>,
    expr: &Expr,
    original_expr: &Expr,
    var: &str,
    non_elem: NonElementaryKind,
) -> IntegrationResult {
    let reason = ReasonCode::NonElementary(non_elem.clone());
    let kind = IntegrandKind::NonElementary(non_elem.clone());

    push_failed(
        &mut attempts,
        Strategy::Substitution,
        reason.clone(),
        None,
    );
    push_failed(
        &mut attempts,
        Strategy::IntegrationByParts,
        reason.clone(),
        None,
    );
    push_failed(
        &mut attempts,
        Strategy::PartialFractions,
        reason.clone(),
        None,
    );

    let mut skip_risch = false;
    match analyze_lite_with_retry(expr, original_expr, var) {
        risch_lite::RischLiteOutcome::Integrated { result, note } => {
            push_succeeded(&mut attempts, Strategy::RischLite, Some(note));
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
            push_failed(
                &mut attempts,
                Strategy::RischLite,
                ReasonCode::NonElementary(ne_kind),
                Some(note),
            );
            skip_risch = true;
        }
        risch_lite::RischLiteOutcome::Indeterminate { note } => {
            push_failed(
                &mut attempts,
                Strategy::RischLite,
                ReasonCode::UnknownStructure,
                Some(note),
            );
        }
    }

    if !skip_risch {
        match analyze_full(expr, var) {
            risch::RischOutcome::Integrated { result, note } => {
                push_succeeded(&mut attempts, Strategy::Risch, Some(note));
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
                push_failed(
                    &mut attempts,
                    Strategy::Risch,
                    ReasonCode::NonElementary(ne_kind),
                    Some(note),
                );
            }
            risch::RischOutcome::Indeterminate { note } => {
                push_failed(
                    &mut attempts,
                    Strategy::Risch,
                    ReasonCode::UnknownStructure,
                    Some(note),
                );
            }
        }
    } else {
        push_failed(
            &mut attempts,
            Strategy::Risch,
            ReasonCode::NonElementary(non_elem.clone()),
            Some("skipped (risch-lite determinate)".to_string()),
        );
    }

    push_failed(
        &mut attempts,
        Strategy::MeijerG,
        ReasonCode::StrategyNotAvailable("meijer-g expansion"),
        None,
    );

    IntegrationResult::NotIntegrable(IntegrandReport {
        kind,
        reason: Some(reason),
        attempts,
    })
}

pub(super) fn finish_with_risch_attempts(
    mut attempts: Vec<IntegrationAttempt>,
    expr: &Expr,
    original_expr: &Expr,
    var: &str,
    mut kind: IntegrandKind,
    non_elem: Option<NonElementaryKind>,
) -> IntegrationResult {
    let mut risch_non_elem: Option<NonElementaryKind> = None;
    let mut risch_full_non_elem: Option<NonElementaryKind> = None;

    match analyze_lite_with_retry(expr, original_expr, var) {
        risch_lite::RischLiteOutcome::Integrated { result, note } => {
            push_succeeded(&mut attempts, Strategy::RischLite, Some(note));
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
            push_failed(
                &mut attempts,
                Strategy::RischLite,
                ReasonCode::NonElementary(ne_kind.clone()),
                Some(note),
            );
            if !matches!(kind, IntegrandKind::NonElementary(_)) {
                kind = IntegrandKind::NonElementary(ne_kind.clone());
            }
            risch_non_elem = Some(ne_kind);
        }
        risch_lite::RischLiteOutcome::Indeterminate { note } => {
            push_failed(
                &mut attempts,
                Strategy::RischLite,
                ReasonCode::UnknownStructure,
                Some(note),
            );
        }
    }

    match analyze_full(expr, var) {
        risch::RischOutcome::Integrated { result, note } => {
            push_succeeded(&mut attempts, Strategy::Risch, Some(note));
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
            push_failed(
                &mut attempts,
                Strategy::Risch,
                ReasonCode::NonElementary(ne_kind.clone()),
                Some(note),
            );
            if !matches!(kind, IntegrandKind::NonElementary(_)) {
                kind = IntegrandKind::NonElementary(ne_kind.clone());
            }
            risch_full_non_elem = Some(ne_kind);
        }
        risch::RischOutcome::Indeterminate { note } => {
            push_failed(
                &mut attempts,
                Strategy::Risch,
                ReasonCode::UnknownStructure,
                Some(note),
            );
        }
    }

    push_failed(
        &mut attempts,
        Strategy::MeijerG,
        ReasonCode::StrategyNotAvailable("meijer-g expansion"),
        None,
    );

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
