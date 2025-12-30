use crate::calculus::integrate::{AttemptStatus, IntegrationAttempt, IntegrationResult};
use crate::format::expr::pretty;

/// Render an `IntegrationResult` into human-friendly lines.
pub fn pretty_integration_result(result: &IntegrationResult) -> Vec<String> {
    match result {
        IntegrationResult::Integrated { result, report } => {
            let mut lines = Vec::new();
            lines.push(format!("integrated: {}", pretty(result)));
            lines.push(format!("kind: {:?}", report.kind));
            lines.extend(report.attempts.iter().map(describe_attempt));
            lines
        }
        IntegrationResult::NotIntegrable(report) => {
            let mut lines = Vec::new();
            lines.push("not integrable".to_string());
            lines.push(format!("kind: {:?}", report.kind));
            if let Some(reason) = &report.reason {
                lines.push(format!("reason: {:?}", reason));
            }
            lines.extend(report.attempts.iter().map(describe_attempt));
            lines
        }
    }
}

fn describe_attempt(attempt: &IntegrationAttempt) -> String {
    match &attempt.status {
        AttemptStatus::Succeeded => format!(" - {:?}: ok", attempt.strategy),
        AttemptStatus::NotApplicable => format!(" - {:?}: n/a", attempt.strategy),
        AttemptStatus::Failed(reason) => {
            format!(" - {:?}: failed {:?}", attempt.strategy, reason)
        }
        AttemptStatus::HitLimit { size, limit } => {
            format!(
                " - {:?}: skipped size {} > limit {}",
                attempt.strategy, size, limit
            )
        }
    }
}
