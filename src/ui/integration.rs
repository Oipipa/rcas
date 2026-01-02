use crate::calculus::integrate::IntegrationResult;

use super::pretty;

/// Render an `IntegrationResult` into a single-line summary.
pub fn integration_summary(result: &IntegrationResult) -> String {
    match result {
        IntegrationResult::Integrated { result, .. } => pretty(result),
        IntegrationResult::NotIntegrable(_) => "antiderivative could not be computed".to_string(),
    }
}
