//! Calculus routines (differentiation and integration).

pub mod differentiate;
pub mod integrate;
pub mod risch;

pub use differentiate::differentiate;
pub use integrate::{
    AttemptStatus, IntegrandKind, IntegrandReport, IntegrationAttempt, IntegrationResult,
    NonElementaryKind, ReasonCode, Strategy, integrate,
};
