//! Calculus routines (differentiation and integration).

pub mod differentiate;
pub mod integrate;

pub use differentiate::differentiate;
pub use integrate::{
    AttemptStatus, IntegrandKind, IntegrandReport, IntegrationAttempt, IntegrationResult,
    NonElementaryKind, ReasonCode, Strategy, integrate,
};
