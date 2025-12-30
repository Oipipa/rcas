//! Lightweight computer algebra system primitives for parsing, manipulating, and solving
//! mathematical expressions.

pub mod calculus;
pub mod error;
pub mod expr;
pub mod format;
pub mod parser;
pub mod simplify;
pub mod solver;

pub use calculus::{
    AttemptStatus, IntegrandKind, IntegrandReport, IntegrationAttempt, IntegrationResult,
    NonElementaryKind, ReasonCode, Strategy, differentiate, integrate,
};
pub use error::{CasError, Result};
pub use expr::{Expr, Rational, add, div, mul, neg, one, pow, rational, sub, zero};
pub use format::{pretty, pretty_integration_result, pretty_solve_result};
pub use parser::parse_expr;
pub use simplify::{normalize, simplify, simplify_fully, simplify_with_limit, substitute};
pub use solver::{
    LinearDiagnostics, LinearFamily, LinearInconsistent, LinearResult, LinearSolution,
    NonLinearResult, NonLinearStatus, SolveResult, solve_system,
};
