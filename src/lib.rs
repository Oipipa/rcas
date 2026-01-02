//! Lightweight computer algebra system primitives for parsing, manipulating, and solving
//! mathematical expressions.

pub mod calculus;
pub mod core;
pub mod prelude;
pub mod simplify;
pub mod solver;
pub mod ui;

pub use calculus::{
    AttemptStatus, IntegrandKind, IntegrandReport, IntegrationAttempt, IntegrationResult,
    NonElementaryKind, ReasonCode, Strategy, differentiate, integrate,
};
pub use crate::calculus::risch::diff_field;
pub use crate::core::{error, expr, factor, parser, polynomial};
pub use diff_field::{Extension, ExtensionKind, FieldElement, Tower};
pub use crate::core::error::{CasError, Result};
pub use crate::core::expr::{Expr, Rational, add, div, mul, neg, one, pow, rational, sub, zero};
pub use crate::core::factor::{Factor, Factorization, factor_polynomial, factor_polynomial_expr};
pub use crate::core::parser::parse_expr;
pub use crate::core::polynomial::Poly;
pub use ui::{pretty, integration_summary, solve_summary};
pub use simplify::{normalize, simplify, simplify_fully, simplify_with_limit, substitute};
pub use solver::{
    LinearDiagnostics, LinearFamily, LinearInconsistent, LinearResult, LinearSolution,
    NonLinearResult, NonLinearStatus, SolveResult, solve_system,
};
