//! Symbolic simplification, normalization, and substitution utilities.

mod normalize;
mod rules;
mod substitute;

pub use crate::core::factor::{factor_polynomial, factor_polynomial_expr};
pub use normalize::{normalize, normalize_for_risch};
pub use rules::{
    simplify, simplify_add, simplify_div, simplify_fully, simplify_mul, simplify_neg, simplify_pow,
    simplify_sub, simplify_with_limit,
};
pub use substitute::substitute;
