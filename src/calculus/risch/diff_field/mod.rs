use crate::core::expr::Expr;
use crate::core::polynomial::Polynomial;

mod algebraic;
mod derive;
mod field;
mod poly;
mod tower;
mod utils;

type ExprPoly = Polynomial<Expr>;

pub use field::FieldElement;
pub use tower::{AlgebraicExtension, Extension, ExtensionKind, Tower};
