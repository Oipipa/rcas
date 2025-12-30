use crate::expr::{Expr, Rational};

use super::coeff_of_var;

pub fn is_exp(expr: &Expr) -> bool {
    matches!(expr, Expr::Exp(_))
}

pub fn integrate(expr: &Expr, var: &str) -> Option<Expr> {
    match expr {
        Expr::Exp(arg) => {
            let k = coeff_of_var(arg, var)?;
            Some(if k == Rational::from_integer(1.into()) {
                Expr::Exp(arg.clone())
            } else {
                Expr::Div(Expr::Exp(arg.clone()).boxed(), Expr::Constant(k).boxed())
            })
        }
        _ => None,
    }
}
