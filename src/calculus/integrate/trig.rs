use crate::expr::{Expr, Rational};

use super::coeff_of_var;

pub fn is_trig(expr: &Expr) -> bool {
    matches!(expr, Expr::Sin(_) | Expr::Cos(_) | Expr::Tan(_))
}

pub fn integrate(expr: &Expr, var: &str) -> Option<Expr> {
    match expr {
        Expr::Sin(arg) => {
            let k = coeff_of_var(arg, var)?;
            let base = Expr::Neg(Expr::Cos(arg.clone()).boxed());
            Some(if k == Rational::from_integer(1.into()) {
                base
            } else {
                Expr::Div(base.boxed(), Expr::Constant(k).boxed())
            })
        }
        Expr::Cos(arg) => {
            let k = coeff_of_var(arg, var)?;
            Some(if k == Rational::from_integer(1.into()) {
                Expr::Sin(arg.clone())
            } else {
                Expr::Div(Expr::Sin(arg.clone()).boxed(), Expr::Constant(k).boxed())
            })
        }
        Expr::Tan(arg) => {
            let k = coeff_of_var(arg, var)?;
            let base = Expr::Neg(Expr::Log(Expr::Cos(arg.clone()).boxed()).boxed());
            Some(if k == Rational::from_integer(1.into()) {
                base
            } else {
                Expr::Div(base.boxed(), Expr::Constant(k).boxed())
            })
        }
        _ => None,
    }
}
