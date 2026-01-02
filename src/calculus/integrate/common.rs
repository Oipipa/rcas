use crate::core::expr::{Expr, Rational};
use crate::simplify::{simplify, simplify_fully};
use num_traits::{One, Zero};

use super::contains_var;

/// Extract (coefficient, constant) from a linear expression `a*var + b`.
pub fn linear_parts(expr: &Expr, var: &str) -> Option<(Expr, Expr)> {
    if !contains_var(expr, var) {
        return Some((Expr::Constant(Rational::zero()), expr.clone()));
    }

    match expr {
        Expr::Variable(v) if v == var => Some((
            Expr::Constant(Rational::one()),
            Expr::Constant(Rational::zero()),
        )),
        Expr::Neg(inner) => {
            let (coef, constant) = linear_parts(inner, var)?;
            Some((
                simplify(Expr::Neg(coef.boxed())),
                simplify(Expr::Neg(constant.boxed())),
            ))
        }
        Expr::Add(a, b) => {
            let (ca, ka) = linear_parts(a, var)?;
            let (cb, kb) = linear_parts(b, var)?;
            Some((
                simplify(Expr::Add(ca.boxed(), cb.boxed())),
                simplify(Expr::Add(ka.boxed(), kb.boxed())),
            ))
        }
        Expr::Sub(a, b) => {
            let (ca, ka) = linear_parts(a, var)?;
            let (cb, kb) = linear_parts(b, var)?;
            Some((
                simplify(Expr::Sub(ca.boxed(), cb.boxed())),
                simplify(Expr::Sub(ka.boxed(), kb.boxed())),
            ))
        }
        Expr::Mul(a, b) => {
            if !contains_var(a, var) {
                let (cb, kb) = linear_parts(b, var)?;
                Some((
                    simplify(Expr::Mul(a.clone().boxed(), cb.boxed())),
                    simplify(Expr::Mul(a.clone().boxed(), kb.boxed())),
                ))
            } else if !contains_var(b, var) {
                let (ca, ka) = linear_parts(a, var)?;
                Some((
                    simplify(Expr::Mul(b.clone().boxed(), ca.boxed())),
                    simplify(Expr::Mul(b.clone().boxed(), ka.boxed())),
                ))
            } else {
                None
            }
        }
        Expr::Div(a, b) if !contains_var(b, var) => {
            let (ca, ka) = linear_parts(a, var)?;
            Some((
                simplify(Expr::Div(ca.boxed(), b.clone().boxed())),
                simplify(Expr::Div(ka.boxed(), b.clone().boxed())),
            ))
        }
        _ => None,
    }
}

/// Return the coefficient k in a linear term k*var (or var) if the expression is linear in `var`.
pub fn coeff_of_var(expr: &Expr, var: &str) -> Option<Expr> {
    let (coef, _) = linear_parts(expr, var)?;
    if is_zero_expr(&coef) {
        None
    } else {
        Some(coef)
    }
}

fn is_zero_expr(expr: &Expr) -> bool {
    matches!(simplify_fully(expr.clone()), Expr::Constant(c) if c.is_zero())
}
