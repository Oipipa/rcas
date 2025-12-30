use crate::expr::Expr;

use super::linear_parts;
use num_traits::Zero;

pub fn is_rational(expr: &Expr) -> bool {
    match expr {
        Expr::Div(num, den) => {
            if let (Some(_), Some((den_coef, _, _))) = (linear_parts(num), linear_parts(den)) {
                !den_coef.is_zero()
            } else {
                false
            }
        }
        _ => false,
    }
}

pub fn integrate(expr: &Expr, var: &str) -> Option<Expr> {
    if let Expr::Div(num, den) = expr {
        let (num_coef, num_const, num_var) = linear_parts(num)?;
        let (den_coef, den_const, den_var) = linear_parts(den)?;
        if den_coef.is_zero() {
            return None;
        }

        // Require the same variable when both numerator and denominator carry one.
        if (!num_coef.is_zero() && num_var != den_var) || (!num_coef.is_zero() && num_var != var) {
            return None;
        }
        if den_var != var {
            return None;
        }

        let var = if num_coef.is_zero() {
            den_var.clone()
        } else {
            num_var.clone()
        };
        let x = Expr::Variable(var.clone());
        let u = Expr::Add(
            Expr::Mul(Expr::Constant(den_coef.clone()).boxed(), x.clone().boxed()).boxed(),
            Expr::Constant(den_const.clone()).boxed(),
        );
        let a_over_c = Expr::Constant(num_coef.clone() / den_coef.clone());
        let numerator = (num_const * den_coef.clone()) - (num_coef * den_const.clone());
        let k = Expr::Constant(numerator / (den_coef.clone() * den_coef));
        Some(Expr::Add(
            Expr::Mul(a_over_c.boxed(), x.boxed()).boxed(),
            Expr::Mul(k.boxed(), Expr::Log(u.boxed()).boxed()).boxed(),
        ))
    } else {
        None
    }
}
