use crate::expr::{Expr, Rational};
use num_traits::Zero;

#[derive(Clone, Debug)]
enum LinearTerm {
    Var(Rational, String),
    Const(Rational),
}

/// Extract (coefficient, constant, variable) from a linear expression `a*x + b`.
pub fn linear_parts(expr: &Expr) -> Option<(Rational, Rational, String)> {
    match expr {
        Expr::Add(a, b) => {
            let left = as_linear_term(a)?;
            let right = as_linear_term(b)?;
            match (left, right) {
                (LinearTerm::Var(coef, var), LinearTerm::Const(c)) => Some((coef, c, var)),
                (LinearTerm::Const(c), LinearTerm::Var(coef, var)) => Some((coef, c, var)),
                (LinearTerm::Var(c1, v1), LinearTerm::Var(c2, v2)) if v1 == v2 => {
                    Some((c1 + c2, Rational::from_integer(0.into()), v1))
                }
                (LinearTerm::Const(c1), LinearTerm::Const(c2)) => {
                    Some((Rational::from_integer(0.into()), c1 + c2, "x".into()))
                }
                _ => None,
            }
        }
        Expr::Sub(a, b) => {
            let left = as_linear_term(a)?;
            let right = as_linear_term(b)?;
            match (left, right) {
                (LinearTerm::Var(coef, var), LinearTerm::Const(c)) => Some((coef, -c, var)),
                (LinearTerm::Const(c), LinearTerm::Var(coef, var)) => Some((-coef, c, var)),
                (LinearTerm::Var(c1, v1), LinearTerm::Var(c2, v2)) if v1 == v2 => {
                    Some((c1 - c2, Rational::from_integer(0.into()), v1))
                }
                (LinearTerm::Const(c1), LinearTerm::Const(c2)) => {
                    Some((Rational::from_integer(0.into()), c1 - c2, "x".into()))
                }
                _ => None,
            }
        }
        Expr::Neg(inner) => {
            let (coef, constant, var) = linear_parts(inner)?;
            Some((-coef, -constant, var))
        }
        Expr::Mul(a, b) => {
            const_var(a, b).map(|(coef, var)| (coef, Rational::from_integer(0.into()), var))
        }
        Expr::Variable(v) => Some((
            Rational::from_integer(1.into()),
            Rational::from_integer(0.into()),
            v.clone(),
        )),
        Expr::Constant(c) => Some((Rational::from_integer(0.into()), c.clone(), "x".into())),
        _ => None,
    }
}

/// Return the coefficient k in a linear term k*var (or var) if the expression is linear in `var`.
pub fn coeff_of_var(expr: &Expr, var: &str) -> Option<Rational> {
    if let Some((coef, _, v)) = linear_parts(expr) {
        if v == var && !coef.is_zero() {
            return Some(coef);
        }
    }
    None
}

fn as_linear_term(expr: &Expr) -> Option<LinearTerm> {
    if let Some((coef, var)) = mul_const_var(expr) {
        return Some(LinearTerm::Var(coef, var));
    }
    match expr {
        Expr::Variable(v) => Some(LinearTerm::Var(Rational::from_integer(1.into()), v.clone())),
        Expr::Constant(c) => Some(LinearTerm::Const(c.clone())),
        _ => None,
    }
}

fn mul_const_var(expr: &Expr) -> Option<(Rational, String)> {
    if let Expr::Mul(a, b) = expr {
        const_var(a, b)
    } else {
        None
    }
}

fn const_var(a: &Expr, b: &Expr) -> Option<(Rational, String)> {
    match (a, b) {
        (Expr::Constant(c), Expr::Variable(v)) => Some((c.clone(), v.clone())),
        (Expr::Variable(v), Expr::Constant(c)) => Some((c.clone(), v.clone())),
        _ => None,
    }
}
