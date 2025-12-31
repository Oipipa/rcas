use crate::expr::{Expr, Rational};
use crate::simplify::simplify;
use num_traits::Zero;

use super::{coeff_of_var, flatten_product};

pub fn is_exp(expr: &Expr) -> bool {
    matches!(expr, Expr::Exp(_))
}

pub fn integrate(expr: &Expr, var: &str) -> Option<Expr> {
    match expr {
        Expr::Exp(arg) => integrate_exp_linear(arg, var),
        Expr::Mul(_, _) => integrate_exp_trig_product(expr, var),
        _ => None,
    }
}

fn integrate_exp_linear(arg: &Expr, var: &str) -> Option<Expr> {
    let k = coeff_of_var(arg, var)?;
    Some(if k == Rational::from_integer(1.into()) {
        Expr::Exp(arg.clone().boxed())
    } else {
        Expr::Div(Expr::Exp(arg.clone().boxed()).boxed(), Expr::Constant(k).boxed())
    })
}

fn integrate_exp_trig_product(expr: &Expr, var: &str) -> Option<Expr> {
    let (const_factor, factors) = flatten_product(expr);
    if const_factor.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let mut exp_arg: Option<Expr> = None;
    let mut trig: Option<(bool, Expr)> = None;

    for f in factors {
        match f {
            Expr::Exp(arg) => exp_arg = Some(*arg),
            Expr::Sin(arg) => trig = Some((true, *arg)),
            Expr::Cos(arg) => trig = Some((false, *arg)),
            Expr::Constant(_) => {}
            _ => return None,
        }
    }

    let (is_sin, trig_arg) = trig?;
    let exp_arg = exp_arg?;
    let a = coeff_of_var(&exp_arg, var)?;
    let b = coeff_of_var(&trig_arg, var)?;
    let denom = a.clone() * a.clone() + b.clone() * b.clone();
    if denom.is_zero() {
        return None;
    }

    let trig_part = if is_sin {
        Expr::Sub(
            Expr::Mul(
                Expr::Constant(a.clone()).boxed(),
                Expr::Sin(trig_arg.clone().boxed()).boxed(),
            )
            .boxed(),
            Expr::Mul(
                Expr::Constant(b.clone()).boxed(),
                Expr::Cos(trig_arg.clone().boxed()).boxed(),
            )
            .boxed(),
        )
    } else {
        Expr::Add(
            Expr::Mul(
                Expr::Constant(a.clone()).boxed(),
                Expr::Cos(trig_arg.clone().boxed()).boxed(),
            )
            .boxed(),
            Expr::Mul(
                Expr::Constant(b.clone()).boxed(),
                Expr::Sin(trig_arg.clone().boxed()).boxed(),
            )
            .boxed(),
        )
    };

    let exp_term = Expr::Exp(exp_arg.clone().boxed());
    let numerator = Expr::Mul(exp_term.boxed(), trig_part.boxed());
    let result = Expr::Div(numerator.boxed(), Expr::Constant(denom).boxed());
    if const_factor == Rational::from_integer(1.into()) {
        Some(simplify(result))
    } else {
        Some(simplify(Expr::Mul(
            Expr::Constant(const_factor).boxed(),
            result.boxed(),
        )))
    }
}
