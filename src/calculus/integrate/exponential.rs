use crate::expr::{Expr, Rational};
use crate::simplify::{simplify, simplify_fully};
use num_traits::{One, Zero};

use super::{coeff_of_var, contains_var, flatten_product, rebuild_product};

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
    Some(scale_by_coeff(Expr::Exp(arg.clone().boxed()), k))
}

fn integrate_exp_trig_product(expr: &Expr, var: &str) -> Option<Expr> {
    let (const_factor, factors) = flatten_product(expr);
    if const_factor.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }
    let mut const_factors = Vec::new();
    let mut var_factors = Vec::new();
    for factor in factors {
        if contains_var(&factor, var) {
            var_factors.push(factor);
        } else {
            const_factors.push(factor);
        }
    }
    let const_expr = rebuild_product(const_factor, const_factors);

    let mut exp_arg: Option<Expr> = None;
    let mut trig: Option<(bool, Expr)> = None;

    for f in var_factors {
        match f {
            Expr::Exp(arg) => exp_arg = Some(*arg),
            Expr::Sin(arg) => trig = Some((true, *arg)),
            Expr::Cos(arg) => trig = Some((false, *arg)),
            _ => return None,
        }
    }

    let (is_sin, trig_arg) = trig?;
    let exp_arg = exp_arg?;
    let a = coeff_of_var(&exp_arg, var)?;
    let b = coeff_of_var(&trig_arg, var)?;
    let denom = simplify(Expr::Add(square_expr(&a).boxed(), square_expr(&b).boxed()));
    if is_const_zero(&denom) {
        return None;
    }

    let trig_part = if is_sin {
        Expr::Sub(
            Expr::Mul(
                a.clone().boxed(),
                Expr::Sin(trig_arg.clone().boxed()).boxed(),
            )
            .boxed(),
            Expr::Mul(
                b.clone().boxed(),
                Expr::Cos(trig_arg.clone().boxed()).boxed(),
            )
            .boxed(),
        )
    } else {
        Expr::Add(
            Expr::Mul(
                a.clone().boxed(),
                Expr::Cos(trig_arg.clone().boxed()).boxed(),
            )
            .boxed(),
            Expr::Mul(
                b.clone().boxed(),
                Expr::Sin(trig_arg.clone().boxed()).boxed(),
            )
            .boxed(),
        )
    };

    let exp_term = Expr::Exp(exp_arg.clone().boxed());
    let numerator = Expr::Mul(exp_term.boxed(), trig_part.boxed());
    let result = Expr::Div(numerator.boxed(), denom.boxed());
    if is_const_one(&const_expr) {
        Some(simplify(result))
    } else {
        Some(simplify(Expr::Mul(const_expr.boxed(), result.boxed())))
    }
}

fn is_const_one(expr: &Expr) -> bool {
    matches!(simplify_fully(expr.clone()), Expr::Constant(c) if c.is_one())
}

fn is_const_zero(expr: &Expr) -> bool {
    matches!(simplify_fully(expr.clone()), Expr::Constant(c) if c.is_zero())
}

fn invert_coeff(expr: Expr) -> Expr {
    match expr {
        Expr::Constant(c) => Expr::Constant(Rational::one() / c),
        Expr::Neg(inner) => Expr::Neg(invert_coeff(*inner).boxed()),
        Expr::Div(num, den) => Expr::Div(den, num),
        Expr::Pow(base, exp) => match &*exp {
            Expr::Constant(k) => Expr::Pow(base, Expr::Constant(-k.clone()).boxed()),
            _ => Expr::Div(
                Expr::Constant(Rational::one()).boxed(),
                Expr::Pow(base, exp).boxed(),
            ),
        },
        other => Expr::Div(Expr::Constant(Rational::one()).boxed(), other.boxed()),
    }
}

fn scale_by_coeff(expr: Expr, coeff: Expr) -> Expr {
    if is_const_one(&coeff) {
        expr
    } else {
        simplify(Expr::Mul(expr.boxed(), invert_coeff(coeff).boxed()))
    }
}

fn square_expr(expr: &Expr) -> Expr {
    simplify(Expr::Mul(expr.clone().boxed(), expr.clone().boxed()))
}
