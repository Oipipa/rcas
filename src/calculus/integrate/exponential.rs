use crate::core::expr::{Expr, Rational};
use crate::core::polynomial::Polynomial;
use crate::simplify::{simplify, simplify_fully};
use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::{coeff_of_var, contains_var, flatten_product, is_polynomial, rebuild_product};

pub fn is_exp(expr: &Expr) -> bool {
    matches!(expr, Expr::Exp(_))
}

pub fn integrate(expr: &Expr, var: &str) -> Option<Expr> {
    match expr {
        Expr::Exp(arg) => integrate_exp_linear(arg, var),
        Expr::Mul(_, _) => integrate_exp_poly_product(expr, var)
            .or_else(|| integrate_exp_trig_product(expr, var)),
        _ => None,
    }
}

pub(crate) fn is_exp_poly_product(expr: &Expr, var: &str) -> bool {
    let Expr::Mul(_, _) = expr else {
        return false;
    };
    let (const_factor, factors) = flatten_product(expr);
    if const_factor.is_zero() {
        return false;
    }

    let mut exp_arg: Option<Expr> = None;
    let mut other_factors = Vec::new();
    for factor in factors {
        match factor {
            Expr::Exp(arg) => {
                if exp_arg.is_some() {
                    return false;
                }
                exp_arg = Some(*arg);
            }
            other => other_factors.push(other),
        }
    }

    let exp_arg = match exp_arg {
        Some(arg) => arg,
        None => return false,
    };
    let poly_expr = rebuild_product(const_factor, other_factors);
    if !is_polynomial(&poly_expr, var) {
        return false;
    }
    coeff_of_var(&exp_arg, var).is_some()
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
            Expr::Exp(arg) => {
                if exp_arg.is_some() {
                    return None;
                }
                exp_arg = Some(*arg);
            }
            Expr::Sin(arg) => {
                if trig.is_some() {
                    return None;
                }
                trig = Some((true, *arg));
            }
            Expr::Cos(arg) => {
                if trig.is_some() {
                    return None;
                }
                trig = Some((false, *arg));
            }
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

fn integrate_exp_poly_product(expr: &Expr, var: &str) -> Option<Expr> {
    let (const_factor, factors) = flatten_product(expr);
    if const_factor.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let mut exp_arg: Option<Expr> = None;
    let mut other_factors = Vec::new();
    for factor in factors {
        match factor {
            Expr::Exp(arg) => {
                if exp_arg.is_some() {
                    return None;
                }
                exp_arg = Some(*arg);
            }
            other => other_factors.push(other),
        }
    }

    let exp_arg = exp_arg?;
    let poly_expr = rebuild_product(const_factor, other_factors);
    if !is_polynomial(&poly_expr, var) {
        return None;
    }

    let coeff = coeff_of_var(&exp_arg, var)?;
    let poly = Polynomial::<Expr>::from_expr(&poly_expr, var)?;
    let degree = poly.degree().unwrap_or(0);
    if poly.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let mut r_coeffs: Vec<Expr> = vec![Expr::Constant(Rational::zero()); degree + 1];
    for k in (0..=degree).rev() {
        let p_k = poly.coeff(k);
        let r_k = if k == degree {
            simplify(Expr::Div(p_k.boxed(), coeff.clone().boxed()))
        } else {
            let factor = Expr::Constant(Rational::from_integer(BigInt::from((k + 1) as i64)));
            let term = simplify(Expr::Mul(factor.boxed(), r_coeffs[k + 1].clone().boxed()));
            let numerator = simplify(Expr::Sub(p_k.boxed(), term.boxed()));
            simplify(Expr::Div(numerator.boxed(), coeff.clone().boxed()))
        };
        r_coeffs[k] = r_k;
    }

    let poly_result = polynomial_expr_from_coeffs(&r_coeffs, var);
    Some(simplify(Expr::Mul(
        Expr::Exp(exp_arg.boxed()).boxed(),
        poly_result.boxed(),
    )))
}

fn polynomial_expr_from_coeffs(coeffs: &[Expr], var: &str) -> Expr {
    let mut terms = Vec::new();
    for (exp, coeff) in coeffs.iter().enumerate() {
        if coeff.is_zero() {
            continue;
        }
        let term = match exp {
            0 => coeff.clone(),
            1 => simplify(Expr::Mul(
                coeff.clone().boxed(),
                Expr::Variable(var.to_string()).boxed(),
            )),
            _ => {
                let power = Expr::Pow(
                    Expr::Variable(var.to_string()).boxed(),
                    Expr::Constant(Rational::from_integer(BigInt::from(exp as i64))).boxed(),
                );
                simplify(Expr::Mul(coeff.clone().boxed(), power.boxed()))
            }
        };
        terms.push(term);
    }
    match terms.len() {
        0 => Expr::Constant(Rational::zero()),
        1 => terms.remove(0),
        _ => terms
            .into_iter()
            .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
            .unwrap(),
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
