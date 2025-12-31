use crate::expr::{Expr, Rational};
use crate::polynomial::Polynomial;
use crate::simplify::simplify;
use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::{contains_var, linear_parts, log_abs};

pub fn is_polynomial(expr: &Expr, var: &str) -> bool {
    matches!(detect_form(expr, var), Some(_))
}

pub(crate) fn degree(expr: &Expr, var: &str) -> Option<usize> {
    let poly = ExprPolynomial::from_expr(expr, var)?;
    Some(poly.degree().unwrap_or(0))
}

pub fn integrate(expr: &Expr, var: &str) -> Option<Expr> {
    match detect_form(expr, var)? {
        PolynomialForm::Polynomial(poly) => Some(integrate_polynomial(&poly, var)),
        PolynomialForm::LinearPower {
            constant_factor,
            coeff,
            constant,
            exponent,
        } => integrate_linear_power(&constant_factor, &coeff, &constant, &exponent, var),
    }
}

fn detect_form(expr: &Expr, var: &str) -> Option<PolynomialForm> {
    if let Some(poly) = ExprPolynomial::from_expr(expr, var) {
        return Some(PolynomialForm::Polynomial(poly));
    }
    detect_linear_power(expr, var).map(|(constant_factor, coeff, constant, exponent)| {
        PolynomialForm::LinearPower {
            constant_factor,
            coeff,
            constant,
            exponent,
        }
    })
}

fn detect_linear_power(expr: &Expr, var: &str) -> Option<(Expr, Expr, Expr, Rational)> {
    let (constant_factor, core) = split_constant_factor(expr, var);
    let (base, exponent) = match &core {
        Expr::Pow(base, exp) => (&**base, extract_rational(exp)?),
        other => (other, Rational::one()),
    };

    let (coeff, constant) = linear_parts(base, var)?;
    if is_zero_coeff(&coeff) {
        return None;
    }

    Some((constant_factor, coeff, constant, exponent))
}

fn integrate_linear_power(
    constant_factor: &Expr,
    coeff: &Expr,
    constant: &Expr,
    exponent: &Rational,
    var: &str,
) -> Option<Expr> {
    if *exponent == -Rational::one() {
        let base = linear_expr(coeff, constant, var);
        let scale = simplify(Expr::Div(
            constant_factor.clone().boxed(),
            coeff.clone().boxed(),
        ));
        return Some(Expr::Mul(scale.boxed(), log_abs(base).boxed()));
    }

    let next = exponent + Rational::one();
    let base = linear_expr(coeff, constant, var);
    let powered = Expr::Pow(base.boxed(), Expr::Constant(next.clone()).boxed());
    let numerator = simplify(Expr::Mul(constant_factor.clone().boxed(), powered.boxed()));
    let denom = simplify(Expr::Mul(
        coeff.clone().boxed(),
        Expr::Constant(next).boxed(),
    ));

    Some(Expr::Div(numerator.boxed(), denom.boxed()))
}

#[derive(Clone, Debug)]
enum PolynomialForm {
    Polynomial(ExprPolynomial),
    LinearPower {
        constant_factor: Expr,
        coeff: Expr,
        constant: Expr,
        exponent: Rational,
    },
}

type ExprPolynomial = Polynomial<Expr>;

fn integrate_polynomial(poly: &ExprPolynomial, var: &str) -> Expr {
    let mut terms: Vec<Expr> = Vec::new();
    for (exp, coeff) in poly.coeff_entries() {
        let next = exp + 1;
        let denom = Expr::Constant(Rational::from_integer(BigInt::from(next as u64)));
        let power = Expr::Pow(
            Expr::Variable(var.to_string()).boxed(),
            denom.clone().boxed(),
        );
        let numerator = Expr::Mul(coeff.boxed(), power.boxed());
        terms.push(Expr::Div(numerator.boxed(), denom.boxed()));
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

fn extract_rational(expr: &Expr) -> Option<Rational> {
    match expr {
        Expr::Constant(n) => Some(n.clone()),
        Expr::Neg(inner) => match &**inner {
            Expr::Constant(n) => Some(-n.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn split_constant_factor(expr: &Expr, var: &str) -> (Expr, Expr) {
    match expr {
        Expr::Mul(a, b) => {
            let (ca, ra) = split_constant_factor(a, var);
            let (cb, rb) = split_constant_factor(b, var);
            let constant = multiply_if_needed(ca, cb);
            let rest = multiply_if_needed(ra, rb);
            (constant, rest)
        }
        _ if !contains_var(expr, var) => (expr.clone(), Expr::Constant(Rational::one())),
        _ => (Expr::Constant(Rational::one()), expr.clone()),
    }
}

fn multiply_if_needed(a: Expr, b: Expr) -> Expr {
    if matches!(a, Expr::Constant(ref c) if c.is_one()) {
        b
    } else if matches!(b, Expr::Constant(ref c) if c.is_one()) {
        a
    } else {
        Expr::Mul(a.boxed(), b.boxed())
    }
}

fn linear_expr(coeff: &Expr, constant: &Expr, var: &str) -> Expr {
    Expr::Add(
        Expr::Mul(
            coeff.clone().boxed(),
            Expr::Variable(var.to_string()).boxed(),
        )
        .boxed(),
        constant.clone().boxed(),
    )
}

fn is_zero_coeff(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(c) if c.is_zero())
}
