use std::collections::BTreeMap;

use crate::expr::{Expr, Rational};
use crate::simplify::simplify;
use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::{contains_var, log_abs};

pub fn is_polynomial(expr: &Expr, var: &str) -> bool {
    matches!(detect_form(expr, var), Some(_))
}

pub fn integrate(expr: &Expr, var: &str) -> Option<Expr> {
    match detect_form(expr, var)? {
        PolynomialForm::Polynomial(poly) => Some(poly.integrate(var)),
        PolynomialForm::LinearPower {
            constant_factor,
            coeff,
            constant,
            exponent,
        } => integrate_linear_power(&constant_factor, &coeff, &constant, &exponent, var),
    }
}

fn detect_form(expr: &Expr, var: &str) -> Option<PolynomialForm> {
    if let Some(poly) = Polynomial::from_expr(expr, var) {
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
    Polynomial(Polynomial),
    LinearPower {
        constant_factor: Expr,
        coeff: Expr,
        constant: Expr,
        exponent: Rational,
    },
}

#[derive(Clone, Debug)]
struct Polynomial {
    terms: BTreeMap<BigInt, Expr>,
}

impl Polynomial {
    fn zero() -> Self {
        Polynomial {
            terms: BTreeMap::new(),
        }
    }

    fn one() -> Self {
        let mut terms = BTreeMap::new();
        terms.insert(BigInt::zero(), Expr::Constant(Rational::one()));
        Polynomial { terms }
    }

    fn from_expr(expr: &Expr, var: &str) -> Option<Self> {
        if !contains_var(expr, var) {
            return Some(Polynomial::from_constant(expr.clone()));
        }

        match expr {
            Expr::Variable(name) if name == var => {
                let mut terms = BTreeMap::new();
                terms.insert(BigInt::one(), Expr::Constant(Rational::one()));
                Some(Polynomial { terms })
            }
            Expr::Neg(inner) => {
                let poly = Polynomial::from_expr(inner, var)?;
                Some(poly.scale(&Expr::Constant(-Rational::one())))
            }
            Expr::Add(a, b) => {
                let left = Polynomial::from_expr(a, var)?;
                let right = Polynomial::from_expr(b, var)?;
                Some(left.add(&right))
            }
            Expr::Sub(a, b) => {
                let left = Polynomial::from_expr(a, var)?;
                let right = Polynomial::from_expr(b, var)?;
                Some(left.sub(&right))
            }
            Expr::Mul(a, b) => {
                let left = Polynomial::from_expr(a, var)?;
                let right = Polynomial::from_expr(b, var)?;
                Some(left.mul(&right))
            }
            Expr::Div(a, b) if !contains_var(b, var) => {
                let numer = Polynomial::from_expr(a, var)?;
                let scale = Expr::Div(Expr::Constant(Rational::one()).boxed(), b.clone().boxed());
                Some(numer.scale(&scale))
            }
            Expr::Pow(base, exp) => {
                let exponent = extract_rational(exp)?;
                if !exponent.is_integer() || exponent < Rational::zero() {
                    return None;
                }
                let power = exponent.to_integer();
                let base_poly = Polynomial::from_expr(base, var)?;
                Some(base_poly.pow(&power))
            }
            _ => None,
        }
    }

    fn from_constant(expr: Expr) -> Self {
        let mut terms = BTreeMap::new();
        terms.insert(BigInt::zero(), expr);
        Polynomial { terms }
    }

    fn add(&self, other: &Self) -> Self {
        let mut result = self.terms.clone();
        for (exp, coeff) in &other.terms {
            let key = exp.clone();
            let existing = result
                .get(&key)
                .cloned()
                .unwrap_or_else(|| Expr::Constant(Rational::zero()));
            let updated = simplify(Expr::Add(existing.boxed(), coeff.clone().boxed()));
            if is_zero_coeff(&updated) {
                result.remove(&key);
            } else {
                result.insert(key, updated);
            }
        }
        Polynomial { terms: result }
    }

    fn sub(&self, other: &Self) -> Self {
        let negated = other.scale(&Expr::Constant(-Rational::one()));
        self.add(&negated)
    }

    fn mul(&self, other: &Self) -> Self {
        let mut result = BTreeMap::new();
        for (exp_a, coeff_a) in &self.terms {
            for (exp_b, coeff_b) in &other.terms {
                let key = exp_a + exp_b;
                let coeff = simplify(Expr::Mul(coeff_a.clone().boxed(), coeff_b.clone().boxed()));
                let existing = result
                    .get(&key)
                    .cloned()
                    .unwrap_or_else(|| Expr::Constant(Rational::zero()));
                let updated = simplify(Expr::Add(existing.boxed(), coeff.boxed()));
                if is_zero_coeff(&updated) {
                    result.remove(&key);
                } else {
                    result.insert(key, updated);
                }
            }
        }
        Polynomial { terms: result }
    }

    fn pow(&self, exp: &BigInt) -> Self {
        if exp.is_zero() {
            return Polynomial::one();
        }
        let mut result = Polynomial::one();
        let mut base = self.clone();
        let mut n = exp.clone();
        while n > BigInt::zero() {
            if (&n & BigInt::one()) == BigInt::one() {
                result = result.mul(&base);
            }
            base = base.mul(&base);
            n >>= 1;
        }
        result
    }

    fn scale(&self, factor: &Expr) -> Self {
        if is_zero_coeff(factor) {
            return Polynomial::zero();
        }
        let mut terms = BTreeMap::new();
        for (exp, coeff) in &self.terms {
            let scaled = simplify(Expr::Mul(coeff.clone().boxed(), factor.clone().boxed()));
            if !is_zero_coeff(&scaled) {
                terms.insert(exp.clone(), scaled);
            }
        }
        Polynomial { terms }
    }

    fn integrate(&self, var: &str) -> Expr {
        let mut terms: Vec<Expr> = Vec::new();
        for (exp, coeff) in &self.terms {
            let next = exp + BigInt::one();
            let denom = Expr::Constant(Rational::from_integer(next.clone()));
            let power = Expr::Pow(
                Expr::Variable(var.to_string()).boxed(),
                denom.clone().boxed(),
            );
            let numerator = Expr::Mul(coeff.clone().boxed(), power.boxed());
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

fn linear_parts(expr: &Expr, var: &str) -> Option<(Expr, Expr)> {
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
