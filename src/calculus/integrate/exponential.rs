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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ExpTrigKind {
    Sin,
    Cos,
    Sinh,
    Cosh,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ExpTrigFamily {
    Circular,
    Hyperbolic,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ExpTrigTarget {
    Sin,
    Cos,
}

impl ExpTrigKind {
    fn family(self) -> ExpTrigFamily {
        match self {
            ExpTrigKind::Sin | ExpTrigKind::Cos => ExpTrigFamily::Circular,
            ExpTrigKind::Sinh | ExpTrigKind::Cosh => ExpTrigFamily::Hyperbolic,
        }
    }

    fn target(self) -> ExpTrigTarget {
        match self {
            ExpTrigKind::Sin | ExpTrigKind::Sinh => ExpTrigTarget::Sin,
            ExpTrigKind::Cos | ExpTrigKind::Cosh => ExpTrigTarget::Cos,
        }
    }

    fn trig_terms(self, arg: Expr) -> (Expr, Expr) {
        match self.family() {
            ExpTrigFamily::Circular => (
                Expr::Sin(arg.clone().boxed()),
                Expr::Cos(arg.boxed()),
            ),
            ExpTrigFamily::Hyperbolic => (
                Expr::Sinh(arg.clone().boxed()),
                Expr::Cosh(arg.boxed()),
            ),
        }
    }
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
    let mut trig_kind: Option<ExpTrigKind> = None;
    let mut trig_arg: Option<Expr> = None;
    let mut poly_factors = Vec::new();

    for f in var_factors {
        match f {
            Expr::Exp(arg) => {
                if exp_arg.is_some() {
                    return None;
                }
                exp_arg = Some(*arg);
            }
            Expr::Sin(arg) => {
                if trig_kind.is_some() {
                    return None;
                }
                trig_kind = Some(ExpTrigKind::Sin);
                trig_arg = Some(*arg);
            }
            Expr::Cos(arg) => {
                if trig_kind.is_some() {
                    return None;
                }
                trig_kind = Some(ExpTrigKind::Cos);
                trig_arg = Some(*arg);
            }
            Expr::Sinh(arg) => {
                if trig_kind.is_some() {
                    return None;
                }
                trig_kind = Some(ExpTrigKind::Sinh);
                trig_arg = Some(*arg);
            }
            Expr::Cosh(arg) => {
                if trig_kind.is_some() {
                    return None;
                }
                trig_kind = Some(ExpTrigKind::Cosh);
                trig_arg = Some(*arg);
            }
            other => {
                if Polynomial::<Expr>::from_expr(&other, var).is_some() {
                    poly_factors.push(other);
                } else {
                    return None;
                }
            }
        }
    }

    let exp_arg = exp_arg?;
    let trig_kind = trig_kind?;
    let trig_arg = trig_arg?;
    let poly_expr = if poly_factors.is_empty() {
        Expr::Constant(Rational::one())
    } else {
        rebuild_product(Rational::one(), poly_factors)
    };
    let poly = Polynomial::<Expr>::from_expr(&poly_expr, var)?;
    if poly.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let a = coeff_of_var(&exp_arg, var)?;
    let b = coeff_of_var(&trig_arg, var)?;
    let family = trig_kind.family();
    let target = trig_kind.target();
    let denom = exp_trig_denom(&a, &b, family);
    if is_const_zero(&denom) {
        if family == ExpTrigFamily::Hyperbolic {
            if let Some(result) =
                integrate_exp_hyperbolic_decompose(&poly_expr, &exp_arg, &trig_arg, trig_kind, var)
            {
                return Some(scale_by_const(result, const_expr));
            }
        }
        return None;
    }

    let (a_coeffs, b_coeffs) =
        solve_exp_trig_poly_system(&poly, &a, &b, family, target, &denom)?;
    let a_poly = polynomial_expr_from_coeffs(&a_coeffs, var);
    let b_poly = polynomial_expr_from_coeffs(&b_coeffs, var);
    let (sin_term, cos_term) = trig_kind.trig_terms(trig_arg.clone());
    let combo = simplify(Expr::Add(
        Expr::Mul(a_poly.boxed(), sin_term.boxed()).boxed(),
        Expr::Mul(b_poly.boxed(), cos_term.boxed()).boxed(),
    ));
    let base = simplify(Expr::Mul(
        Expr::Exp(exp_arg.clone().boxed()).boxed(),
        combo.boxed(),
    ));
    Some(scale_by_const(base, const_expr))
}

fn exp_trig_denom(a: &Expr, b: &Expr, family: ExpTrigFamily) -> Expr {
    let a_sq = square_expr(a);
    let b_sq = square_expr(b);
    match family {
        ExpTrigFamily::Circular => simplify(Expr::Add(a_sq.boxed(), b_sq.boxed())),
        ExpTrigFamily::Hyperbolic => simplify(Expr::Sub(a_sq.boxed(), b_sq.boxed())),
    }
}

fn solve_exp_trig_poly_system(
    poly: &Polynomial<Expr>,
    a: &Expr,
    b: &Expr,
    family: ExpTrigFamily,
    target: ExpTrigTarget,
    denom: &Expr,
) -> Option<(Vec<Expr>, Vec<Expr>)> {
    let degree = poly.degree().unwrap_or(0);
    let zero = Expr::Constant(Rational::zero());
    let mut a_coeffs = vec![zero.clone(); degree + 2];
    let mut b_coeffs = vec![zero.clone(); degree + 2];
    let sign = match family {
        ExpTrigFamily::Circular => 1,
        ExpTrigFamily::Hyperbolic => -1,
    };

    for k in (0..=degree).rev() {
        let p_k = poly.coeff(k);
        let (mut rhs1, mut rhs2) = match target {
            ExpTrigTarget::Sin => (p_k, zero.clone()),
            ExpTrigTarget::Cos => (zero.clone(), p_k),
        };
        let factor = Expr::Constant(Rational::from_integer(BigInt::from((k + 1) as u64)));
        if !a_coeffs[k + 1].is_zero() {
            let term = simplify(Expr::Mul(factor.clone().boxed(), a_coeffs[k + 1].clone().boxed()));
            rhs1 = simplify(Expr::Sub(rhs1.boxed(), term.boxed()));
        }
        if !b_coeffs[k + 1].is_zero() {
            let term = simplify(Expr::Mul(factor.boxed(), b_coeffs[k + 1].clone().boxed()));
            rhs2 = simplify(Expr::Sub(rhs2.boxed(), term.boxed()));
        }

        let signed_b = if sign == 1 {
            b.clone()
        } else {
            simplify(Expr::Neg(b.clone().boxed()))
        };
        let a_num = simplify(Expr::Add(
            Expr::Mul(a.clone().boxed(), rhs1.clone().boxed()).boxed(),
            Expr::Mul(signed_b.boxed(), rhs2.clone().boxed()).boxed(),
        ));
        let b_num = simplify(Expr::Add(
            Expr::Mul(
                simplify(Expr::Neg(b.clone().boxed())).boxed(),
                rhs1.boxed(),
            )
            .boxed(),
            Expr::Mul(a.clone().boxed(), rhs2.boxed()).boxed(),
        ));

        a_coeffs[k] = simplify(Expr::Div(a_num.boxed(), denom.clone().boxed()));
        b_coeffs[k] = simplify(Expr::Div(b_num.boxed(), denom.clone().boxed()));
    }

    a_coeffs.pop();
    b_coeffs.pop();
    Some((a_coeffs, b_coeffs))
}

fn integrate_exp_hyperbolic_decompose(
    poly_expr: &Expr,
    exp_arg: &Expr,
    trig_arg: &Expr,
    kind: ExpTrigKind,
    var: &str,
) -> Option<Expr> {
    let (add, sub) = match kind {
        ExpTrigKind::Sinh | ExpTrigKind::Cosh => (
            simplify(Expr::Add(exp_arg.clone().boxed(), trig_arg.clone().boxed())),
            simplify(Expr::Sub(exp_arg.clone().boxed(), trig_arg.clone().boxed())),
        ),
        _ => return None,
    };

    let pos_term = integrate_poly_exp_term(poly_expr, &add, var)?;
    let neg_term = integrate_poly_exp_term(poly_expr, &sub, var)?;
    let combined = match kind {
        ExpTrigKind::Sinh => Expr::Sub(pos_term.boxed(), neg_term.boxed()),
        ExpTrigKind::Cosh => Expr::Add(pos_term.boxed(), neg_term.boxed()),
        _ => return None,
    };
    let half = Expr::Constant(Rational::new(1.into(), 2.into()));
    Some(simplify(Expr::Mul(half.boxed(), combined.boxed())))
}

fn integrate_poly_exp_term(poly_expr: &Expr, exp_arg: &Expr, var: &str) -> Option<Expr> {
    if !contains_var(exp_arg, var) {
        let poly_int = super::polynomial::integrate(poly_expr, var)?;
        let exp_term = Expr::Exp(exp_arg.clone().boxed());
        return Some(simplify(Expr::Mul(exp_term.boxed(), poly_int.boxed())));
    }
    let expr = Expr::Mul(
        poly_expr.clone().boxed(),
        Expr::Exp(exp_arg.clone().boxed()).boxed(),
    );
    integrate_exp_poly_product(&expr, var)
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

fn scale_by_const(expr: Expr, const_expr: Expr) -> Expr {
    if is_const_one(&const_expr) {
        expr
    } else {
        simplify(Expr::Mul(const_expr.boxed(), expr.boxed()))
    }
}

fn square_expr(expr: &Expr) -> Expr {
    simplify(Expr::Mul(expr.clone().boxed(), expr.clone().boxed()))
}
