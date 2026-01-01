use crate::expr::{Expr, Rational};
use crate::simplify::{simplify, simplify_fully};
use num_traits::{One, ToPrimitive, Zero};
use num_bigint::BigInt;

use super::{coeff_of_var, contains_var, flatten_product, linear_parts, log_abs, rebuild_product};

pub fn is_trig(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Sin(_)
            | Expr::Cos(_)
            | Expr::Tan(_)
            | Expr::Sec(_)
            | Expr::Csc(_)
            | Expr::Cot(_)
            | Expr::Atan(_)
            | Expr::Asin(_)
            | Expr::Acos(_)
            | Expr::Asec(_)
            | Expr::Acsc(_)
            | Expr::Acot(_)
            | Expr::Sinh(_)
            | Expr::Cosh(_)
            | Expr::Tanh(_)
            | Expr::Asinh(_)
            | Expr::Acosh(_)
            | Expr::Atanh(_)
    )
}

pub fn integrate(expr: &Expr, var: &str) -> Option<Expr> {
    match expr {
        Expr::Sin(arg) => {
            let k = coeff_of_var(arg, var)?;
            let base = Expr::Neg(Expr::Cos(arg.clone().boxed()).boxed());
            Some(scale_by_coeff(base, k))
        }
        Expr::Cos(arg) => {
            let k = coeff_of_var(arg, var)?;
            Some(scale_by_coeff(Expr::Sin(arg.clone().boxed()), k))
        }
        Expr::Tan(arg) => integrate_tan(arg, var),
        Expr::Sec(arg) => integrate_sec(arg, var),
        Expr::Csc(arg) => integrate_csc(arg, var),
        Expr::Cot(arg) => integrate_cot(arg, var),
        Expr::Sinh(arg) => integrate_sinh(arg, var),
        Expr::Cosh(arg) => integrate_cosh(arg, var),
        Expr::Tanh(arg) => integrate_tanh(arg, var),
        Expr::Pow(base, exp) => match (&**base, &**exp) {
            (Expr::Sin(inner), Expr::Constant(p)) if p.is_integer() && p >= &Rational::zero() => {
                integrate_sin_power(inner, p, var)
            }
            (Expr::Cos(inner), Expr::Constant(p)) if p.is_integer() && p >= &Rational::zero() => {
                integrate_cos_power(inner, p, var)
            }
            (Expr::Sec(inner), Expr::Constant(p)) if p == &Rational::from_integer(2.into()) => {
                integrate_sec_squared(inner, var)
            }
            (Expr::Csc(inner), Expr::Constant(p)) if p == &Rational::from_integer(2.into()) => {
                integrate_csc_squared(inner, var)
            }
            _ => None,
        },
        Expr::Mul(_, _) => integrate_sin_cos_product(expr, var),
        Expr::Asin(arg) => integrate_arcsin(arg, var),
        Expr::Acos(arg) => integrate_arccos(arg, var),
        Expr::Atan(arg) => integrate_arctan(arg, var),
        Expr::Asec(arg) => integrate_arcsec(arg, var),
        Expr::Acsc(arg) => integrate_arccsc(arg, var),
        Expr::Acot(arg) => integrate_arccot(arg, var),
        Expr::Asinh(arg) => integrate_asinh(arg, var),
        Expr::Acosh(arg) => integrate_acosh(arg, var),
        Expr::Atanh(arg) => integrate_atanh(arg, var),
        _ => None,
    }
}

fn integrate_tan(arg: &Expr, var: &str) -> Option<Expr> {
    let k = coeff_of_var(arg, var)?;
    let base = Expr::Neg(log_abs(Expr::Cos(arg.clone().boxed())).boxed());
    Some(scale_by_coeff(base, k))
}

fn integrate_sec(arg: &Expr, var: &str) -> Option<Expr> {
    let k = coeff_of_var(arg, var)?;
    let sum = Expr::Add(
        Expr::Sec(arg.clone().boxed()).boxed(),
        Expr::Tan(arg.clone().boxed()).boxed(),
    );
    let base = log_abs(sum);
    Some(scale_by_coeff(base, k))
}

fn integrate_csc(arg: &Expr, var: &str) -> Option<Expr> {
    let k = coeff_of_var(arg, var)?;
    let diff = Expr::Sub(
        Expr::Csc(arg.clone().boxed()).boxed(),
        Expr::Cot(arg.clone().boxed()).boxed(),
    );
    let base = log_abs(diff);
    Some(scale_by_coeff(base, k))
}

fn integrate_cot(arg: &Expr, var: &str) -> Option<Expr> {
    let k = coeff_of_var(arg, var)?;
    let base = log_abs(Expr::Sin(arg.clone().boxed()));
    Some(scale_by_coeff(base, k))
}

fn integrate_sinh(arg: &Expr, var: &str) -> Option<Expr> {
    let k = coeff_of_var(arg, var)?;
    Some(scale_by_coeff(Expr::Cosh(arg.clone().boxed()), k))
}

fn integrate_cosh(arg: &Expr, var: &str) -> Option<Expr> {
    let k = coeff_of_var(arg, var)?;
    Some(scale_by_coeff(Expr::Sinh(arg.clone().boxed()), k))
}

fn integrate_tanh(arg: &Expr, var: &str) -> Option<Expr> {
    let k = coeff_of_var(arg, var)?;
    let base = log_abs(Expr::Cosh(arg.clone().boxed()));
    Some(scale_by_coeff(base, k))
}

fn integrate_sec_squared(inner: &Expr, var: &str) -> Option<Expr> {
    let k = coeff_of_var(inner, var)?;
    Some(scale_by_coeff(Expr::Tan(inner.clone().boxed()), k))
}

fn integrate_csc_squared(inner: &Expr, var: &str) -> Option<Expr> {
    let k = coeff_of_var(inner, var)?;
    let base = Expr::Neg(Expr::Cot(inner.clone().boxed()).boxed());
    Some(scale_by_coeff(base, k))
}

fn pow_to_i64(p: &Rational) -> Option<i64> {
    if !p.is_integer() || p < &Rational::zero() {
        return None;
    }
    p.to_integer().to_i64()
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

fn scale_by_coeff(expr: Expr, k: Expr) -> Expr {
    if is_const_one(&k) {
        expr
    } else {
        simplify(Expr::Mul(expr.boxed(), invert_coeff(k).boxed()))
    }
}

fn integrate_sin_power(inner: &Expr, power: &Rational, var: &str) -> Option<Expr> {
    let n = pow_to_i64(power)?;
    let k = coeff_of_var(inner, var)?;
    let integral = sin_power_reduction(n, inner)?;
    Some(scale_by_coeff(integral, k))
}

fn integrate_cos_power(inner: &Expr, power: &Rational, var: &str) -> Option<Expr> {
    let n = pow_to_i64(power)?;
    let k = coeff_of_var(inner, var)?;
    let integral = cos_power_reduction(n, inner)?;
    Some(scale_by_coeff(integral, k))
}

fn sin_power_reduction(n: i64, inner: &Expr) -> Option<Expr> {
    if n < 0 {
        return None;
    }
    if n == 0 {
        return Some(inner.clone());
    }
    if n == 1 {
        return Some(Expr::Neg(Expr::Cos(inner.clone().boxed()).boxed()));
    }
    if n == 3 {
        let cos_inner = Expr::Cos(inner.clone().boxed());
        let cos_cubed = Expr::Pow(
            cos_inner.clone().boxed(),
            Expr::Constant(Rational::from_integer(3.into())).boxed(),
        );
        return Some(Expr::Add(
            Expr::Neg(cos_inner.boxed()).boxed(),
            Expr::Mul(
                Expr::Constant(Rational::new(1.into(), 3.into())).boxed(),
                cos_cubed.boxed(),
            )
            .boxed(),
        ));
    }
    let n_r = Rational::from_integer(n.into());
    let n_minus_one = Rational::from_integer((n - 1).into());
    let leading = Expr::Div(
        Expr::Mul(
            Expr::Neg(Expr::Cos(inner.clone().boxed()).boxed()).boxed(),
            Expr::Pow(
                Expr::Sin(inner.clone().boxed()).boxed(),
                Expr::Constant(n_minus_one.clone()).boxed(),
            )
            .boxed(),
        )
        .boxed(),
        Expr::Constant(n_r.clone()).boxed(),
    );
    let reduced = sin_power_reduction(n - 2, inner)?;
    let scaled = Expr::Mul(
        Expr::Constant(n_minus_one / n_r.clone()).boxed(),
        reduced.boxed(),
    );
    Some(simplify(Expr::Add(leading.boxed(), scaled.boxed())))
}

fn cos_power_reduction(n: i64, inner: &Expr) -> Option<Expr> {
    if n < 0 {
        return None;
    }
    if n == 0 {
        return Some(inner.clone());
    }
    if n == 1 {
        return Some(Expr::Sin(inner.clone().boxed()));
    }
    if n == 3 {
        let sin_inner = Expr::Sin(inner.clone().boxed());
        let sin_cubed = Expr::Pow(
            sin_inner.clone().boxed(),
            Expr::Constant(Rational::from_integer(3.into())).boxed(),
        );
        return Some(Expr::Sub(
            sin_inner.boxed(),
            Expr::Mul(
                Expr::Constant(Rational::new(1.into(), 3.into())).boxed(),
                sin_cubed.boxed(),
            )
            .boxed(),
        ));
    }
    let n_r = Rational::from_integer(n.into());
    let n_minus_one = Rational::from_integer((n - 1).into());
    let leading = Expr::Div(
        Expr::Mul(
            Expr::Sin(inner.clone().boxed()).boxed(),
            Expr::Pow(
                Expr::Cos(inner.clone().boxed()).boxed(),
                Expr::Constant(n_minus_one.clone()).boxed(),
            )
            .boxed(),
        )
        .boxed(),
        Expr::Constant(n_r.clone()).boxed(),
    );
    let reduced = cos_power_reduction(n - 2, inner)?;
    let scaled = Expr::Mul(
        Expr::Constant(n_minus_one / n_r.clone()).boxed(),
        reduced.boxed(),
    );
    Some(simplify(Expr::Add(leading.boxed(), scaled.boxed())))
}

fn integrate_sin_cos_product(expr: &Expr, var: &str) -> Option<Expr> {
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
    let mut sin_exp = 0_i64;
    let mut cos_exp = 0_i64;
    let mut inner: Option<Expr> = None;

    for factor in var_factors {
        match factor {
            Expr::Sin(arg) => {
                inner = match inner {
                    None => Some(*arg.clone()),
                    Some(ref existing) if *existing == *arg => Some(existing.clone()),
                    _ => return None,
                };
                sin_exp += 1;
            }
            Expr::Cos(arg) => {
                inner = match inner {
                    None => Some(*arg.clone()),
                    Some(ref existing) if *existing == *arg => Some(existing.clone()),
                    _ => return None,
                };
                cos_exp += 1;
            }
            Expr::Pow(base, exp) => match (&*base, &*exp) {
                (Expr::Sin(arg), Expr::Constant(p)) if p.is_integer() && p >= &Rational::zero() => {
                    inner = match inner {
                        None => Some(*arg.clone()),
                        Some(ref existing) if *existing == **arg => Some(existing.clone()),
                        _ => return None,
                    };
                    sin_exp += pow_to_i64(p)?;
                }
                (Expr::Cos(arg), Expr::Constant(p)) if p.is_integer() && p >= &Rational::zero() => {
                    inner = match inner {
                        None => Some(*arg.clone()),
                        Some(ref existing) if *existing == **arg => Some(existing.clone()),
                        _ => return None,
                    };
                    cos_exp += pow_to_i64(p)?;
                }
                _ => return None,
            },
            Expr::Constant(_) => {}
            _ => return None,
        }
    }

    let inner = inner?;
    let k = coeff_of_var(&inner, var)?;
    let combined = integrate_sin_cos_powers(sin_exp, cos_exp, &inner, k)?;
    let scaled = simplify(combined);
    if is_const_one(&const_expr) {
        Some(scaled)
    } else {
        Some(simplify(Expr::Mul(const_expr.boxed(), scaled.boxed())))
    }
}

fn integrate_sin_cos_powers(
    sin_exp: i64,
    cos_exp: i64,
    inner: &Expr,
    k: Expr,
) -> Option<Expr> {
    if sin_exp == 0 && cos_exp == 0 {
        return None;
    }
    if cos_exp == 0 {
        return sin_power_reduction(sin_exp, inner).map(|r| scale_by_coeff(r, k.clone()));
    }
    if sin_exp == 0 {
        return cos_power_reduction(cos_exp, inner).map(|r| scale_by_coeff(r, k.clone()));
    }

    if sin_exp == 1 && cos_exp == 1 {
        let cos_sq = Expr::Pow(
            Expr::Cos(inner.clone().boxed()).boxed(),
            Expr::Constant(Rational::from_integer(2.into())).boxed(),
        );
        let result = Expr::Mul(
            Expr::Constant(Rational::new((-1).into(), 2.into())).boxed(),
            cos_sq.boxed(),
        );
        return Some(scale_by_coeff(result, k));
    }

    if sin_exp % 2 == 1 {
        return integrate_with_cos_substitution(sin_exp, cos_exp, inner, k);
    }
    if cos_exp % 2 == 1 {
        return integrate_with_sin_substitution(sin_exp, cos_exp, inner, k);
    }

    if sin_exp == 2 && cos_exp == 2 {
        let four = Rational::from_integer(4.into());
        let eight = Rational::from_integer(8.into());
        let thirty_two = Rational::from_integer(32.into());
        let scaled_inner = Expr::Mul(
            Expr::Constant(four.clone()).boxed(),
            inner.clone().boxed(),
        );
        let linear_term = Expr::Div(inner.clone().boxed(), Expr::Constant(eight).boxed());
        let oscillatory = Expr::Div(
            Expr::Sin(scaled_inner.boxed()).boxed(),
            Expr::Constant(thirty_two).boxed(),
        );
        let combined = Expr::Sub(linear_term.boxed(), oscillatory.boxed());
        return Some(scale_by_coeff(combined, k));
    }

    None
}

fn choose(n: i64, k: i64) -> Rational {
    if k < 0 || k > n {
        return Rational::zero();
    }
    let mut num = BigInt::from(1_i64);
    let mut den = BigInt::from(1_i64);
    for i in 0..k {
        num *= n - i;
        den *= i + 1;
    }
    Rational::new(num, den)
}

fn integrate_with_cos_substitution(
    sin_exp: i64,
    cos_exp: i64,
    inner: &Expr,
    k: Expr,
) -> Option<Expr> {
    if sin_exp < 1 {
        return None;
    }
    let m = (sin_exp - 1) / 2;
    let mut terms: Vec<Expr> = Vec::new();
    for j in 0..=m {
        let coeff = choose(m, j);
        let power = cos_exp + 2 * j + 1;
        let denom = Rational::from_integer(power.into());
        let sign = if j % 2 == 0 {
            Rational::one()
        } else {
            -Rational::one()
        };
        let factor = Expr::Mul(
            Expr::Constant(-sign * coeff.clone() / denom.clone()).boxed(),
            Expr::Pow(
                Expr::Cos(inner.clone().boxed()).boxed(),
                Expr::Constant(Rational::from_integer(power.into())).boxed(),
            )
            .boxed(),
        );
        terms.push(factor);
    }
    let sum = terms
        .into_iter()
        .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
        .unwrap_or_else(|| Expr::Constant(Rational::zero()));
    Some(scale_by_coeff(sum, k))
}

fn integrate_with_sin_substitution(
    sin_exp: i64,
    cos_exp: i64,
    inner: &Expr,
    k: Expr,
) -> Option<Expr> {
    if cos_exp < 1 {
        return None;
    }
    let m = (cos_exp - 1) / 2;
    let mut terms: Vec<Expr> = Vec::new();
    for j in 0..=m {
        let coeff = choose(m, j);
        let power = sin_exp + 2 * j + 1;
        let denom = Rational::from_integer(power.into());
        let sign = if j % 2 == 0 {
            Rational::one()
        } else {
            -Rational::one()
        };
        let factor = Expr::Mul(
            Expr::Constant(sign * coeff.clone() / denom.clone()).boxed(),
            Expr::Pow(
                Expr::Sin(inner.clone().boxed()).boxed(),
                Expr::Constant(Rational::from_integer(power.into())).boxed(),
            )
            .boxed(),
        );
        terms.push(factor);
    }
    let sum = terms
        .into_iter()
        .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
        .unwrap_or_else(|| Expr::Constant(Rational::zero()));
    Some(scale_by_coeff(sum, k))
}

fn integrate_arcsin(arg: &Expr, var: &str) -> Option<Expr> {
    let (k, c) = linear_parts(arg, var)?;
    if is_const_zero(&k) {
        return None;
    }
    let inner = simplify(Expr::Add(
        Expr::Mul(k.clone().boxed(), Expr::Variable(var.to_string()).boxed()).boxed(),
        c.clone().boxed(),
    ));
    let sqrt = Expr::Pow(
        Expr::Sub(
            Expr::Constant(Rational::one()).boxed(),
            Expr::Pow(inner.clone().boxed(), Expr::Constant(Rational::from_integer(2.into())).boxed()).boxed(),
        )
        .boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into())).boxed(),
    );
    let term = Expr::Mul(inner.clone().boxed(), Expr::Asin(inner.clone().boxed()).boxed());
    Some(scale_by_coeff(Expr::Add(term.boxed(), sqrt.boxed()), k))
}

fn integrate_arccos(arg: &Expr, var: &str) -> Option<Expr> {
    let (k, c) = linear_parts(arg, var)?;
    if is_const_zero(&k) {
        return None;
    }
    let inner = simplify(Expr::Add(
        Expr::Mul(k.clone().boxed(), Expr::Variable(var.to_string()).boxed()).boxed(),
        c.clone().boxed(),
    ));
    let sqrt = Expr::Pow(
        Expr::Sub(
            Expr::Constant(Rational::one()).boxed(),
            Expr::Pow(inner.clone().boxed(), Expr::Constant(Rational::from_integer(2.into())).boxed()).boxed(),
        )
        .boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into())).boxed(),
    );
    let term = Expr::Mul(inner.clone().boxed(), Expr::Acos(inner.clone().boxed()).boxed());
    Some(scale_by_coeff(Expr::Sub(term.boxed(), sqrt.boxed()), k))
}

fn integrate_arctan(arg: &Expr, var: &str) -> Option<Expr> {
    let (k, c) = linear_parts(arg, var)?;
    if is_const_zero(&k) {
        return None;
    }
    let inner = simplify(Expr::Add(
        Expr::Mul(k.clone().boxed(), Expr::Variable(var.to_string()).boxed()).boxed(),
        c.clone().boxed(),
    ));
    let log_term = log_abs(Expr::Add(
        Expr::Constant(Rational::one()).boxed(),
        Expr::Pow(inner.clone().boxed(), Expr::Constant(Rational::from_integer(2.into())).boxed()).boxed(),
    ));
    let term = Expr::Mul(inner.clone().boxed(), Expr::Atan(inner.clone().boxed()).boxed());
    Some(scale_by_coeff(
        Expr::Sub(
            term.boxed(),
            Expr::Div(log_term.boxed(), Expr::Constant(Rational::from_integer(2.into())).boxed())
                .boxed(),
        ),
        k,
    ))
}

fn integrate_arcsec(arg: &Expr, var: &str) -> Option<Expr> {
    let (k, c) = linear_parts(arg, var)?;
    if is_const_zero(&k) {
        return None;
    }
    let inner = simplify(Expr::Add(
        Expr::Mul(k.clone().boxed(), Expr::Variable(var.to_string()).boxed()).boxed(),
        c.clone().boxed(),
    ));
    let sqrt = Expr::Pow(
        Expr::Sub(
            Expr::Pow(inner.clone().boxed(), Expr::Constant(Rational::from_integer(2.into())).boxed())
                .boxed(),
            Expr::Constant(Rational::one()).boxed(),
        )
        .boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into())).boxed(),
    );
    let log_term = log_abs(Expr::Add(inner.clone().boxed(), sqrt.boxed()));
    let term = Expr::Mul(inner.clone().boxed(), Expr::Asec(inner.clone().boxed()).boxed());
    Some(scale_by_coeff(Expr::Sub(term.boxed(), log_term.boxed()), k))
}

fn integrate_arccsc(arg: &Expr, var: &str) -> Option<Expr> {
    let (k, c) = linear_parts(arg, var)?;
    if is_const_zero(&k) {
        return None;
    }
    let inner = simplify(Expr::Add(
        Expr::Mul(k.clone().boxed(), Expr::Variable(var.to_string()).boxed()).boxed(),
        c.clone().boxed(),
    ));
    let sqrt = Expr::Pow(
        Expr::Sub(
            Expr::Pow(inner.clone().boxed(), Expr::Constant(Rational::from_integer(2.into())).boxed())
                .boxed(),
            Expr::Constant(Rational::one()).boxed(),
        )
        .boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into())).boxed(),
    );
    let log_term = log_abs(Expr::Add(inner.clone().boxed(), sqrt.boxed()));
    let term = Expr::Mul(inner.clone().boxed(), Expr::Acsc(inner.clone().boxed()).boxed());
    Some(scale_by_coeff(Expr::Add(term.boxed(), log_term.boxed()), k))
}

fn integrate_arccot(arg: &Expr, var: &str) -> Option<Expr> {
    let (k, c) = linear_parts(arg, var)?;
    if is_const_zero(&k) {
        return None;
    }
    let inner = simplify(Expr::Add(
        Expr::Mul(k.clone().boxed(), Expr::Variable(var.to_string()).boxed()).boxed(),
        c.clone().boxed(),
    ));
    let log_term = log_abs(Expr::Add(
        Expr::Constant(Rational::one()).boxed(),
        Expr::Pow(inner.clone().boxed(), Expr::Constant(Rational::from_integer(2.into())).boxed())
            .boxed(),
    ));
    let term = Expr::Mul(inner.clone().boxed(), Expr::Acot(inner.clone().boxed()).boxed());
    Some(scale_by_coeff(
        Expr::Add(
            term.boxed(),
            Expr::Div(log_term.boxed(), Expr::Constant(Rational::from_integer(2.into())).boxed())
                .boxed(),
        ),
        k,
    ))
}

fn integrate_asinh(arg: &Expr, var: &str) -> Option<Expr> {
    let (k, c) = linear_parts(arg, var)?;
    if is_const_zero(&k) {
        return None;
    }
    let inner = simplify(Expr::Add(
        Expr::Mul(k.clone().boxed(), Expr::Variable(var.to_string()).boxed()).boxed(),
        c.clone().boxed(),
    ));
    let sqrt = Expr::Pow(
        Expr::Add(
            Expr::Pow(inner.clone().boxed(), Expr::Constant(Rational::from_integer(2.into())).boxed())
                .boxed(),
            Expr::Constant(Rational::one()).boxed(),
        )
        .boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into())).boxed(),
    );
    let term = Expr::Mul(inner.clone().boxed(), Expr::Asinh(inner.clone().boxed()).boxed());
    Some(scale_by_coeff(Expr::Sub(term.boxed(), sqrt.boxed()), k))
}

fn integrate_acosh(arg: &Expr, var: &str) -> Option<Expr> {
    let (k, c) = linear_parts(arg, var)?;
    if is_const_zero(&k) {
        return None;
    }
    let inner = simplify(Expr::Add(
        Expr::Mul(k.clone().boxed(), Expr::Variable(var.to_string()).boxed()).boxed(),
        c.clone().boxed(),
    ));
    let sqrt = Expr::Pow(
        Expr::Sub(
            Expr::Pow(inner.clone().boxed(), Expr::Constant(Rational::from_integer(2.into())).boxed())
                .boxed(),
            Expr::Constant(Rational::one()).boxed(),
        )
        .boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into())).boxed(),
    );
    let term = Expr::Mul(inner.clone().boxed(), Expr::Acosh(inner.clone().boxed()).boxed());
    Some(scale_by_coeff(Expr::Sub(term.boxed(), sqrt.boxed()), k))
}

fn integrate_atanh(arg: &Expr, var: &str) -> Option<Expr> {
    let (k, c) = linear_parts(arg, var)?;
    if is_const_zero(&k) {
        return None;
    }
    let inner = simplify(Expr::Add(
        Expr::Mul(k.clone().boxed(), Expr::Variable(var.to_string()).boxed()).boxed(),
        c.clone().boxed(),
    ));
    let log_term = log_abs(Expr::Sub(
        Expr::Constant(Rational::one()).boxed(),
        Expr::Pow(inner.clone().boxed(), Expr::Constant(Rational::from_integer(2.into())).boxed())
            .boxed(),
    ));
    let term = Expr::Mul(inner.clone().boxed(), Expr::Atanh(inner.clone().boxed()).boxed());
    Some(scale_by_coeff(
        Expr::Add(
            term.boxed(),
            Expr::Div(log_term.boxed(), Expr::Constant(Rational::from_integer(2.into())).boxed())
                .boxed(),
        ),
        k,
    ))
}
