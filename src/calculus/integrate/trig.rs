use crate::core::expr::{Expr, Rational};
use crate::simplify::{simplify, simplify_fully, substitute};
use num_traits::{One, ToPrimitive, Zero};
use num_bigint::BigInt;

use super::{coeff_of_var, contains_var, flatten_product, linear_parts, log_abs, rebuild_product};
use super::rational;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TrigFamily {
    Circular,
    Hyperbolic,
}

struct TrigRationalInfo {
    family: TrigFamily,
    arg: Expr,
}

pub fn integrate(expr: &Expr, var: &str) -> Option<Expr> {
    let direct = match expr {
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
            (Expr::Tan(inner), Expr::Constant(p)) if p.is_integer() && p >= &Rational::zero() => {
                integrate_tan_power(inner, p, var)
            }
            (Expr::Sec(inner), Expr::Constant(p)) if p.is_integer() && p >= &Rational::zero() => {
                integrate_sec_power(inner, p, var)
            }
            (Expr::Csc(inner), Expr::Constant(p)) if p.is_integer() && p >= &Rational::zero() => {
                integrate_csc_power(inner, p, var)
            }
            (Expr::Cot(inner), Expr::Constant(p)) if p.is_integer() && p >= &Rational::zero() => {
                integrate_cot_power(inner, p, var)
            }
            (Expr::Sec(inner), Expr::Constant(p)) if p == &Rational::from_integer(2.into()) => {
                integrate_sec_squared(inner, var)
            }
            (Expr::Csc(inner), Expr::Constant(p)) if p == &Rational::from_integer(2.into()) => {
                integrate_csc_squared(inner, var)
            }
            _ => None,
        },
        Expr::Mul(_, _) => integrate_sin_cos_product(expr, var)
            .or_else(|| integrate_tan_sec_product(expr, var))
            .or_else(|| integrate_cot_csc_product(expr, var))
            .or_else(|| integrate_mixed_trig_product(expr, var)),
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
    };
    direct.or_else(|| integrate_rational_trig(expr, var))
}

fn integrate_rational_trig(expr: &Expr, var: &str) -> Option<Expr> {
    let info = trig_rational_info(expr, var)?;
    let k = coeff_of_var(&info.arg, var)?;
    let t_name = fresh_var_name(expr, var, "t");
    let t_var = Expr::Variable(t_name.clone());
    let replaced = replace_trig_expr(expr, &info, &t_var)?;
    let dx_factor = half_angle_dx_factor(info.family, &t_var);
    let integrand_t = simplify(Expr::Mul(replaced.boxed(), dx_factor.boxed()));
    let (num_t, den_t) = rationalize_expr(&integrand_t, &t_name)?;
    let num_t = simplify(num_t);
    let den_t = simplify(den_t);
    let rational_t = Expr::Div(num_t.boxed(), den_t.boxed());
    let integrated_t = rational::integrate(&rational_t, &t_name)?;
    let t_sub = half_angle_substitution(info.family, &info.arg);
    let restored = substitute(&integrated_t, &t_name, &t_sub);
    Some(simplify(scale_by_coeff(restored, k)))
}

fn trig_rational_info(expr: &Expr, var: &str) -> Option<TrigRationalInfo> {
    let mut family = None;
    let mut arg = None;
    scan_trig_rational(expr, var, false, &mut family, &mut arg)?;
    Some(TrigRationalInfo {
        family: family?,
        arg: arg?,
    })
}

fn scan_trig_rational(
    expr: &Expr,
    var: &str,
    inside_trig_arg: bool,
    family: &mut Option<TrigFamily>,
    arg: &mut Option<Expr>,
) -> Option<()> {
    match expr {
        Expr::Variable(name) => {
            if name == var && !inside_trig_arg {
                None
            } else {
                Some(())
            }
        }
        Expr::Constant(_) => Some(()),
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b) => {
            scan_trig_rational(a, var, inside_trig_arg, family, arg)?;
            scan_trig_rational(b, var, inside_trig_arg, family, arg)?;
            Some(())
        }
        Expr::Neg(inner) => scan_trig_rational(inner, var, inside_trig_arg, family, arg),
        Expr::Pow(base, exp) => {
            if extract_integer(exp).is_none() {
                return None;
            }
            scan_trig_rational(base, var, inside_trig_arg, family, arg)
        }
        Expr::Sin(inner)
        | Expr::Cos(inner)
        | Expr::Tan(inner)
        | Expr::Sec(inner)
        | Expr::Csc(inner)
        | Expr::Cot(inner) => {
            if inside_trig_arg {
                return None;
            }
            set_trig_family(family, TrigFamily::Circular)?;
            let (base, _) = normalize_arg(inner);
            update_trig_arg(arg, base)?;
            scan_trig_rational(inner, var, true, family, arg)?;
            Some(())
        }
        Expr::Sinh(inner) | Expr::Cosh(inner) | Expr::Tanh(inner) => {
            if inside_trig_arg {
                return None;
            }
            set_trig_family(family, TrigFamily::Hyperbolic)?;
            let (base, _) = normalize_arg(inner);
            update_trig_arg(arg, base)?;
            scan_trig_rational(inner, var, true, family, arg)?;
            Some(())
        }
        Expr::Atan(_)
        | Expr::Asin(_)
        | Expr::Acos(_)
        | Expr::Asec(_)
        | Expr::Acsc(_)
        | Expr::Acot(_)
        | Expr::Asinh(_)
        | Expr::Acosh(_)
        | Expr::Atanh(_)
        | Expr::Exp(_)
        | Expr::Log(_)
        | Expr::Abs(_) => None,
    }
}

fn set_trig_family(slot: &mut Option<TrigFamily>, family: TrigFamily) -> Option<()> {
    match slot {
        Some(existing) if *existing != family => None,
        _ => {
            *slot = Some(family);
            Some(())
        }
    }
}

fn update_trig_arg(slot: &mut Option<Expr>, arg: Expr) -> Option<()> {
    if let Some(existing) = slot {
        if *existing != arg {
            return None;
        }
    } else {
        *slot = Some(arg);
    }
    Some(())
}

fn fresh_var_name(expr: &Expr, var: &str, base: &str) -> String {
    if base != var && !contains_var(expr, base) {
        return base.to_string();
    }
    for idx in 1..64 {
        let candidate = format!("{base}{idx}");
        if candidate != var && !contains_var(expr, &candidate) {
            return candidate;
        }
    }
    format!("{base}_sub")
}

fn normalize_arg(expr: &Expr) -> (Expr, bool) {
    match expr {
        Expr::Neg(inner) => ((*inner.clone()), true),
        Expr::Mul(a, b) => {
            if let Expr::Constant(c) = &**a {
                if c < &Rational::zero() {
                    let base = Expr::Mul(
                        Expr::Constant(-c.clone()).boxed(),
                        b.clone(),
                    );
                    return (simplify(base), true);
                }
            }
            if let Expr::Constant(c) = &**b {
                if c < &Rational::zero() {
                    let base = Expr::Mul(
                        a.clone(),
                        Expr::Constant(-c.clone()).boxed(),
                    );
                    return (simplify(base), true);
                }
            }
            (expr.clone(), false)
        }
        Expr::Div(a, b) => {
            if let Expr::Constant(c) = &**b {
                if c < &Rational::zero() {
                    let base = Expr::Div(
                        a.clone(),
                        Expr::Constant(-c.clone()).boxed(),
                    );
                    return (simplify(base), true);
                }
            }
            (expr.clone(), false)
        }
        _ => (expr.clone(), false),
    }
}

fn replace_trig_expr(expr: &Expr, info: &TrigRationalInfo, t_var: &Expr) -> Option<Expr> {
    match expr {
        Expr::Constant(_) | Expr::Variable(_) => Some(expr.clone()),
        Expr::Add(a, b) => Some(Expr::Add(
            replace_trig_expr(a, info, t_var)?.boxed(),
            replace_trig_expr(b, info, t_var)?.boxed(),
        )),
        Expr::Sub(a, b) => Some(Expr::Sub(
            replace_trig_expr(a, info, t_var)?.boxed(),
            replace_trig_expr(b, info, t_var)?.boxed(),
        )),
        Expr::Mul(a, b) => Some(Expr::Mul(
            replace_trig_expr(a, info, t_var)?.boxed(),
            replace_trig_expr(b, info, t_var)?.boxed(),
        )),
        Expr::Div(a, b) => Some(Expr::Div(
            replace_trig_expr(a, info, t_var)?.boxed(),
            replace_trig_expr(b, info, t_var)?.boxed(),
        )),
        Expr::Neg(inner) => replace_trig_expr(inner, info, t_var)
            .map(|r| Expr::Neg(r.boxed())),
        Expr::Pow(base, exp) => {
            if extract_integer(exp).is_none() {
                return None;
            }
            Some(Expr::Pow(
                replace_trig_expr(base, info, t_var)?.boxed(),
                exp.clone(),
            ))
        }
        Expr::Sin(arg) => replace_circular_func(CircularFunc::Sin, arg, info, t_var),
        Expr::Cos(arg) => replace_circular_func(CircularFunc::Cos, arg, info, t_var),
        Expr::Tan(arg) => replace_circular_func(CircularFunc::Tan, arg, info, t_var),
        Expr::Sec(arg) => replace_circular_func(CircularFunc::Sec, arg, info, t_var),
        Expr::Csc(arg) => replace_circular_func(CircularFunc::Csc, arg, info, t_var),
        Expr::Cot(arg) => replace_circular_func(CircularFunc::Cot, arg, info, t_var),
        Expr::Sinh(arg) => replace_hyperbolic_func(HyperbolicFunc::Sinh, arg, info, t_var),
        Expr::Cosh(arg) => replace_hyperbolic_func(HyperbolicFunc::Cosh, arg, info, t_var),
        Expr::Tanh(arg) => replace_hyperbolic_func(HyperbolicFunc::Tanh, arg, info, t_var),
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum CircularFunc {
    Sin,
    Cos,
    Tan,
    Sec,
    Csc,
    Cot,
}

fn replace_circular_func(
    func: CircularFunc,
    arg: &Expr,
    info: &TrigRationalInfo,
    t_var: &Expr,
) -> Option<Expr> {
    if info.family != TrigFamily::Circular {
        return None;
    }
    let (base, negated) = normalize_arg(arg);
    if base != info.arg {
        return None;
    }
    let t_sq = t_square(t_var);
    let one = Expr::Constant(Rational::one());
    let two = Expr::Constant(Rational::from_integer(2.into()));
    let one_plus = Expr::Add(one.clone().boxed(), t_sq.clone().boxed());
    let one_minus = Expr::Sub(one.clone().boxed(), t_sq.clone().boxed());
    let expr = match func {
        CircularFunc::Sin => Expr::Div(
            Expr::Mul(two.clone().boxed(), t_var.clone().boxed()).boxed(),
            one_plus.clone().boxed(),
        ),
        CircularFunc::Cos => Expr::Div(one_minus.clone().boxed(), one_plus.clone().boxed()),
        CircularFunc::Tan => Expr::Div(
            Expr::Mul(two.clone().boxed(), t_var.clone().boxed()).boxed(),
            one_minus.clone().boxed(),
        ),
        CircularFunc::Sec => Expr::Div(one_plus.clone().boxed(), one_minus.clone().boxed()),
        CircularFunc::Csc => Expr::Div(
            one_plus.clone().boxed(),
            Expr::Mul(two.clone().boxed(), t_var.clone().boxed()).boxed(),
        ),
        CircularFunc::Cot => Expr::Div(
            one_minus.clone().boxed(),
            Expr::Mul(two.clone().boxed(), t_var.clone().boxed()).boxed(),
        ),
    };
    let odd = matches!(
        func,
        CircularFunc::Sin | CircularFunc::Tan | CircularFunc::Csc | CircularFunc::Cot
    );
    Some(apply_parity(expr, negated, odd))
}

#[derive(Clone, Copy)]
enum HyperbolicFunc {
    Sinh,
    Cosh,
    Tanh,
}

fn replace_hyperbolic_func(
    func: HyperbolicFunc,
    arg: &Expr,
    info: &TrigRationalInfo,
    t_var: &Expr,
) -> Option<Expr> {
    if info.family != TrigFamily::Hyperbolic {
        return None;
    }
    let (base, negated) = normalize_arg(arg);
    if base != info.arg {
        return None;
    }
    let t_sq = t_square(t_var);
    let one = Expr::Constant(Rational::one());
    let two = Expr::Constant(Rational::from_integer(2.into()));
    let one_minus = Expr::Sub(one.clone().boxed(), t_sq.clone().boxed());
    let one_plus = Expr::Add(one.clone().boxed(), t_sq.clone().boxed());
    let expr = match func {
        HyperbolicFunc::Sinh => Expr::Div(
            Expr::Mul(two.clone().boxed(), t_var.clone().boxed()).boxed(),
            one_minus.clone().boxed(),
        ),
        HyperbolicFunc::Cosh => Expr::Div(one_plus.clone().boxed(), one_minus.clone().boxed()),
        HyperbolicFunc::Tanh => Expr::Div(
            Expr::Mul(two.clone().boxed(), t_var.clone().boxed()).boxed(),
            one_plus.clone().boxed(),
        ),
    };
    let odd = matches!(func, HyperbolicFunc::Sinh | HyperbolicFunc::Tanh);
    Some(apply_parity(expr, negated, odd))
}

fn apply_parity(expr: Expr, negated: bool, odd: bool) -> Expr {
    if negated && odd {
        Expr::Neg(expr.boxed())
    } else {
        expr
    }
}

fn t_square(t_var: &Expr) -> Expr {
    Expr::Pow(
        t_var.clone().boxed(),
        Expr::Constant(Rational::from_integer(2.into())).boxed(),
    )
}

fn half_angle_dx_factor(family: TrigFamily, t_var: &Expr) -> Expr {
    let two = Expr::Constant(Rational::from_integer(2.into()));
    let t_sq = t_square(t_var);
    let denom = match family {
        TrigFamily::Circular => Expr::Add(
            Expr::Constant(Rational::one()).boxed(),
            t_sq.boxed(),
        ),
        TrigFamily::Hyperbolic => Expr::Sub(
            Expr::Constant(Rational::one()).boxed(),
            t_sq.boxed(),
        ),
    };
    Expr::Div(two.boxed(), denom.boxed())
}

fn half_angle_substitution(family: TrigFamily, arg: &Expr) -> Expr {
    let half = Expr::Constant(Rational::new(1.into(), 2.into()));
    let half_arg = simplify(Expr::Mul(half.boxed(), arg.clone().boxed()));
    match family {
        TrigFamily::Circular => Expr::Tan(half_arg.boxed()),
        TrigFamily::Hyperbolic => Expr::Tanh(half_arg.boxed()),
    }
}

fn extract_integer(exp: &Expr) -> Option<i64> {
    match exp {
        Expr::Constant(c) if c.is_integer() => c.to_integer().to_i64(),
        Expr::Neg(inner) => extract_integer(inner).map(|value| -value),
        _ => None,
    }
}

fn rationalize_expr(expr: &Expr, var: &str) -> Option<(Expr, Expr)> {
    if !contains_var(expr, var) {
        return Some((expr.clone(), Expr::Constant(Rational::one())));
    }
    match expr {
        Expr::Variable(name) if name == var => Some((
            Expr::Variable(name.clone()),
            Expr::Constant(Rational::one()),
        )),
        Expr::Constant(_) => Some((expr.clone(), Expr::Constant(Rational::one()))),
        Expr::Add(a, b) => {
            let (an, ad) = rationalize_expr(a, var)?;
            let (bn, bd) = rationalize_expr(b, var)?;
            let numer = Expr::Add(
                Expr::Mul(an.boxed(), bd.clone().boxed()).boxed(),
                Expr::Mul(bn.boxed(), ad.clone().boxed()).boxed(),
            );
            let denom = Expr::Mul(ad.boxed(), bd.boxed());
            Some((numer, denom))
        }
        Expr::Sub(a, b) => {
            let (an, ad) = rationalize_expr(a, var)?;
            let (bn, bd) = rationalize_expr(b, var)?;
            let numer = Expr::Sub(
                Expr::Mul(an.boxed(), bd.clone().boxed()).boxed(),
                Expr::Mul(bn.boxed(), ad.clone().boxed()).boxed(),
            );
            let denom = Expr::Mul(ad.boxed(), bd.boxed());
            Some((numer, denom))
        }
        Expr::Mul(a, b) => {
            let (an, ad) = rationalize_expr(a, var)?;
            let (bn, bd) = rationalize_expr(b, var)?;
            let numer = Expr::Mul(an.boxed(), bn.boxed());
            let denom = Expr::Mul(ad.boxed(), bd.boxed());
            Some((numer, denom))
        }
        Expr::Div(a, b) => {
            let (an, ad) = rationalize_expr(a, var)?;
            let (bn, bd) = rationalize_expr(b, var)?;
            let numer = Expr::Mul(an.boxed(), bd.boxed());
            let denom = Expr::Mul(ad.boxed(), bn.boxed());
            Some((numer, denom))
        }
        Expr::Neg(inner) => {
            let (n, d) = rationalize_expr(inner, var)?;
            Some((Expr::Neg(n.boxed()), d))
        }
        Expr::Pow(base, exp) => {
            let power = extract_integer(exp)?;
            if power == 0 {
                return Some((
                    Expr::Constant(Rational::one()),
                    Expr::Constant(Rational::one()),
                ));
            }
            let abs_power = power.abs() as usize;
            let (bn, bd) = rationalize_expr(base, var)?;
            let mut numer = pow_expr(bn, abs_power);
            let mut denom = pow_expr(bd, abs_power);
            if power < 0 {
                std::mem::swap(&mut numer, &mut denom);
            }
            Some((numer, denom))
        }
        _ => None,
    }
}

fn pow_expr(expr: Expr, power: usize) -> Expr {
    match power {
        0 => Expr::Constant(Rational::one()),
        1 => expr,
        _ => Expr::Pow(
            expr.boxed(),
            Expr::Constant(Rational::from_integer(power.into())).boxed(),
        ),
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

fn integrate_tan_power(inner: &Expr, power: &Rational, var: &str) -> Option<Expr> {
    let n = pow_to_i64(power)?;
    let k = coeff_of_var(inner, var)?;
    let integral = tan_power_reduction(n, inner)?;
    Some(scale_by_coeff(integral, k))
}

fn integrate_sec_power(inner: &Expr, power: &Rational, var: &str) -> Option<Expr> {
    let n = pow_to_i64(power)?;
    let k = coeff_of_var(inner, var)?;
    let integral = sec_power_reduction(n, inner)?;
    Some(scale_by_coeff(integral, k))
}

fn integrate_csc_power(inner: &Expr, power: &Rational, var: &str) -> Option<Expr> {
    let n = pow_to_i64(power)?;
    let k = coeff_of_var(inner, var)?;
    let integral = csc_power_reduction(n, inner)?;
    Some(scale_by_coeff(integral, k))
}

fn integrate_cot_power(inner: &Expr, power: &Rational, var: &str) -> Option<Expr> {
    let n = pow_to_i64(power)?;
    let k = coeff_of_var(inner, var)?;
    let integral = cot_power_reduction(n, inner)?;
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

fn tan_power_reduction(n: i64, inner: &Expr) -> Option<Expr> {
    if n < 0 {
        return None;
    }
    if n == 0 {
        return Some(inner.clone());
    }
    if n == 1 {
        return Some(Expr::Neg(log_abs(Expr::Cos(inner.clone().boxed())).boxed()));
    }
    let n_minus_one = Rational::from_integer((n - 1).into());
    let power = pow_expr(Expr::Tan(inner.clone().boxed()), (n - 1) as usize);
    let leading = Expr::Div(power.boxed(), Expr::Constant(n_minus_one).boxed());
    let reduced = tan_power_reduction(n - 2, inner)?;
    Some(simplify(Expr::Sub(leading.boxed(), reduced.boxed())))
}

fn sec_power_reduction(n: i64, inner: &Expr) -> Option<Expr> {
    if n < 0 {
        return None;
    }
    if n == 0 {
        return Some(inner.clone());
    }
    if n == 1 {
        let sum = Expr::Add(
            Expr::Sec(inner.clone().boxed()).boxed(),
            Expr::Tan(inner.clone().boxed()).boxed(),
        );
        return Some(log_abs(sum));
    }
    if n == 2 {
        return Some(Expr::Tan(inner.clone().boxed()));
    }
    let n_minus_one = Rational::from_integer((n - 1).into());
    let n_minus_two = Rational::from_integer((n - 2).into());
    let leading = Expr::Div(
        Expr::Mul(
            pow_expr(Expr::Sec(inner.clone().boxed()), (n - 2) as usize).boxed(),
            Expr::Tan(inner.clone().boxed()).boxed(),
        )
        .boxed(),
        Expr::Constant(n_minus_one.clone()).boxed(),
    );
    let reduced = sec_power_reduction(n - 2, inner)?;
    let scaled = Expr::Mul(
        Expr::Constant(n_minus_two / n_minus_one).boxed(),
        reduced.boxed(),
    );
    Some(simplify(Expr::Add(leading.boxed(), scaled.boxed())))
}

fn csc_power_reduction(n: i64, inner: &Expr) -> Option<Expr> {
    if n < 0 {
        return None;
    }
    if n == 0 {
        return Some(inner.clone());
    }
    if n == 1 {
        let diff = Expr::Sub(
            Expr::Csc(inner.clone().boxed()).boxed(),
            Expr::Cot(inner.clone().boxed()).boxed(),
        );
        return Some(log_abs(diff));
    }
    if n == 2 {
        return Some(Expr::Neg(Expr::Cot(inner.clone().boxed()).boxed()));
    }
    let n_minus_one = Rational::from_integer((n - 1).into());
    let n_minus_two = Rational::from_integer((n - 2).into());
    let leading = Expr::Div(
        Expr::Neg(
            Expr::Mul(
                pow_expr(Expr::Csc(inner.clone().boxed()), (n - 2) as usize).boxed(),
                Expr::Cot(inner.clone().boxed()).boxed(),
            )
            .boxed(),
        )
        .boxed(),
        Expr::Constant(n_minus_one.clone()).boxed(),
    );
    let reduced = csc_power_reduction(n - 2, inner)?;
    let scaled = Expr::Mul(
        Expr::Constant(n_minus_two / n_minus_one).boxed(),
        reduced.boxed(),
    );
    Some(simplify(Expr::Add(leading.boxed(), scaled.boxed())))
}

fn cot_power_reduction(n: i64, inner: &Expr) -> Option<Expr> {
    if n < 0 {
        return None;
    }
    if n == 0 {
        return Some(inner.clone());
    }
    if n == 1 {
        return Some(log_abs(Expr::Sin(inner.clone().boxed())));
    }
    let n_minus_one = Rational::from_integer((n - 1).into());
    let power = pow_expr(Expr::Cot(inner.clone().boxed()), (n - 1) as usize);
    let leading = Expr::Div(
        Expr::Neg(power.boxed()).boxed(),
        Expr::Constant(n_minus_one).boxed(),
    );
    let reduced = cot_power_reduction(n - 2, inner)?;
    Some(simplify(Expr::Sub(leading.boxed(), reduced.boxed())))
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

fn integrate_tan_sec_product(expr: &Expr, var: &str) -> Option<Expr> {
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
    let mut tan_exp = 0_i64;
    let mut sec_exp = 0_i64;
    let mut inner: Option<Expr> = None;

    for factor in var_factors {
        match factor {
            Expr::Tan(arg) => {
                inner = match inner {
                    None => Some(*arg.clone()),
                    Some(ref existing) if *existing == *arg => Some(existing.clone()),
                    _ => return None,
                };
                tan_exp += 1;
            }
            Expr::Sec(arg) => {
                inner = match inner {
                    None => Some(*arg.clone()),
                    Some(ref existing) if *existing == *arg => Some(existing.clone()),
                    _ => return None,
                };
                sec_exp += 1;
            }
            Expr::Pow(base, exp) => match (&*base, &*exp) {
                (Expr::Tan(arg), Expr::Constant(p)) if p.is_integer() && p >= &Rational::zero() => {
                    inner = match inner {
                        None => Some(*arg.clone()),
                        Some(ref existing) if *existing == **arg => Some(existing.clone()),
                        _ => return None,
                    };
                    tan_exp += pow_to_i64(p)?;
                }
                (Expr::Sec(arg), Expr::Constant(p)) if p.is_integer() && p >= &Rational::zero() => {
                    inner = match inner {
                        None => Some(*arg.clone()),
                        Some(ref existing) if *existing == **arg => Some(existing.clone()),
                        _ => return None,
                    };
                    sec_exp += pow_to_i64(p)?;
                }
                _ => return None,
            },
            Expr::Constant(_) => {}
            _ => return None,
        }
    }

    let inner = inner?;
    let k = coeff_of_var(&inner, var)?;
    let combined = integrate_tan_sec_powers(tan_exp, sec_exp, &inner, k)?;
    let scaled = simplify(combined);
    if is_const_one(&const_expr) {
        Some(scaled)
    } else {
        Some(simplify(Expr::Mul(const_expr.boxed(), scaled.boxed())))
    }
}

fn integrate_tan_sec_powers(
    tan_exp: i64,
    sec_exp: i64,
    inner: &Expr,
    k: Expr,
) -> Option<Expr> {
    if tan_exp == 0 && sec_exp == 0 {
        return None;
    }
    if sec_exp == 0 {
        return tan_power_reduction(tan_exp, inner).map(|r| scale_by_coeff(r, k.clone()));
    }
    if tan_exp == 0 {
        return sec_power_reduction(sec_exp, inner).map(|r| scale_by_coeff(r, k.clone()));
    }

    if sec_exp % 2 == 0 && sec_exp >= 2 {
        let p = (sec_exp - 2) / 2;
        let mut terms = Vec::new();
        for j in 0..=p {
            let coeff = choose(p, j);
            let power = tan_exp + 2 * j + 1;
            let denom = Rational::from_integer(power.into());
            let term_pow = pow_expr(Expr::Tan(inner.clone().boxed()), power as usize);
            let term = Expr::Mul(
                Expr::Constant(coeff / denom).boxed(),
                term_pow.boxed(),
            );
            terms.push(term);
        }
        let sum = terms
            .into_iter()
            .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
            .unwrap_or_else(|| Expr::Constant(Rational::zero()));
        return Some(scale_by_coeff(sum, k));
    }

    if tan_exp % 2 == 1 && sec_exp >= 1 {
        let q = (tan_exp - 1) / 2;
        let mut terms = Vec::new();
        for j in 0..=q {
            let coeff = choose(q, j);
            let sign = if (q - j) % 2 == 0 {
                Rational::one()
            } else {
                -Rational::one()
            };
            let power = sec_exp + 2 * j;
            let denom = Rational::from_integer(power.into());
            let term_pow = pow_expr(Expr::Sec(inner.clone().boxed()), power as usize);
            let term = Expr::Mul(
                Expr::Constant(sign * coeff / denom).boxed(),
                term_pow.boxed(),
            );
            terms.push(term);
        }
        let sum = terms
            .into_iter()
            .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
            .unwrap_or_else(|| Expr::Constant(Rational::zero()));
        return Some(scale_by_coeff(sum, k));
    }

    if tan_exp % 2 == 0 && sec_exp % 2 == 1 {
        let q = tan_exp / 2;
        let mut terms = Vec::new();
        for j in 0..=q {
            let coeff = choose(q, j);
            let sign = if (q - j) % 2 == 0 {
                Rational::one()
            } else {
                -Rational::one()
            };
            let power = sec_exp + 2 * j;
            let integral = sec_power_reduction(power, inner)?;
            terms.push(Expr::Mul(
                Expr::Constant(sign * coeff).boxed(),
                integral.boxed(),
            ));
        }
        let sum = terms
            .into_iter()
            .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
            .unwrap_or_else(|| Expr::Constant(Rational::zero()));
        return Some(scale_by_coeff(sum, k));
    }

    None
}

fn integrate_cot_csc_product(expr: &Expr, var: &str) -> Option<Expr> {
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
    let mut cot_exp = 0_i64;
    let mut csc_exp = 0_i64;
    let mut inner: Option<Expr> = None;

    for factor in var_factors {
        match factor {
            Expr::Cot(arg) => {
                inner = match inner {
                    None => Some(*arg.clone()),
                    Some(ref existing) if *existing == *arg => Some(existing.clone()),
                    _ => return None,
                };
                cot_exp += 1;
            }
            Expr::Csc(arg) => {
                inner = match inner {
                    None => Some(*arg.clone()),
                    Some(ref existing) if *existing == *arg => Some(existing.clone()),
                    _ => return None,
                };
                csc_exp += 1;
            }
            Expr::Pow(base, exp) => match (&*base, &*exp) {
                (Expr::Cot(arg), Expr::Constant(p)) if p.is_integer() && p >= &Rational::zero() => {
                    inner = match inner {
                        None => Some(*arg.clone()),
                        Some(ref existing) if *existing == **arg => Some(existing.clone()),
                        _ => return None,
                    };
                    cot_exp += pow_to_i64(p)?;
                }
                (Expr::Csc(arg), Expr::Constant(p)) if p.is_integer() && p >= &Rational::zero() => {
                    inner = match inner {
                        None => Some(*arg.clone()),
                        Some(ref existing) if *existing == **arg => Some(existing.clone()),
                        _ => return None,
                    };
                    csc_exp += pow_to_i64(p)?;
                }
                _ => return None,
            },
            Expr::Constant(_) => {}
            _ => return None,
        }
    }

    let inner = inner?;
    let k = coeff_of_var(&inner, var)?;
    let combined = integrate_cot_csc_powers(cot_exp, csc_exp, &inner, k)?;
    let scaled = simplify(combined);
    if is_const_one(&const_expr) {
        Some(scaled)
    } else {
        Some(simplify(Expr::Mul(const_expr.boxed(), scaled.boxed())))
    }
}

fn integrate_cot_csc_powers(
    cot_exp: i64,
    csc_exp: i64,
    inner: &Expr,
    k: Expr,
) -> Option<Expr> {
    if cot_exp == 0 && csc_exp == 0 {
        return None;
    }
    if csc_exp == 0 {
        return cot_power_reduction(cot_exp, inner).map(|r| scale_by_coeff(r, k.clone()));
    }
    if cot_exp == 0 {
        return csc_power_reduction(csc_exp, inner).map(|r| scale_by_coeff(r, k.clone()));
    }

    if csc_exp % 2 == 0 && csc_exp >= 2 {
        let p = (csc_exp - 2) / 2;
        let mut terms = Vec::new();
        for j in 0..=p {
            let coeff = choose(p, j);
            let power = cot_exp + 2 * j + 1;
            let denom = Rational::from_integer(power.into());
            let term_pow = pow_expr(Expr::Cot(inner.clone().boxed()), power as usize);
            let term = Expr::Mul(
                Expr::Constant(-coeff / denom).boxed(),
                term_pow.boxed(),
            );
            terms.push(term);
        }
        let sum = terms
            .into_iter()
            .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
            .unwrap_or_else(|| Expr::Constant(Rational::zero()));
        return Some(scale_by_coeff(sum, k));
    }

    if cot_exp % 2 == 1 && csc_exp >= 1 {
        let q = (cot_exp - 1) / 2;
        let mut terms = Vec::new();
        for j in 0..=q {
            let coeff = choose(q, j);
            let sign = if (q - j) % 2 == 0 {
                -Rational::one()
            } else {
                Rational::one()
            };
            let power = csc_exp + 2 * j;
            let denom = Rational::from_integer(power.into());
            let term_pow = pow_expr(Expr::Csc(inner.clone().boxed()), power as usize);
            let term = Expr::Mul(
                Expr::Constant(sign * coeff / denom).boxed(),
                term_pow.boxed(),
            );
            terms.push(term);
        }
        let sum = terms
            .into_iter()
            .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
            .unwrap_or_else(|| Expr::Constant(Rational::zero()));
        return Some(scale_by_coeff(sum, k));
    }

    if cot_exp % 2 == 0 && csc_exp % 2 == 1 {
        let q = cot_exp / 2;
        let mut terms = Vec::new();
        for j in 0..=q {
            let coeff = choose(q, j);
            let sign = if (q - j) % 2 == 0 {
                Rational::one()
            } else {
                -Rational::one()
            };
            let power = csc_exp + 2 * j;
            let integral = csc_power_reduction(power, inner)?;
            terms.push(Expr::Mul(
                Expr::Constant(sign * coeff).boxed(),
                integral.boxed(),
            ));
        }
        let sum = terms
            .into_iter()
            .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
            .unwrap_or_else(|| Expr::Constant(Rational::zero()));
        return Some(scale_by_coeff(sum, k));
    }

    None
}

fn integrate_mixed_trig_product(expr: &Expr, var: &str) -> Option<Expr> {
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
    if var_factors.len() != 2 {
        return None;
    }

    let const_expr = rebuild_product(const_factor, const_factors);
    let (first, second) = (&var_factors[0], &var_factors[1]);
    let half = Rational::new(1.into(), 2.into());

    let combined = match (first, second) {
        (Expr::Sin(a), Expr::Sin(b)) => {
            let arg_sum = Expr::Add(a.clone().boxed(), b.clone().boxed());
            let arg_diff = Expr::Sub(a.clone().boxed(), b.clone().boxed());
            let term1 = integrate_linear_trig(TrigSimple::Cos, arg_diff, var)?;
            let term2 = integrate_linear_trig(TrigSimple::Cos, arg_sum, var)?;
            Expr::Mul(
                Expr::Constant(half).boxed(),
                Expr::Sub(term1.boxed(), term2.boxed()).boxed(),
            )
        }
        (Expr::Sin(a), Expr::Cos(b)) | (Expr::Cos(b), Expr::Sin(a)) => {
            let arg_sum = Expr::Add(a.clone().boxed(), b.clone().boxed());
            let arg_diff = Expr::Sub(a.clone().boxed(), b.clone().boxed());
            let term1 = integrate_linear_trig(TrigSimple::Sin, arg_sum, var)?;
            let term2 = integrate_linear_trig(TrigSimple::Sin, arg_diff, var)?;
            Expr::Mul(
                Expr::Constant(half).boxed(),
                Expr::Add(term1.boxed(), term2.boxed()).boxed(),
            )
        }
        (Expr::Cos(a), Expr::Cos(b)) => {
            let arg_sum = Expr::Add(a.clone().boxed(), b.clone().boxed());
            let arg_diff = Expr::Sub(a.clone().boxed(), b.clone().boxed());
            let term1 = integrate_linear_trig(TrigSimple::Cos, arg_sum, var)?;
            let term2 = integrate_linear_trig(TrigSimple::Cos, arg_diff, var)?;
            Expr::Mul(
                Expr::Constant(half).boxed(),
                Expr::Add(term1.boxed(), term2.boxed()).boxed(),
            )
        }
        (Expr::Sinh(a), Expr::Sinh(b)) => {
            let arg_sum = Expr::Add(a.clone().boxed(), b.clone().boxed());
            let arg_diff = Expr::Sub(a.clone().boxed(), b.clone().boxed());
            let term1 = integrate_linear_hyperbolic(HyperbolicSimple::Cosh, arg_sum, var)?;
            let term2 = integrate_linear_hyperbolic(HyperbolicSimple::Cosh, arg_diff, var)?;
            Expr::Mul(
                Expr::Constant(half).boxed(),
                Expr::Sub(term1.boxed(), term2.boxed()).boxed(),
            )
        }
        (Expr::Sinh(a), Expr::Cosh(b)) | (Expr::Cosh(b), Expr::Sinh(a)) => {
            let arg_sum = Expr::Add(a.clone().boxed(), b.clone().boxed());
            let arg_diff = Expr::Sub(a.clone().boxed(), b.clone().boxed());
            let term1 = integrate_linear_hyperbolic(HyperbolicSimple::Sinh, arg_sum, var)?;
            let term2 = integrate_linear_hyperbolic(HyperbolicSimple::Sinh, arg_diff, var)?;
            Expr::Mul(
                Expr::Constant(half).boxed(),
                Expr::Add(term1.boxed(), term2.boxed()).boxed(),
            )
        }
        (Expr::Cosh(a), Expr::Cosh(b)) => {
            let arg_sum = Expr::Add(a.clone().boxed(), b.clone().boxed());
            let arg_diff = Expr::Sub(a.clone().boxed(), b.clone().boxed());
            let term1 = integrate_linear_hyperbolic(HyperbolicSimple::Cosh, arg_sum, var)?;
            let term2 = integrate_linear_hyperbolic(HyperbolicSimple::Cosh, arg_diff, var)?;
            Expr::Mul(
                Expr::Constant(half).boxed(),
                Expr::Add(term1.boxed(), term2.boxed()).boxed(),
            )
        }
        _ => return None,
    };

    if is_const_one(&const_expr) {
        Some(simplify(combined))
    } else {
        Some(simplify(Expr::Mul(const_expr.boxed(), combined.boxed())))
    }
}

#[derive(Clone, Copy)]
enum TrigSimple {
    Sin,
    Cos,
}

fn integrate_linear_trig(func: TrigSimple, arg: Expr, var: &str) -> Option<Expr> {
    if !contains_var(&arg, var) {
        let base = match func {
            TrigSimple::Sin => Expr::Sin(arg.boxed()),
            TrigSimple::Cos => Expr::Cos(arg.boxed()),
        };
        return Some(Expr::Mul(base.boxed(), Expr::Variable(var.to_string()).boxed()));
    }
    let k = coeff_of_var(&arg, var)?;
    let base = match func {
        TrigSimple::Sin => Expr::Neg(Expr::Cos(arg.boxed()).boxed()),
        TrigSimple::Cos => Expr::Sin(arg.boxed()),
    };
    Some(scale_by_coeff(base, k))
}

#[derive(Clone, Copy)]
enum HyperbolicSimple {
    Sinh,
    Cosh,
}

fn integrate_linear_hyperbolic(func: HyperbolicSimple, arg: Expr, var: &str) -> Option<Expr> {
    if !contains_var(&arg, var) {
        let base = match func {
            HyperbolicSimple::Sinh => Expr::Sinh(arg.boxed()),
            HyperbolicSimple::Cosh => Expr::Cosh(arg.boxed()),
        };
        return Some(Expr::Mul(base.boxed(), Expr::Variable(var.to_string()).boxed()));
    }
    let k = coeff_of_var(&arg, var)?;
    let base = match func {
        HyperbolicSimple::Sinh => Expr::Cosh(arg.boxed()),
        HyperbolicSimple::Cosh => Expr::Sinh(arg.boxed()),
    };
    Some(scale_by_coeff(base, k))
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
