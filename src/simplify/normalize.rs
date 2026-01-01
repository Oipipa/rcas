use std::collections::{BTreeSet, HashMap};

use crate::expr::{Expr, Rational};
use crate::polynomial::Poly;
use crate::simplify::{simplify_add, simplify_fully, simplify_mul, simplify_neg, simplify_pow, simplify_sub};
use num_traits::{One, Signed, ToPrimitive, Zero};

const NORMALIZE_SIZE_LIMIT: usize = 160;

#[derive(Clone, Debug)]
struct LinearForm {
    coeff: Rational,
    constant: Rational,
    var: Option<String>,
}

pub fn normalize(expr: Expr) -> Expr {
    normalize_with_limit(expr, NORMALIZE_SIZE_LIMIT)
}

pub fn normalize_with_limit(expr: Expr, size_limit: usize) -> Expr {
    let simplified = simplify_fully(expr);
    normalize_once(simplified, size_limit)
}

fn normalize_once(expr: Expr, size_limit: usize) -> Expr {
    if expr_size(&expr) > size_limit {
        return simplify_fully(expr);
    }

    match expr {
        Expr::Add(a, b) => {
            let left = normalize_once(*a, size_limit);
            let right = normalize_once(*b, size_limit);
            if let Some(factored) = factor_pair(&left, &right, size_limit) {
                factored
            } else {
                simplify_add(left, right)
            }
        }
        Expr::Sub(a, b) => {
            let left = normalize_once(*a, size_limit);
            let right = normalize_once(*b, size_limit);
            if let Some(factored) = factor_pair(&left, &simplify_neg(right.clone()), size_limit) {
                factored
            } else {
                simplify_sub(left, right)
            }
        }
        Expr::Mul(_, _) | Expr::Div(_, _) => normalize_product(expr, size_limit),
        Expr::Pow(base, exp) => normalize_pow_form(*base, *exp, size_limit),
        Expr::Neg(inner) => simplify_neg(normalize_once(*inner, size_limit)),
        Expr::Sin(inner) => Expr::Sin(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Cos(inner) => Expr::Cos(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Tan(inner) => Expr::Tan(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Sec(inner) => Expr::Sec(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Csc(inner) => Expr::Csc(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Cot(inner) => Expr::Cot(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Atan(inner) => Expr::Atan(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Asin(inner) => Expr::Asin(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Acos(inner) => Expr::Acos(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Asec(inner) => Expr::Asec(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Acsc(inner) => Expr::Acsc(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Acot(inner) => Expr::Acot(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Sinh(inner) => Expr::Sinh(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Cosh(inner) => Expr::Cosh(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Tanh(inner) => Expr::Tanh(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Asinh(inner) => Expr::Asinh(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Acosh(inner) => Expr::Acosh(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Atanh(inner) => Expr::Atanh(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Exp(inner) => Expr::Exp(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Log(inner) => Expr::Log(normalize_linear_arg(*inner, size_limit).boxed()),
        Expr::Abs(inner) => Expr::Abs(normalize_linear_arg(*inner, size_limit).boxed()),
        other => other,
    }
}

fn normalize_product(expr: Expr, size_limit: usize) -> Expr {
    let (mut const_factor, factors) = collect_product(&expr);
    if const_factor.is_zero() {
        return Expr::Constant(Rational::zero());
    }

    let mut exponents: HashMap<Expr, Rational> = HashMap::new();
    for factor in factors {
        let normalized = normalize_once(factor, size_limit);
        let (c_inner, inner_factors) = collect_product(&normalized);
        const_factor *= c_inner;
        if const_factor.is_zero() {
            return Expr::Constant(Rational::zero());
        }
        for inner in inner_factors {
            match inner {
                Expr::Constant(c) => {
                    const_factor *= c;
                    if const_factor.is_zero() {
                        return Expr::Constant(Rational::zero());
                    }
                }
                Expr::Pow(base, exp) => {
                    if let Expr::Constant(e) = *exp {
                        if let Expr::Pow(inner_base, inner_exp) = *base {
                            if let Expr::Constant(inner_e) = *inner_exp {
                                add_exponent(&mut exponents, *inner_base, inner_e * e.clone());
                                continue;
                            } else {
                                let rebuilt = Expr::Pow(inner_base, inner_exp);
                                add_exponent(&mut exponents, rebuilt, e);
                                continue;
                            }
                        }
                        add_exponent(&mut exponents, *base, e);
                    } else {
                        add_exponent(&mut exponents, Expr::Pow(base, exp), Rational::one());
                    }
                }
                other => add_exponent(&mut exponents, other, Rational::one()),
            }
        }
    }

    let mut num_exps: HashMap<Expr, Rational> = HashMap::new();
    let mut den_exps: HashMap<Expr, Rational> = HashMap::new();
    for (base, exp) in exponents.iter() {
        if exp.is_zero() {
            continue;
        }
        if exp.is_negative() {
            den_exps.insert(base.clone(), -exp.clone());
        } else {
            num_exps.insert(base.clone(), exp.clone());
        }
    }

    if !den_exps.is_empty() {
        let numerator = build_product_from_parts(const_factor.clone(), num_exps);
        let denominator = build_product_from_parts(Rational::one(), den_exps);
        if !has_composite_power(&numerator) && !has_composite_power(&denominator) {
            if let Some((num_simplified, den_simplified)) =
                cancel_polynomial_gcd(&numerator, &denominator)
            {
                return rebuild_rational_from_expr(num_simplified, den_simplified);
            }
        }
    }

    let mut items: Vec<(Expr, Rational)> = exponents
        .into_iter()
        .filter(|(_, e)| !e.is_zero())
        .collect();
    items.sort_by(|(a, _), (b, _)| a.cmp(b));

    let mut result = if const_factor.is_one() {
        None
    } else {
        Some(Expr::Constant(const_factor))
    };

    for (base, exp) in items {
        let factor = if exp == Rational::one() {
            base
        } else {
            simplify_pow(base, Expr::Constant(exp))
        };
        result = Some(match result {
            None => factor,
            Some(acc) => simplify_mul(acc, factor),
        });
    }

    result.unwrap_or_else(|| Expr::Constant(Rational::one()))
}

fn normalize_pow_form(base: Expr, exp: Expr, size_limit: usize) -> Expr {
    let base_norm = normalize_once(base, size_limit);
    let exp_norm = normalize_once(exp, size_limit);

    let maybe_const_exp = match &exp_norm {
        Expr::Constant(c) => Some(c.clone()),
        _ => None,
    };

    // Collapse nested powers only when the outer exponent is an integer to avoid branch changes.
    if let Some(e_outer) = maybe_const_exp.clone() {
        if e_outer.is_integer() {
            if let Expr::Pow(inner_base, inner_exp) = &base_norm {
                if let Expr::Constant(e_inner) = &**inner_exp {
                    let combined = Expr::Constant(e_inner.clone() * e_outer);
                    let merged = simplify_pow((**inner_base).clone(), combined);
                    return normalize_once(merged, size_limit);
                }
            }
        }
    }

    // Distribute over products for integer exponents.
    if let Some(e) = maybe_const_exp.clone() {
        if e.is_integer() {
            if let Some(distributed) = distribute_pow_over_product(&base_norm, &e, size_limit) {
                return simplify_fully(distributed);
            }
            if let Some(factored) = factor_linear_power(&base_norm, &e) {
                return simplify_fully(factored);
            }
        }
    }

    simplify_pow(base_norm, exp_norm)
}

fn normalize_linear_arg(arg: Expr, size_limit: usize) -> Expr {
    let normalized = normalize_once(arg, size_limit);
    standardize_linear(normalized)
}

fn standardize_linear(expr: Expr) -> Expr {
    let form = match linear_form(&expr) {
        Some(l) => l,
        None => return expr,
    };

    if form.coeff.is_zero() {
        return Expr::Constant(form.constant);
    }

    let var = form
        .var
        .map(Expr::Variable)
        .unwrap_or_else(|| Expr::Variable("x".into()));

    let core = simplify_mul(Expr::Constant(form.coeff), var);
    if form.constant.is_zero() {
        core
    } else {
        simplify_add(core, Expr::Constant(form.constant))
    }
}

fn factor_linear_power(base: &Expr, exp: &Rational) -> Option<Expr> {
    let form = linear_form(base)?;
    if form.coeff.is_zero() {
        return None;
    }
    let var = form
        .var
        .map(Expr::Variable)
        .unwrap_or_else(|| Expr::Variable("x".into()));
    let adjusted_const = form.constant / form.coeff.clone();
    let inner = if adjusted_const.is_zero() {
        var
    } else {
        simplify_add(var, Expr::Constant(adjusted_const))
    };
    let pow_inner = simplify_pow(inner, Expr::Constant(exp.clone()));
    let coeff_pow = pow_rational(&form.coeff, exp);
    let prefactor = Expr::Constant(coeff_pow);
    Some(simplify_mul(prefactor, pow_inner))
}

fn distribute_pow_over_product(base: &Expr, exp: &Rational, _size_limit: usize) -> Option<Expr> {
    let (mut const_factor, factors) = collect_product(base);
    if factors.is_empty() || (factors.len() == 1 && const_factor.is_one()) {
        return None;
    }


    const_factor = pow_rational(&const_factor, exp);
    let mut exps: HashMap<Expr, Rational> = HashMap::new();
    for f in factors {
        match f {
            Expr::Pow(base, inner_exp) => {
                if let Expr::Constant(inner_e) = *inner_exp {
                    add_exponent(&mut exps, *base, inner_e * exp.clone());
                } else {
                    add_exponent(&mut exps, Expr::Pow(base, inner_exp), exp.clone());
                }
            }
            other => add_exponent(&mut exps, other, exp.clone()),
        }
    }

    let mut items: Vec<(Expr, Rational)> = exps.into_iter().collect();
    items.sort_by(|(a, _), (b, _)| a.cmp(b));

    let mut result = if const_factor.is_one() {
        None
    } else {
        Some(Expr::Constant(const_factor))
    };

    for (base, exponent) in items {
        let factor = simplify_pow(base, Expr::Constant(exponent));
        result = Some(match result {
            None => factor,
            Some(acc) => simplify_mul(acc, factor),
        });
    }

    result
}

fn add_exponent(map: &mut HashMap<Expr, Rational>, base: Expr, exp: Rational) {
    map.entry(base)
        .and_modify(|e| *e += &exp)
        .or_insert(exp);
}

fn build_product_from_parts(const_factor: Rational, exponents: HashMap<Expr, Rational>) -> Expr {
    if const_factor.is_zero() {
        return Expr::Constant(Rational::zero());
    }
    let mut items: Vec<(Expr, Rational)> = exponents
        .into_iter()
        .filter(|(_, e)| !e.is_zero())
        .collect();
    items.sort_by(|(a, _), (b, _)| a.cmp(b));

    let mut result = if const_factor.is_one() {
        None
    } else {
        Some(Expr::Constant(const_factor))
    };

    for (base, exp) in items {
        let factor = simplify_pow(base, Expr::Constant(exp));
        result = Some(match result {
            None => factor,
            Some(acc) => simplify_mul(acc, factor),
        });
    }

    result.unwrap_or_else(|| Expr::Constant(Rational::one()))
}

fn exponent_map(factors: Vec<Expr>) -> HashMap<Expr, Rational> {
    let mut exps = HashMap::new();
    for f in factors {
        match f {
            Expr::Pow(base, exp) => {
                if let Expr::Constant(e) = *exp {
                    if let Expr::Pow(inner_base, inner_exp) = *base {
                        if let Expr::Constant(inner_e) = *inner_exp {
                            add_exponent(&mut exps, *inner_base, inner_e * e.clone());
                            continue;
                        } else {
                            let rebuilt = Expr::Pow(inner_base, inner_exp);
                            add_exponent(&mut exps, rebuilt, e);
                            continue;
                        }
                    }
                    add_exponent(&mut exps, *base, e);
                } else {
                    add_exponent(&mut exps, Expr::Pow(base, exp), Rational::one());
                }
            }
            other => add_exponent(&mut exps, other, Rational::one()),
        }
    }
    exps
}

fn factor_pair(left: &Expr, right: &Expr, _size_limit: usize) -> Option<Expr> {
    let (c1, f1) = collect_product(left);
    let (c2, f2) = collect_product(right);
    if c1.is_zero() || c2.is_zero() {
        return None;
    }

    let mut exps1 = exponent_map(f1);
    let mut exps2 = exponent_map(f2);

    let mut common: HashMap<Expr, Rational> = HashMap::new();
    for (base, exp1) in exps1.clone() {
        if let Some(exp2) = exps2.get(&base) {
            let common_exp = if exp1 <= *exp2 { exp1 } else { exp2.clone() };
            if !common_exp.is_zero() {
                common.insert(base, common_exp);
            }
        }
    }

    if common.is_empty() {
        return None;
    }

    for (base, common_exp) in &common {
        if let Some(e1) = exps1.get_mut(base) {
            *e1 -= common_exp.clone();
        }
        if let Some(e2) = exps2.get_mut(base) {
            *e2 -= common_exp.clone();
        }
    }

    let common_expr = build_product_from_parts(Rational::one(), common);
    let left_rest = build_product_from_parts(c1, exps1);
    let right_rest = build_product_from_parts(c2, exps2);

    let factored = Expr::Mul(common_expr.boxed(), simplify_add(left_rest, right_rest).boxed());
    Some(factored)
}

fn collect_product(expr: &Expr) -> (Rational, Vec<Expr>) {
    match expr {
        Expr::Constant(c) => (c.clone(), Vec::new()),
        Expr::Neg(inner) => {
            let (c, f) = collect_product(inner);
            (-c, f)
        }
        Expr::Mul(a, b) => {
            let (ca, mut fa) = collect_product(a);
            let (cb, mut fb) = collect_product(b);
            fa.append(&mut fb);
            (ca * cb, fa)
        }
        Expr::Div(a, b) => {
            let (ca, mut fa) = collect_product(a);
            let (cb, fb) = collect_product(b);
            for factor in fb {
                fa.push(Expr::Pow(
                    factor.boxed(),
                    Expr::Constant(Rational::from_integer((-1).into())).boxed(),
                ));
            }
            (ca / cb, fa)
        }
        other => (Rational::one(), vec![other.clone()]),
    }
}

fn linear_form(expr: &Expr) -> Option<LinearForm> {
    match expr {
        Expr::Variable(v) => Some(LinearForm {
            coeff: Rational::one(),
            constant: Rational::zero(),
            var: Some(v.clone()),
        }),
        Expr::Constant(c) => Some(LinearForm {
            coeff: Rational::zero(),
            constant: c.clone(),
            var: None,
        }),
        Expr::Neg(inner) => {
            let form = linear_form(inner)?;
            Some(LinearForm {
                coeff: -form.coeff,
                constant: -form.constant,
                var: form.var,
            })
        }
        Expr::Mul(a, b) => match (&**a, &**b) {
            (Expr::Constant(c), Expr::Variable(v))
            | (Expr::Variable(v), Expr::Constant(c)) => Some(LinearForm {
                coeff: c.clone(),
                constant: Rational::zero(),
                var: Some(v.clone()),
            }),
            _ => None,
        },
        Expr::Add(a, b) => {
            let left = linear_form(a)?;
            let right = linear_form(b)?;
            combine_linear(left, right)
        }
        Expr::Sub(a, b) => {
            let left = linear_form(a)?;
            let right = linear_form(b)?;
            combine_linear(left, LinearForm {
                coeff: -right.coeff,
                constant: -right.constant,
                var: right.var,
            })
        }
        _ => None,
    }
}

fn combine_linear(lhs: LinearForm, rhs: LinearForm) -> Option<LinearForm> {
    let var = match (&lhs.var, &rhs.var) {
        (None, None) => None,
        (Some(v), None) | (None, Some(v)) => Some(v.clone()),
        (Some(a), Some(b)) if a == b => Some(a.clone()),
        _ => return None,
    };

    Some(LinearForm {
        coeff: lhs.coeff + rhs.coeff,
        constant: lhs.constant + rhs.constant,
        var,
    })
}

fn pow_rational(base: &Rational, exp: &Rational) -> Rational {
    if exp.is_zero() {
        return Rational::one();
    }
    if !exp.is_integer() {
        return base.clone();
    }
    let n = exp.to_integer();
    if let Some(pow) = n.abs().to_u32() {
        let num = base.numer().pow(pow);
        let den = base.denom().pow(pow);
        if n.is_negative() {
            return Rational::new(den, num);
        } else {
            return Rational::new(num, den);
        }
    }
    base.clone()
}

fn expr_size(expr: &Expr) -> usize {
    match expr {
        Expr::Variable(_) | Expr::Constant(_) => 1,
        Expr::Neg(inner)
        | Expr::Sin(inner)
        | Expr::Cos(inner)
        | Expr::Tan(inner)
        | Expr::Sec(inner)
        | Expr::Csc(inner)
        | Expr::Cot(inner)
        | Expr::Atan(inner)
        | Expr::Asin(inner)
        | Expr::Acos(inner)
        | Expr::Asec(inner)
        | Expr::Acsc(inner)
        | Expr::Acot(inner)
        | Expr::Sinh(inner)
        | Expr::Cosh(inner)
        | Expr::Tanh(inner)
        | Expr::Asinh(inner)
        | Expr::Acosh(inner)
        | Expr::Atanh(inner)
        | Expr::Exp(inner)
        | Expr::Log(inner)
        | Expr::Abs(inner) => 1 + expr_size(inner),
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => 1 + expr_size(a) + expr_size(b),
    }
}

fn collect_vars(expr: &Expr, vars: &mut BTreeSet<String>) {
    match expr {
        Expr::Variable(name) => {
            vars.insert(name.clone());
        }
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => {
            collect_vars(a, vars);
            collect_vars(b, vars);
        }
        Expr::Neg(inner)
        | Expr::Sin(inner)
        | Expr::Cos(inner)
        | Expr::Tan(inner)
        | Expr::Sec(inner)
        | Expr::Csc(inner)
        | Expr::Cot(inner)
        | Expr::Atan(inner)
        | Expr::Asin(inner)
        | Expr::Acos(inner)
        | Expr::Asec(inner)
        | Expr::Acsc(inner)
        | Expr::Acot(inner)
        | Expr::Sinh(inner)
        | Expr::Cosh(inner)
        | Expr::Tanh(inner)
        | Expr::Asinh(inner)
        | Expr::Acosh(inner)
        | Expr::Atanh(inner)
        | Expr::Exp(inner)
        | Expr::Log(inner)
        | Expr::Abs(inner) => collect_vars(inner, vars),
        Expr::Constant(_) => {}
    }
}

fn has_composite_power(expr: &Expr) -> bool {
    match expr {
        Expr::Pow(base, exp) => {
            let composite_base = !matches!(**base, Expr::Variable(_) | Expr::Constant(_));
            composite_base || has_composite_power(base) || has_composite_power(exp)
        }
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b) => has_composite_power(a) || has_composite_power(b),
        Expr::Neg(inner)
        | Expr::Sin(inner)
        | Expr::Cos(inner)
        | Expr::Tan(inner)
        | Expr::Sec(inner)
        | Expr::Csc(inner)
        | Expr::Cot(inner)
        | Expr::Atan(inner)
        | Expr::Asin(inner)
        | Expr::Acos(inner)
        | Expr::Asec(inner)
        | Expr::Acsc(inner)
        | Expr::Acot(inner)
        | Expr::Sinh(inner)
        | Expr::Cosh(inner)
        | Expr::Tanh(inner)
        | Expr::Asinh(inner)
        | Expr::Acosh(inner)
        | Expr::Atanh(inner)
        | Expr::Exp(inner)
        | Expr::Log(inner)
        | Expr::Abs(inner) => has_composite_power(inner),
        Expr::Variable(_) | Expr::Constant(_) => false,
    }
}

fn cancel_polynomial_gcd(numerator: &Expr, denominator: &Expr) -> Option<(Expr, Expr)> {
    let mut vars = BTreeSet::new();
    collect_vars(numerator, &mut vars);
    collect_vars(denominator, &mut vars);
    if vars.len() != 1 {
        return None;
    }
    let var = vars.into_iter().next()?;
    let num_poly = Poly::from_expr(numerator, &var)?;
    let den_poly = Poly::from_expr(denominator, &var)?;
    if den_poly.is_zero() {
        return None;
    }
    if num_poly.is_zero() {
        return Some((
            Expr::Constant(Rational::zero()),
            Expr::Constant(Rational::one()),
        ));
    }
    let gcd = Poly::gcd(&num_poly, &den_poly);
    let num_reduced = num_poly.div_exact(&gcd)?;
    let den_reduced = den_poly.div_exact(&gcd)?;
    let num_lc = num_reduced.leading_coeff();
    let den_lc = den_reduced.leading_coeff();
    let scale = num_lc / den_lc;
    let num_expr = simplify_fully(num_reduced.monic().to_expr(&var));
    let den_expr = simplify_fully(den_reduced.monic().to_expr(&var));
    let scaled_num = if scale.is_one() {
        num_expr
    } else {
        simplify_mul(Expr::Constant(scale), num_expr)
    };
    Some((scaled_num, den_expr))
}

fn rebuild_rational_from_expr(numerator: Expr, denominator: Expr) -> Expr {
    let (c_num, f_num) = collect_product(&numerator);
    let (c_den, f_den) = collect_product(&denominator);
    if c_den.is_zero() {
        return Expr::Div(numerator.boxed(), denominator.boxed());
    }
    let mut exps = exponent_map(f_num);
    let den_exps = exponent_map(f_den);
    for (base, exp) in den_exps {
        add_exponent(&mut exps, base, -exp);
    }
    build_product_from_parts(c_num / c_den, exps)
}
