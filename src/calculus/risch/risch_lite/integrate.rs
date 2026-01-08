use num_traits::{One, Zero};

use crate::calculus::differentiate;
use crate::calculus::integrate::{
    apply_constant_factor, constant_ratio, contains_var, flatten_product, polynomial, rational,
    rebuild_product, split_constant_factors, to_rational_candidate,
};
use crate::core::expr::{Expr, Rational};
use crate::simplify::{simplify, simplify_fully};

use super::tower::{GeneratorKind, Tower};
use super::utils::contains_subexpr;

pub(super) fn log_derivative(expr: &Expr, var: &str) -> Option<(Expr, Expr)> {
    if let Expr::Div(num, den) = expr {
        let deriv = simplify_fully(differentiate(var, den));
        if !deriv.is_zero() {
            if let Some(coeff) = constant_ratio(num, &deriv, var) {
                return Some((coeff, (*den.clone()).clone()));
            }
        }
    }

    let (const_expr, factors) = split_constant_factors(expr, var);
    for (idx, factor) in factors.iter().enumerate() {
        let candidate = match factor {
            Expr::Pow(base, exp) if is_negative_one(exp) => (*base.clone()).clone(),
            _ => continue,
        };
        let deriv = simplify_fully(differentiate(var, &candidate));
        if deriv.is_zero() {
            continue;
        }
        let remaining: Vec<Expr> = factors
            .iter()
            .enumerate()
            .filter_map(|(i, f)| if i == idx { None } else { Some(f.clone()) })
            .collect();
        let remaining_expr =
            apply_constant_factor(const_expr.clone(), rebuild_product(Rational::one(), remaining));
        if let Some(coeff) = constant_ratio(&remaining_expr, &deriv, var) {
            return Some((coeff, candidate));
        }
    }

    None
}

pub(super) fn integrate_in_tower(expr: &Expr, var: &str, tower: &Tower) -> Option<(Expr, String)> {
    for (idx, generator) in tower.generators.iter().enumerate().rev() {
        if !contains_subexpr(expr, &generator.expr) {
            continue;
        }
        let t_name = format!("__t{idx}");
        let t_var = Expr::Variable(t_name.clone());
        let replaced = replace_expr(expr, &generator.expr, &t_var);

        let integrand_t = match generator.kind {
            GeneratorKind::Exp => {
                let denom = Expr::Mul(generator.arg_deriv.clone().boxed(), t_var.clone().boxed());
                cancel_common_factors(replaced, denom, var)
            }
            GeneratorKind::Log => {
                let scale = Expr::Div(
                    generator.arg_deriv.clone().boxed(),
                    generator.arg.clone().boxed(),
                );
                cancel_common_factors(replaced, scale, var)
            }
        };

        let integrand_t = normalize_rational_candidate(integrand_t);
        let integrand_t = simplify_fully(integrand_t);
        if contains_var(&integrand_t, var) {
            continue;
        }

        let result_t = polynomial::integrate(&integrand_t, &t_name)
            .or_else(|| rational::integrate(&integrand_t, &t_name));
        let Some(result_t) = result_t else {
            continue;
        };
        let target = Expr::Variable(t_name);
        let restored = replace_expr(&result_t, &target, &generator.expr);
        return Some((
            simplify(restored),
            format!("tower substitution {}", generator.kind.label()),
        ));
    }
    None
}

fn cancel_common_factors(numer: Expr, denom: Expr, var: &str) -> Expr {
    let mut numer = numer;
    let (mut c_num, mut f_num) = flatten_product(&numer);
    let (c_den, mut f_den) = flatten_product(&denom);
    if matches!(numer, Expr::Add(_, _) | Expr::Sub(_, _) | Expr::Neg(_)) && !f_den.is_empty() {
        let (factored, remaining_den) = factor_sum_common_factors(numer, &f_den, var);
        if remaining_den.len() != f_den.len() {
            numer = factored;
            f_den = remaining_den;
            let (c_next, f_next) = flatten_product(&numer);
            c_num = c_next;
            f_num = f_next;
        }
    }
    let mut i = 0;
    while i < f_den.len() {
        if let Some(pos) = f_num.iter().position(|f| f == &f_den[i]) {
            f_num.remove(pos);
            f_den.remove(i);
        } else {
            let mut matched = None;
            for (idx, factor) in f_num.iter().enumerate() {
                if let Some(ratio) = constant_ratio(factor, &f_den[i], var) {
                    matched = Some((idx, ratio));
                    break;
                }
            }
            if let Some((idx, ratio)) = matched {
                f_num.remove(idx);
                match ratio {
                    Expr::Constant(c) => {
                        c_num *= c;
                    }
                    _ => f_num.push(ratio),
                }
                f_den.remove(i);
            } else {
                i += 1;
            }
        }
    }
    let num_expr = rebuild_product(c_num, f_num);
    let den_expr = rebuild_product(c_den, f_den);
    Expr::Div(num_expr.boxed(), den_expr.boxed())
}

fn factor_sum_common_factors(numer: Expr, den_factors: &[Expr], var: &str) -> (Expr, Vec<Expr>) {
    let terms = flatten_sum_terms(&numer);
    let mut term_parts: Vec<(Rational, Vec<Expr>)> =
        terms.iter().map(|term| flatten_product(term)).collect();
    let mut remaining_den = den_factors.to_vec();

    let mut idx = 0;
    while idx < remaining_den.len() {
        let factor = &remaining_den[idx];
        let all_have = term_parts.iter().all(|(c, factors)| {
            if c.is_zero() {
                true
            } else if factors.iter().any(|f| f == factor) {
                true
            } else {
                factors
                    .iter()
                    .any(|f| constant_ratio(f, factor, var).is_some())
            }
        });
        if all_have {
            for (c, factors) in term_parts.iter_mut() {
                if c.is_zero() {
                    continue;
                }
                if let Some(pos) = factors.iter().position(|f| f == factor) {
                    factors.remove(pos);
                    continue;
                }
                if let Some((pos, ratio)) = factors
                    .iter()
                    .enumerate()
                    .find_map(|(i, f)| constant_ratio(f, factor, var).map(|r| (i, r)))
                {
                    factors.remove(pos);
                    match ratio {
                        Expr::Constant(k) => {
                            *c *= k;
                        }
                        _ => factors.push(ratio),
                    }
                }
            }
            remaining_den.remove(idx);
        } else {
            idx += 1;
        }
    }

    let rebuilt_terms: Vec<Expr> = term_parts
        .into_iter()
        .map(|(c, factors)| rebuild_product(c, factors))
        .collect();
    (rebuild_sum(rebuilt_terms), remaining_den)
}

fn flatten_sum_terms(expr: &Expr) -> Vec<Expr> {
    match expr {
        Expr::Add(a, b) => {
            let mut out = flatten_sum_terms(a);
            out.extend(flatten_sum_terms(b));
            out
        }
        Expr::Sub(a, b) => {
            let mut out = flatten_sum_terms(a);
            out.extend(
                flatten_sum_terms(b)
                    .into_iter()
                    .map(|term| Expr::Neg(term.boxed())),
            );
            out
        }
        Expr::Neg(inner) => flatten_sum_terms(inner)
            .into_iter()
            .map(|term| Expr::Neg(term.boxed()))
            .collect(),
        _ => vec![expr.clone()],
    }
}

fn rebuild_sum(terms: Vec<Expr>) -> Expr {
    let mut iter = terms.into_iter();
    let Some(first) = iter.next() else {
        return Expr::Constant(Rational::zero());
    };
    iter.fold(first, |acc, term| Expr::Add(acc.boxed(), term.boxed()))
}

fn normalize_rational_candidate(expr: Expr) -> Expr {
    let (constant, factors) = flatten_product(&expr);
    if let Some(rational) = to_rational_candidate(constant, &factors) {
        simplify_fully(rational)
    } else {
        expr
    }
}

fn is_negative_one(expr: &Expr) -> bool {
    match expr {
        Expr::Constant(c) => *c == -Rational::one(),
        Expr::Neg(inner) => matches!(&**inner, Expr::Constant(c) if *c == Rational::one()),
        _ => false,
    }
}

fn replace_expr(expr: &Expr, target: &Expr, replacement: &Expr) -> Expr {
    if expr == target {
        return replacement.clone();
    }
    match expr {
        Expr::Add(a, b) => Expr::Add(
            replace_expr(a, target, replacement).boxed(),
            replace_expr(b, target, replacement).boxed(),
        ),
        Expr::Sub(a, b) => Expr::Sub(
            replace_expr(a, target, replacement).boxed(),
            replace_expr(b, target, replacement).boxed(),
        ),
        Expr::Mul(a, b) => Expr::Mul(
            replace_expr(a, target, replacement).boxed(),
            replace_expr(b, target, replacement).boxed(),
        ),
        Expr::Div(a, b) => Expr::Div(
            replace_expr(a, target, replacement).boxed(),
            replace_expr(b, target, replacement).boxed(),
        ),
        Expr::Pow(a, b) => Expr::Pow(
            replace_expr(a, target, replacement).boxed(),
            replace_expr(b, target, replacement).boxed(),
        ),
        Expr::Neg(inner) => Expr::Neg(replace_expr(inner, target, replacement).boxed()),
        Expr::Sin(inner) => Expr::Sin(replace_expr(inner, target, replacement).boxed()),
        Expr::Cos(inner) => Expr::Cos(replace_expr(inner, target, replacement).boxed()),
        Expr::Tan(inner) => Expr::Tan(replace_expr(inner, target, replacement).boxed()),
        Expr::Sec(inner) => Expr::Sec(replace_expr(inner, target, replacement).boxed()),
        Expr::Csc(inner) => Expr::Csc(replace_expr(inner, target, replacement).boxed()),
        Expr::Cot(inner) => Expr::Cot(replace_expr(inner, target, replacement).boxed()),
        Expr::Atan(inner) => Expr::Atan(replace_expr(inner, target, replacement).boxed()),
        Expr::Asin(inner) => Expr::Asin(replace_expr(inner, target, replacement).boxed()),
        Expr::Acos(inner) => Expr::Acos(replace_expr(inner, target, replacement).boxed()),
        Expr::Asec(inner) => Expr::Asec(replace_expr(inner, target, replacement).boxed()),
        Expr::Acsc(inner) => Expr::Acsc(replace_expr(inner, target, replacement).boxed()),
        Expr::Acot(inner) => Expr::Acot(replace_expr(inner, target, replacement).boxed()),
        Expr::Sinh(inner) => Expr::Sinh(replace_expr(inner, target, replacement).boxed()),
        Expr::Cosh(inner) => Expr::Cosh(replace_expr(inner, target, replacement).boxed()),
        Expr::Tanh(inner) => Expr::Tanh(replace_expr(inner, target, replacement).boxed()),
        Expr::Asinh(inner) => Expr::Asinh(replace_expr(inner, target, replacement).boxed()),
        Expr::Acosh(inner) => Expr::Acosh(replace_expr(inner, target, replacement).boxed()),
        Expr::Atanh(inner) => Expr::Atanh(replace_expr(inner, target, replacement).boxed()),
        Expr::Exp(inner) => Expr::Exp(replace_expr(inner, target, replacement).boxed()),
        Expr::Log(inner) => Expr::Log(replace_expr(inner, target, replacement).boxed()),
        Expr::Abs(inner) => Expr::Abs(replace_expr(inner, target, replacement).boxed()),
        Expr::Variable(_) | Expr::Constant(_) => expr.clone(),
    }
}
