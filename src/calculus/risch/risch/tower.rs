use std::collections::{HashMap, HashSet};

use num_bigint::BigInt;
use num_traits::ToPrimitive;

use crate::calculus::integrate::contains_var;
use crate::calculus::risch::diff_field::{ExtensionKind, FieldElement, Tower};
use crate::core::expr::{Expr, Rational};

use super::utils::extract_rational_const;

pub(super) fn build_tower(expr: &Expr, var: &str) -> Result<Tower, String> {
    let mut generators = HashSet::new();
    let mut saw_abs_log = false;
    collect_generators(expr, var, &mut generators, &mut saw_abs_log);
    if saw_abs_log {
        return Err("log(abs(..)) not supported".to_string());
    }

    if generators.is_empty() {
        return Ok(Tower::new(var));
    }

    let mut gens_vec: Vec<Expr> = generators.into_iter().collect();
    gens_vec.sort();

    let mut deps: HashMap<Expr, Vec<Expr>> = HashMap::new();
    for gen_expr in &gens_vec {
        let arg = match gen_expr {
            Expr::Exp(inner) | Expr::Log(inner) => inner.as_ref(),
            Expr::Pow(base, _) if algebraic_degree_from_generator(gen_expr).is_some() => {
                base.as_ref()
            }
            _ => continue,
        };
        let mut dep_list = Vec::new();
        for other in &gens_vec {
            if other == gen_expr {
                continue;
            }
            if contains_subexpr(arg, other) {
                dep_list.push(other.clone());
            }
        }
        deps.insert(gen_expr.clone(), dep_list);
    }

    let mut ordered = Vec::new();
    let mut remaining = gens_vec.clone();
    while !remaining.is_empty() {
        let mut next_index = None;
        for (idx, gen_expr) in remaining.iter().enumerate() {
            let ready = deps
                .get(gen_expr)
                .map(|items| items.iter().all(|dep| ordered.contains(dep)))
                .unwrap_or(true);
            if ready {
                next_index = Some(idx);
                break;
            }
        }
        let Some(idx) = next_index else {
            return Err("cyclic generator dependencies".to_string());
        };
        ordered.push(remaining.remove(idx));
    }

    let mut tower = Tower::new(var);
    for gen_expr in ordered {
        match gen_expr {
            Expr::Exp(inner) => {
                tower
                    .push_exp((*inner).clone())
                    .map_err(|err| err.to_string())?;
            }
            Expr::Log(inner) => match &*inner {
                Expr::Abs(_) => return Err("log(abs(..)) not supported".to_string()),
                _ => {
                    tower
                        .push_log((*inner).clone())
                        .map_err(|err| err.to_string())?;
                }
            },
            other => {
                let Some((base_expr, degree)) = algebraic_degree_from_generator(&other) else {
                    continue;
                };
                tower
                    .push_algebraic_root(base_expr, degree)
                    .map_err(|err| err.to_string())?;
            }
        }
    }

    Ok(tower)
}

fn collect_generators(expr: &Expr, var: &str, out: &mut HashSet<Expr>, saw_abs_log: &mut bool) {
    match expr {
        Expr::Exp(inner) => {
            if contains_var(inner, var) {
                out.insert(expr.clone());
            }
            collect_generators(inner, var, out, saw_abs_log);
        }
        Expr::Log(inner) => {
            if matches!(&**inner, Expr::Abs(_)) {
                *saw_abs_log = true;
            }
            if contains_var(inner, var) {
                out.insert(expr.clone());
            }
            collect_generators(inner, var, out, saw_abs_log);
        }
        Expr::Pow(base, exp) => {
            if let Some(root) = algebraic_root_candidate(base, exp) {
                if contains_var(base, var) {
                    out.insert(root);
                }
            }
            collect_generators(base, var, out, saw_abs_log);
            collect_generators(exp, var, out, saw_abs_log);
        }
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) => {
            collect_generators(a, var, out, saw_abs_log);
            collect_generators(b, var, out, saw_abs_log);
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
        | Expr::Abs(inner) => {
            collect_generators(inner, var, out, saw_abs_log);
        }
        Expr::Variable(_) | Expr::Constant(_) => {}
    }
}

fn algebraic_root_candidate(base: &Expr, exp: &Expr) -> Option<Expr> {
    let exp = extract_rational_const(exp)?;
    if exp.is_integer() {
        return None;
    }
    let degree = exp.denom().to_usize()?;
    if degree < 2 {
        return None;
    }
    let root_exp =
        Rational::from_integer(1.into()) / Rational::from_integer(BigInt::from(degree));
    Some(Expr::Pow(
        base.clone().boxed(),
        Expr::Constant(root_exp).boxed(),
    ))
}

fn algebraic_degree_from_generator(expr: &Expr) -> Option<(Expr, usize)> {
    let Expr::Pow(base, exp) = expr else {
        return None;
    };
    let exp = extract_rational_const(exp)?;
    if exp.numer() != &BigInt::from(1) {
        return None;
    }
    let degree = exp.denom().to_usize()?;
    if degree < 2 {
        return None;
    }
    Some((*base.clone(), degree))
}

fn contains_subexpr(expr: &Expr, target: &Expr) -> bool {
    if expr == target {
        return true;
    }
    match expr {
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => contains_subexpr(a, target) || contains_subexpr(b, target),
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
        | Expr::Abs(inner) => contains_subexpr(inner, target),
        Expr::Variable(_) | Expr::Constant(_) => false,
    }
}

pub(super) fn tower_prefix(tower: &Tower, len: usize) -> Option<Tower> {
    if len > tower.extensions().len() {
        return None;
    }
    let mut base = Tower::new(tower.base_var().to_string());
    for ext in tower.extensions().iter().take(len) {
        match ext.kind {
            ExtensionKind::Exp => match &ext.generator {
                Expr::Exp(inner) => {
                    base.push_exp((**inner).clone()).ok()?;
                }
                _ => return None,
            },
            ExtensionKind::Log => match &ext.generator {
                Expr::Log(inner) => {
                    base.push_log((**inner).clone()).ok()?;
                }
                _ => return None,
            },
            ExtensionKind::Algebraic => {
                let algebraic = ext.algebraic.as_ref()?;
                base.push_algebraic_root(algebraic.base.clone(), algebraic.degree)
                    .ok()?;
            }
        }
    }
    Some(base)
}

pub(super) fn derivative_in_tower(expr: &Expr, tower: &Tower) -> Option<Expr> {
    let elem = FieldElement::try_from_expr(expr, tower).ok()?;
    let deriv = elem.derivative().ok()?;
    Some(deriv.to_expr())
}

pub(super) fn is_constant_in_tower(expr: &Expr, tower: &Tower) -> Option<bool> {
    let elem = FieldElement::try_from_expr(expr, tower).ok()?;
    elem.is_constant().ok()
}

pub(super) fn lower_symbol_set(tower: &Tower) -> HashSet<String> {
    let mut symbols: Vec<String> = tower.extensions().iter().map(|ext| ext.symbol.clone()).collect();
    if !symbols.is_empty() {
        symbols.pop();
    }
    symbols.into_iter().collect()
}

pub(super) fn is_constant_wrt_base(expr: &Expr, var: &str, symbols: &HashSet<String>) -> bool {
    !contains_var(expr, var) && !contains_any_symbol(expr, symbols)
}

pub(super) fn contains_any_symbol(expr: &Expr, symbols: &HashSet<String>) -> bool {
    match expr {
        Expr::Variable(name) => symbols.contains(name),
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => contains_any_symbol(a, symbols) || contains_any_symbol(b, symbols),
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
        | Expr::Abs(inner) => contains_any_symbol(inner, symbols),
        Expr::Constant(_) => false,
    }
}
