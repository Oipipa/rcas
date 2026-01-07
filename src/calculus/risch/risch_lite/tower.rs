use std::collections::{HashMap, HashSet};

use crate::calculus::differentiate;
use crate::calculus::integrate::contains_var;
use crate::core::expr::Expr;
use crate::simplify::simplify_fully;

use super::utils::contains_subexpr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum GeneratorKind {
    Exp,
    Log,
}

impl GeneratorKind {
    pub(super) fn label(&self) -> &'static str {
        match self {
            GeneratorKind::Exp => "exp",
            GeneratorKind::Log => "log",
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct Generator {
    pub(super) kind: GeneratorKind,
    pub(super) expr: Expr,
    pub(super) arg: Expr,
    pub(super) arg_deriv: Expr,
}

#[derive(Debug, Clone)]
pub(super) struct Tower {
    pub(super) generators: Vec<Generator>,
}

pub(super) fn build_tower(expr: &Expr, var: &str) -> Result<Tower, String> {
    let mut generators = HashSet::new();
    let mut saw_abs_log = false;
    collect_generators(expr, var, &mut generators, &mut saw_abs_log);
    if saw_abs_log {
        return Err("log(abs(..)) not supported".to_string());
    }

    if generators.is_empty() {
        return Ok(Tower {
            generators: Vec::new(),
        });
    }

    let mut gens_vec: Vec<Expr> = generators.into_iter().collect();
    gens_vec.sort();

    let mut deps: HashMap<Expr, Vec<Expr>> = HashMap::new();
    for gen_expr in &gens_vec {
        let arg = match gen_expr {
            Expr::Exp(inner) | Expr::Log(inner) => inner.as_ref(),
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

    let mut available = Vec::new();
    let mut tower_gens = Vec::new();
    for gen_expr in ordered {
        let (kind, arg) = match &gen_expr {
            Expr::Exp(inner) => (GeneratorKind::Exp, (*inner.clone()).clone()),
            Expr::Log(inner) => match &**inner {
                Expr::Abs(_) => {
                    return Err("log(abs(..)) not supported".to_string());
                }
                _ => (GeneratorKind::Log, (*inner.clone()).clone()),
            },
            _ => continue,
        };

        if !is_in_field(&arg, var, &available) {
            return Err("generator argument not in base field".to_string());
        }

        let arg_deriv = simplify_fully(differentiate(var, &arg));
        if arg_deriv.is_zero() {
            return Err("generator derivative is zero".to_string());
        }
        if !is_in_field(&arg_deriv, var, &available) {
            return Err("generator derivative not in base field".to_string());
        }

        tower_gens.push(Generator {
            kind,
            expr: gen_expr.clone(),
            arg,
            arg_deriv,
        });
        available.push(gen_expr);
    }

    Ok(Tower {
        generators: tower_gens,
    })
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
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => {
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

fn is_in_field(expr: &Expr, var: &str, gens: &[Expr]) -> bool {
    if gens.iter().any(|g| g == expr) {
        return true;
    }
    if !contains_var(expr, var) {
        return true;
    }
    match expr {
        Expr::Constant(_) | Expr::Variable(_) => true,
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b) => is_in_field(a, var, gens) && is_in_field(b, var, gens),
        Expr::Pow(base, exp) => {
            if contains_var(exp, var) {
                return false;
            }
            is_in_field(base, var, gens)
        }
        Expr::Neg(inner) => is_in_field(inner, var, gens),
        Expr::Exp(_) | Expr::Log(_) => false,
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
        | Expr::Abs(_) => false,
    }
}
