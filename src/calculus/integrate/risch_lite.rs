use std::collections::{HashMap, HashSet};

use num_traits::One;

use crate::calculus::differentiate;
use crate::expr::{Expr, Rational};
use crate::simplify::{simplify, simplify_fully};

use super::{
    apply_constant_factor, constant_ratio, contains_var, detect_non_elementary, flatten_product,
    log_abs, rebuild_product, split_constant_factors, to_rational_candidate,
};

#[derive(Debug, Clone)]
pub enum RischLiteOutcome {
    Integrated { result: Expr, note: String },
    NonElementary { kind: super::NonElementaryKind, note: String },
    Indeterminate { note: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum GeneratorKind {
    Exp,
    Log,
}

impl GeneratorKind {
    fn label(&self) -> &'static str {
        match self {
            GeneratorKind::Exp => "exp",
            GeneratorKind::Log => "log",
        }
    }
}

#[derive(Debug, Clone)]
struct Generator {
    kind: GeneratorKind,
    expr: Expr,
    arg: Expr,
    arg_deriv: Expr,
}

#[derive(Debug, Clone)]
struct Tower {
    generators: Vec<Generator>,
}

pub fn analyze(expr: &Expr, var: &str) -> RischLiteOutcome {
    let tower = match build_tower(expr, var) {
        Ok(tower) => tower,
        Err(note) => {
            if let Some(kind) = detect_non_elementary(expr, var) {
                return RischLiteOutcome::NonElementary {
                    kind,
                    note: format!("determinate non-elementary (tower: {note})"),
                };
            }
            return RischLiteOutcome::Indeterminate {
                note: format!("tower: {note}"),
            };
        }
    };

    if let Some((coeff, arg)) = log_derivative(expr, var) {
        let result = simplify(Expr::Mul(coeff.boxed(), log_abs(arg).boxed()));
        return RischLiteOutcome::Integrated {
            result,
            note: "logarithmic derivative (determinate)".to_string(),
        };
    }

    if let Some((result, note)) = integrate_in_tower(expr, var, &tower) {
        return RischLiteOutcome::Integrated {
            result,
            note: format!("{note} (determinate)"),
        };
    }

    if let Some(kind) = detect_non_elementary(expr, var) {
        return RischLiteOutcome::NonElementary {
            kind,
            note: "determinate non-elementary".to_string(),
        };
    }

    RischLiteOutcome::Indeterminate {
        note: "indeterminate".to_string(),
    }
}

fn build_tower(expr: &Expr, var: &str) -> Result<Tower, String> {
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

fn log_derivative(expr: &Expr, var: &str) -> Option<(Expr, Expr)> {
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

fn integrate_in_tower(expr: &Expr, var: &str, tower: &Tower) -> Option<(Expr, String)> {
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
                cancel_common_factors(replaced, denom)
            }
            GeneratorKind::Log => {
                let scale = Expr::Div(
                    generator.arg_deriv.clone().boxed(),
                    generator.arg.clone().boxed(),
                );
                cancel_common_factors(replaced, scale)
            }
        };

        let integrand_t = normalize_rational_candidate(integrand_t);
        let integrand_t = simplify_fully(integrand_t);
        if contains_var(&integrand_t, var) {
            continue;
        }

        let result_t = super::polynomial::integrate(&integrand_t, &t_name)
            .or_else(|| super::rational::integrate(&integrand_t, &t_name));
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

fn cancel_common_factors(numer: Expr, denom: Expr) -> Expr {
    let (c_num, mut f_num) = flatten_product(&numer);
    let (c_den, mut f_den) = flatten_product(&denom);
    let mut i = 0;
    while i < f_den.len() {
        if let Some(pos) = f_num.iter().position(|f| f == &f_den[i]) {
            f_num.remove(pos);
            f_den.remove(i);
        } else {
            i += 1;
        }
    }
    let num_expr = rebuild_product(c_num, f_num);
    let den_expr = rebuild_product(c_den, f_den);
    Expr::Div(num_expr.boxed(), den_expr.boxed())
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
