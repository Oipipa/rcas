use std::collections::{HashMap, HashSet};

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive};

use crate::calculus::differentiate;
use crate::core::error::{CasError, Result};
use crate::core::expr::{Expr, Rational, one};
use crate::simplify::simplify_fully;

use super::algebraic::{algebraic_derivative, algebraic_minimal_poly};
use super::utils::{expr_in_field, extract_rational_exp};
use super::ExprPoly;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExtensionKind {
    Exp,
    Log,
    Algebraic,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlgebraicExtension {
    pub base: Expr,
    pub base_symbol: Expr,
    pub degree: usize,
    pub minimal_poly: ExprPoly,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Extension {
    pub kind: ExtensionKind,
    pub symbol: String,
    pub generator: Expr,
    pub derivative: Expr,
    pub algebraic: Option<AlgebraicExtension>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tower {
    base_var: String,
    extensions: Vec<Extension>,
}

impl Tower {
    pub fn new(base_var: impl Into<String>) -> Self {
        Tower {
            base_var: base_var.into(),
            extensions: Vec::new(),
        }
    }

    pub fn base_var(&self) -> &str {
        &self.base_var
    }

    pub fn extensions(&self) -> &[Extension] {
        &self.extensions
    }

    pub fn push_exp(&mut self, arg: Expr) -> Result<&Extension> {
        self.push_extension(ExtensionKind::Exp, arg)
    }

    pub fn push_log(&mut self, arg: Expr) -> Result<&Extension> {
        self.push_extension(ExtensionKind::Log, arg)
    }

    pub fn push_algebraic_root(&mut self, base: Expr, degree: usize) -> Result<&Extension> {
        if degree < 2 {
            return Err(CasError::Unsupported(
                "algebraic degree must be >= 2".to_string(),
            ));
        }
        let base = simplify_fully(base);
        let generator = Expr::Pow(
            base.clone().boxed(),
            Expr::Constant(
                Rational::from_integer(1.into()) / Rational::from_integer(BigInt::from(degree)),
            )
            .boxed(),
        );
        self.push_algebraic(generator, base, degree)
    }

    pub fn replace_generators(&self, expr: &Expr) -> Expr {
        let replaced = replace_generators_inner(expr, self);
        simplify_fully(replaced)
    }

    pub fn expand_symbols(&self, expr: &Expr) -> Expr {
        let map = self.symbol_map();
        let expanded = replace_symbols_inner(expr, &map);
        simplify_fully(expanded)
    }

    pub fn top_symbol(&self) -> &str {
        self.extensions
            .last()
            .map(|ext| ext.symbol.as_str())
            .unwrap_or(&self.base_var)
    }

    pub fn top_derivative_expr(&self) -> Expr {
        self.extensions
            .last()
            .map(|ext| ext.derivative.clone())
            .unwrap_or_else(one)
    }

    pub(super) fn top_algebraic(&self) -> Option<&AlgebraicExtension> {
        self.extensions.last().and_then(|ext| ext.algebraic.as_ref())
    }

    pub fn expr_in_field(&self, expr: &Expr) -> bool {
        let symbols = self.symbol_set();
        expr_in_field(expr, &self.base_var, &symbols)
    }

    pub(super) fn symbol_derivative(&self, name: &str) -> Option<Expr> {
        self.extensions
            .iter()
            .find(|ext| ext.symbol == name)
            .map(|ext| ext.derivative.clone())
    }

    fn push_extension(&mut self, kind: ExtensionKind, arg: Expr) -> Result<&Extension> {
        let arg = simplify_fully(arg);
        let generator = match kind {
            ExtensionKind::Exp => Expr::Exp(arg.clone().boxed()),
            ExtensionKind::Log => Expr::Log(arg.clone().boxed()),
            ExtensionKind::Algebraic => {
                return Err(CasError::Unsupported(
                    "use push_algebraic_root for algebraic extensions".to_string(),
                ))
            }
        };
        let generator = simplify_fully(generator);

        if self.extensions.iter().any(|ext| ext.generator == generator) {
            return Err(CasError::Unsupported("duplicate generator".to_string()));
        }

        let arg_symbol = self.replace_generators(&arg);
        let symbols = self.symbol_set();
        if !expr_in_field(&arg_symbol, &self.base_var, &symbols) {
            return Err(CasError::Unsupported(
                "extension argument not in base field".to_string(),
            ));
        }

        let arg_derivative = simplify_fully(differentiate(&self.base_var, &arg));
        if arg_derivative.is_zero() {
            return Err(CasError::Unsupported(
                "extension derivative is zero".to_string(),
            ));
        }
        let arg_derivative_symbol = self.replace_generators(&arg_derivative);
        if !expr_in_field(&arg_derivative_symbol, &self.base_var, &symbols) {
            return Err(CasError::Unsupported(
                "extension derivative not in base field".to_string(),
            ));
        }

        let symbol = self.next_symbol();
        let symbol_expr = Expr::Variable(symbol.clone());
        let derivative = match kind {
            ExtensionKind::Exp => simplify_fully(Expr::Mul(
                arg_derivative_symbol.boxed(),
                symbol_expr.boxed(),
            )),
            ExtensionKind::Log => simplify_fully(Expr::Div(
                arg_derivative_symbol.boxed(),
                arg_symbol.boxed(),
            )),
            ExtensionKind::Algebraic => unreachable!("algebraic handled separately"),
        };

        self.extensions.push(Extension {
            kind,
            symbol,
            generator,
            derivative,
            algebraic: None,
        });
        Ok(self.extensions.last().expect("extension added"))
    }

    fn push_algebraic(&mut self, generator: Expr, base: Expr, degree: usize) -> Result<&Extension> {
        let generator = simplify_fully(generator);
        if self.extensions.iter().any(|ext| ext.generator == generator) {
            return Err(CasError::Unsupported("duplicate generator".to_string()));
        }

        let base_symbol = self.replace_generators(&base);
        let symbols = self.symbol_set();
        if !expr_in_field(&base_symbol, &self.base_var, &symbols) {
            return Err(CasError::Unsupported(
                "algebraic base not in base field".to_string(),
            ));
        }

        let base_derivative = simplify_fully(differentiate(&self.base_var, &base));
        if base_derivative.is_zero() {
            return Err(CasError::Unsupported(
                "algebraic base derivative is zero".to_string(),
            ));
        }

        let symbol = self.next_symbol();
        let minimal_poly = algebraic_minimal_poly(&base_symbol, degree);
        let derivative = algebraic_derivative(&minimal_poly, self, &symbol, &symbols)?;
        if derivative.is_zero() {
            return Err(CasError::Unsupported(
                "algebraic generator derivative is zero".to_string(),
            ));
        }

        self.extensions.push(Extension {
            kind: ExtensionKind::Algebraic,
            symbol,
            generator,
            derivative,
            algebraic: Some(AlgebraicExtension {
                base,
                base_symbol,
                degree,
                minimal_poly,
            }),
        });
        Ok(self.extensions.last().expect("extension added"))
    }

    fn next_symbol(&self) -> String {
        let mut used = self.symbol_set();
        used.insert(self.base_var.clone());
        for ext in &self.extensions {
            collect_vars(&ext.generator, &mut used);
        }
        let mut idx = self.extensions.len();
        loop {
            let candidate = format!("__t{idx}");
            if !used.contains(&candidate) {
                return candidate;
            }
            idx += 1;
        }
    }

    pub(super) fn symbol_set(&self) -> HashSet<String> {
        self.extensions.iter().map(|ext| ext.symbol.clone()).collect()
    }

    fn symbol_map(&self) -> HashMap<String, Expr> {
        self.extensions
            .iter()
            .map(|ext| (ext.symbol.clone(), ext.generator.clone()))
            .collect()
    }

    fn generator_symbol(&self, expr: &Expr) -> Option<&str> {
        self.extensions
            .iter()
            .find(|ext| ext.generator == *expr)
            .map(|ext| ext.symbol.as_str())
    }
}

fn rewrite_algebraic_power(base: &Expr, exp: &Expr, tower: &Tower) -> Option<Expr> {
    let exp = extract_rational_exp(exp)?;
    if exp.is_integer() {
        return None;
    }
    for ext in &tower.extensions {
        let algebraic = ext.algebraic.as_ref()?;
        if &algebraic.base_symbol != base {
            continue;
        }
        let degree = BigInt::from(algebraic.degree as i64);
        if exp.denom() != &degree {
            continue;
        }
        let (mut q, mut r) = exp.numer().div_rem(&degree);
        if r.is_negative() {
            q -= BigInt::one();
            r += degree.clone();
        }
        let q_i64 = q.to_i64()?;
        let r_i64 = r.to_i64()?;
        let base_factor = if q_i64 == 0 {
            None
        } else {
            Some(Expr::Pow(base.clone().boxed(), Expr::integer(q_i64).boxed()))
        };
        let symbol_factor = Expr::Pow(
            Expr::Variable(ext.symbol.clone()).boxed(),
            Expr::integer(r_i64).boxed(),
        );
        let combined = if let Some(base_factor) = base_factor {
            Expr::Mul(base_factor.boxed(), symbol_factor.boxed())
        } else {
            symbol_factor
        };
        return Some(simplify_fully(combined));
    }
    None
}

fn collect_vars(expr: &Expr, out: &mut HashSet<String>) {
    match expr {
        Expr::Variable(name) => {
            out.insert(name.clone());
        }
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => {
            collect_vars(a, out);
            collect_vars(b, out);
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
        | Expr::Abs(inner)
        | Expr::Exp(inner)
        | Expr::Log(inner) => collect_vars(inner, out),
        Expr::Constant(_) => {}
    }
}

fn replace_generators_inner(expr: &Expr, tower: &Tower) -> Expr {
    if let Some(symbol) = tower.generator_symbol(expr) {
        return Expr::Variable(symbol.to_string());
    }
    match expr {
        Expr::Variable(_) | Expr::Constant(_) => expr.clone(),
        Expr::Add(a, b) => Expr::Add(
            replace_generators_inner(a, tower).boxed(),
            replace_generators_inner(b, tower).boxed(),
        ),
        Expr::Sub(a, b) => Expr::Sub(
            replace_generators_inner(a, tower).boxed(),
            replace_generators_inner(b, tower).boxed(),
        ),
        Expr::Mul(a, b) => Expr::Mul(
            replace_generators_inner(a, tower).boxed(),
            replace_generators_inner(b, tower).boxed(),
        ),
        Expr::Div(a, b) => Expr::Div(
            replace_generators_inner(a, tower).boxed(),
            replace_generators_inner(b, tower).boxed(),
        ),
        Expr::Pow(a, b) => {
            let base = replace_generators_inner(a, tower);
            let exp = replace_generators_inner(b, tower);
            if let Some(rewritten) = rewrite_algebraic_power(&base, &exp, tower) {
                return rewritten;
            }
            Expr::Pow(base.boxed(), exp.boxed())
        }
        Expr::Neg(inner) => Expr::Neg(replace_generators_inner(inner, tower).boxed()),
        Expr::Sin(inner) => Expr::Sin(replace_generators_inner(inner, tower).boxed()),
        Expr::Cos(inner) => Expr::Cos(replace_generators_inner(inner, tower).boxed()),
        Expr::Tan(inner) => Expr::Tan(replace_generators_inner(inner, tower).boxed()),
        Expr::Sec(inner) => Expr::Sec(replace_generators_inner(inner, tower).boxed()),
        Expr::Csc(inner) => Expr::Csc(replace_generators_inner(inner, tower).boxed()),
        Expr::Cot(inner) => Expr::Cot(replace_generators_inner(inner, tower).boxed()),
        Expr::Atan(inner) => Expr::Atan(replace_generators_inner(inner, tower).boxed()),
        Expr::Asin(inner) => Expr::Asin(replace_generators_inner(inner, tower).boxed()),
        Expr::Acos(inner) => Expr::Acos(replace_generators_inner(inner, tower).boxed()),
        Expr::Asec(inner) => Expr::Asec(replace_generators_inner(inner, tower).boxed()),
        Expr::Acsc(inner) => Expr::Acsc(replace_generators_inner(inner, tower).boxed()),
        Expr::Acot(inner) => Expr::Acot(replace_generators_inner(inner, tower).boxed()),
        Expr::Sinh(inner) => Expr::Sinh(replace_generators_inner(inner, tower).boxed()),
        Expr::Cosh(inner) => Expr::Cosh(replace_generators_inner(inner, tower).boxed()),
        Expr::Tanh(inner) => Expr::Tanh(replace_generators_inner(inner, tower).boxed()),
        Expr::Asinh(inner) => Expr::Asinh(replace_generators_inner(inner, tower).boxed()),
        Expr::Acosh(inner) => Expr::Acosh(replace_generators_inner(inner, tower).boxed()),
        Expr::Atanh(inner) => Expr::Atanh(replace_generators_inner(inner, tower).boxed()),
        Expr::Exp(inner) => Expr::Exp(replace_generators_inner(inner, tower).boxed()),
        Expr::Log(inner) => Expr::Log(replace_generators_inner(inner, tower).boxed()),
        Expr::Abs(inner) => Expr::Abs(replace_generators_inner(inner, tower).boxed()),
    }
}

fn replace_symbols_inner(expr: &Expr, map: &HashMap<String, Expr>) -> Expr {
    match expr {
        Expr::Variable(name) => map.get(name).cloned().unwrap_or_else(|| expr.clone()),
        Expr::Constant(_) => expr.clone(),
        Expr::Add(a, b) => Expr::Add(
            replace_symbols_inner(a, map).boxed(),
            replace_symbols_inner(b, map).boxed(),
        ),
        Expr::Sub(a, b) => Expr::Sub(
            replace_symbols_inner(a, map).boxed(),
            replace_symbols_inner(b, map).boxed(),
        ),
        Expr::Mul(a, b) => Expr::Mul(
            replace_symbols_inner(a, map).boxed(),
            replace_symbols_inner(b, map).boxed(),
        ),
        Expr::Div(a, b) => Expr::Div(
            replace_symbols_inner(a, map).boxed(),
            replace_symbols_inner(b, map).boxed(),
        ),
        Expr::Pow(a, b) => Expr::Pow(
            replace_symbols_inner(a, map).boxed(),
            replace_symbols_inner(b, map).boxed(),
        ),
        Expr::Neg(inner) => Expr::Neg(replace_symbols_inner(inner, map).boxed()),
        Expr::Sin(inner) => Expr::Sin(replace_symbols_inner(inner, map).boxed()),
        Expr::Cos(inner) => Expr::Cos(replace_symbols_inner(inner, map).boxed()),
        Expr::Tan(inner) => Expr::Tan(replace_symbols_inner(inner, map).boxed()),
        Expr::Sec(inner) => Expr::Sec(replace_symbols_inner(inner, map).boxed()),
        Expr::Csc(inner) => Expr::Csc(replace_symbols_inner(inner, map).boxed()),
        Expr::Cot(inner) => Expr::Cot(replace_symbols_inner(inner, map).boxed()),
        Expr::Atan(inner) => Expr::Atan(replace_symbols_inner(inner, map).boxed()),
        Expr::Asin(inner) => Expr::Asin(replace_symbols_inner(inner, map).boxed()),
        Expr::Acos(inner) => Expr::Acos(replace_symbols_inner(inner, map).boxed()),
        Expr::Asec(inner) => Expr::Asec(replace_symbols_inner(inner, map).boxed()),
        Expr::Acsc(inner) => Expr::Acsc(replace_symbols_inner(inner, map).boxed()),
        Expr::Acot(inner) => Expr::Acot(replace_symbols_inner(inner, map).boxed()),
        Expr::Sinh(inner) => Expr::Sinh(replace_symbols_inner(inner, map).boxed()),
        Expr::Cosh(inner) => Expr::Cosh(replace_symbols_inner(inner, map).boxed()),
        Expr::Tanh(inner) => Expr::Tanh(replace_symbols_inner(inner, map).boxed()),
        Expr::Asinh(inner) => Expr::Asinh(replace_symbols_inner(inner, map).boxed()),
        Expr::Acosh(inner) => Expr::Acosh(replace_symbols_inner(inner, map).boxed()),
        Expr::Atanh(inner) => Expr::Atanh(replace_symbols_inner(inner, map).boxed()),
        Expr::Exp(inner) => Expr::Exp(replace_symbols_inner(inner, map).boxed()),
        Expr::Log(inner) => Expr::Log(replace_symbols_inner(inner, map).boxed()),
        Expr::Abs(inner) => Expr::Abs(replace_symbols_inner(inner, map).boxed()),
    }
}
