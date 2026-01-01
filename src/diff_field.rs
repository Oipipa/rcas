use std::collections::{BTreeMap, HashMap, HashSet};

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive};

use crate::calculus::differentiate;
use crate::error::{CasError, Result};
use crate::expr::{Expr, Rational, one, zero};
use crate::polynomial::Polynomial;
use crate::simplify::simplify_fully;

type ExprPoly = Polynomial<Expr>;

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

    fn top_algebraic(&self) -> Option<&AlgebraicExtension> {
        self.extensions.last().and_then(|ext| ext.algebraic.as_ref())
    }

    pub fn expr_in_field(&self, expr: &Expr) -> bool {
        let symbols = self.symbol_set();
        expr_in_field(expr, &self.base_var, &symbols)
    }

    fn symbol_derivative(&self, name: &str) -> Option<Expr> {
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

    fn symbol_set(&self) -> HashSet<String> {
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldElement {
    numer: ExprPoly,
    denom: ExprPoly,
    tower: Tower,
}

impl FieldElement {
    pub fn try_from_expr(expr: &Expr, tower: &Tower) -> Result<Self> {
        let simplified = simplify_fully(expr.clone());
        let replaced = tower.replace_generators(&simplified);
        if !tower.expr_in_field(&replaced) {
            return Err(CasError::Unsupported(
                "expression not in differential field".to_string(),
            ));
        }
        let top = tower.top_symbol();
        let (numer, denom) = expr_to_rational_polys(&replaced, top)?;
        FieldElement::from_polys(numer, denom, tower.clone())
    }

    pub fn to_expr(&self) -> Expr {
        let var = self.tower.top_symbol();
        let numer = poly_to_expr(&self.numer, var);
        let denom = poly_to_expr(&self.denom, var);
        if denom.is_one() {
            simplify_fully(numer)
        } else {
            simplify_fully(Expr::Div(numer.boxed(), denom.boxed()))
        }
    }

    pub fn to_original_expr(&self) -> Expr {
        let expr = self.to_expr();
        self.tower.expand_symbols(&expr)
    }

    pub fn is_zero(&self) -> bool {
        self.numer.is_zero()
    }

    pub fn is_constant(&self) -> Result<bool> {
        Ok(self.derivative()?.is_zero())
    }

    pub fn add(&self, other: &Self) -> Result<Self> {
        self.ensure_same_tower(other)?;
        let numer = self.numer.clone() * other.denom.clone()
            + other.numer.clone() * self.denom.clone();
        let denom = self.denom.clone() * other.denom.clone();
        FieldElement::from_polys(numer, denom, self.tower.clone())
    }

    pub fn sub(&self, other: &Self) -> Result<Self> {
        self.ensure_same_tower(other)?;
        let numer = self.numer.clone() * other.denom.clone()
            - other.numer.clone() * self.denom.clone();
        let denom = self.denom.clone() * other.denom.clone();
        FieldElement::from_polys(numer, denom, self.tower.clone())
    }

    pub fn mul(&self, other: &Self) -> Result<Self> {
        self.ensure_same_tower(other)?;
        let numer = self.numer.clone() * other.numer.clone();
        let denom = self.denom.clone() * other.denom.clone();
        FieldElement::from_polys(numer, denom, self.tower.clone())
    }

    pub fn div(&self, other: &Self) -> Result<Self> {
        self.ensure_same_tower(other)?;
        if other.numer.is_zero() {
            return Err(CasError::Unsupported("division by zero".to_string()));
        }
        let numer = self.numer.clone() * other.denom.clone();
        let denom = self.denom.clone() * other.numer.clone();
        FieldElement::from_polys(numer, denom, self.tower.clone())
    }

    pub fn neg(&self) -> Result<Self> {
        FieldElement::from_polys(-self.numer.clone(), self.denom.clone(), self.tower.clone())
    }

    pub fn pow_i64(&self, exp: i64) -> Result<Self> {
        if exp == 0 {
            return FieldElement::from_polys(ExprPoly::one(), ExprPoly::one(), self.tower.clone());
        }
        let power = abs_i64_to_usize(exp)?;
        let mut numer = self.numer.pow(power);
        let mut denom = self.denom.pow(power);
        if exp < 0 {
            std::mem::swap(&mut numer, &mut denom);
        }
        FieldElement::from_polys(numer, denom, self.tower.clone())
    }

    pub fn derivative(&self) -> Result<Self> {
        let numer_deriv = poly_derivative(&self.numer, &self.tower)?;
        let denom_deriv = poly_derivative(&self.denom, &self.tower)?;
        let numer = numer_deriv * self.denom.clone() - self.numer.clone() * denom_deriv;
        let denom = self.denom.clone() * self.denom.clone();
        FieldElement::from_polys(numer, denom, self.tower.clone())
    }

    fn from_polys(numer: ExprPoly, denom: ExprPoly, tower: Tower) -> Result<Self> {
        if denom.is_zero() {
            return Err(CasError::Unsupported("zero denominator".to_string()));
        }
        let mut numer = simplify_poly_coeffs(numer);
        let mut denom = simplify_poly_coeffs(denom);
        if denom.is_zero() {
            return Err(CasError::Unsupported("zero denominator".to_string()));
        }
        if numer.is_zero() {
            denom = ExprPoly::one();
            return Ok(FieldElement { numer, denom, tower });
        }

        if let Some(algebraic) = tower.top_algebraic() {
            let reduced = reduce_algebraic_rational(&numer, &denom, &algebraic.minimal_poly)?;
            numer = reduced.0;
            denom = reduced.1;
            if numer.is_zero() {
                denom = ExprPoly::one();
                return Ok(FieldElement { numer, denom, tower });
            }
        }

        let lc = denom.leading_coeff();
        if !lc.is_one() {
            let scale = Expr::Div(one().boxed(), lc.boxed());
            numer = numer.scale(&scale);
            denom = denom.scale(&scale);
            numer = simplify_poly_coeffs(numer);
            denom = simplify_poly_coeffs(denom);
        }

        Ok(FieldElement { numer, denom, tower })
    }

    fn ensure_same_tower(&self, other: &Self) -> Result<()> {
        if self.tower != other.tower {
            return Err(CasError::Unsupported(
                "mismatched differential towers".to_string(),
            ));
        }
        Ok(())
    }
}

fn poly_derivative(poly: &ExprPoly, tower: &Tower) -> Result<ExprPoly> {
    let top = tower.top_symbol();
    let t_deriv_expr = tower.top_derivative_expr();
    let t_deriv_poly = ExprPoly::from_expr(&t_deriv_expr, top).ok_or_else(|| {
        CasError::Unsupported("top symbol derivative not polynomial".to_string())
    })?;

    let symbols = tower.symbol_set();
    let mut result = ExprPoly::zero();
    for (exp, coeff) in poly.coeff_entries() {
        let coeff_deriv = derive_expr_inner(&coeff, tower, &symbols)?;
        if !coeff_deriv.is_zero() {
            result = result + poly_from_coeff(exp, coeff_deriv);
        }
        if exp == 0 {
            continue;
        }
        let factor = Expr::Constant(Rational::from_integer(BigInt::from(exp as i64)));
        let scaled = simplify_fully(Expr::Mul(coeff.clone().boxed(), factor.boxed()));
        if scaled.is_zero() {
            continue;
        }
        let mut term = poly_from_power(exp - 1);
        term = term * t_deriv_poly.clone();
        term = term.scale(&scaled);
        result = result + term;
    }
    Ok(simplify_poly_coeffs(result))
}

fn derive_expr_inner(expr: &Expr, tower: &Tower, symbols: &HashSet<String>) -> Result<Expr> {
    if !expr_depends_on(expr, tower.base_var(), symbols) {
        return Ok(zero());
    }
    let derived = match expr {
        Expr::Variable(name) if name == tower.base_var() => one(),
        Expr::Variable(name) => tower.symbol_derivative(name).unwrap_or_else(zero),
        Expr::Constant(_) => zero(),
        Expr::Add(a, b) => Expr::Add(
            derive_expr_inner(a, tower, symbols)?.boxed(),
            derive_expr_inner(b, tower, symbols)?.boxed(),
        ),
        Expr::Sub(a, b) => Expr::Sub(
            derive_expr_inner(a, tower, symbols)?.boxed(),
            derive_expr_inner(b, tower, symbols)?.boxed(),
        ),
        Expr::Mul(a, b) => {
            let da = derive_expr_inner(a, tower, symbols)?;
            let db = derive_expr_inner(b, tower, symbols)?;
            Expr::Add(
                Expr::Mul(da.boxed(), b.clone().boxed()).boxed(),
                Expr::Mul(a.clone().boxed(), db.boxed()).boxed(),
            )
        }
        Expr::Div(a, b) => {
            let da = derive_expr_inner(a, tower, symbols)?;
            let db = derive_expr_inner(b, tower, symbols)?;
            Expr::Div(
                Expr::Sub(
                    Expr::Mul(da.boxed(), b.clone().boxed()).boxed(),
                    Expr::Mul(a.clone().boxed(), db.boxed()).boxed(),
                )
                .boxed(),
                Expr::Pow(b.clone().boxed(), Expr::integer(2).boxed()).boxed(),
            )
        }
        Expr::Neg(inner) => Expr::Neg(derive_expr_inner(inner, tower, symbols)?.boxed()),
        Expr::Pow(base, exp) => {
            let power = extract_integer(exp).ok_or_else(|| {
                CasError::Unsupported("non-integer exponent in derivative".to_string())
            })?;
            if power == 0 {
                zero()
            } else {
                let coeff = Expr::Constant(Rational::from_integer(BigInt::from(power)));
                Expr::Mul(
                    coeff.boxed(),
                    Expr::Mul(
                        Expr::Pow(
                            base.clone().boxed(),
                            Expr::Constant(Rational::from_integer(BigInt::from(power - 1))).boxed(),
                        )
                        .boxed(),
                        derive_expr_inner(base, tower, symbols)?.boxed(),
                    )
                    .boxed(),
                )
            }
        }
        _ => {
            if expr_depends_on(expr, tower.base_var(), symbols) {
                return Err(CasError::Unsupported(
                    "unsupported expression in derivative".to_string(),
                ));
            }
            zero()
        }
    };
    Ok(simplify_fully(derived))
}

fn expr_to_rational_polys(expr: &Expr, var: &str) -> Result<(ExprPoly, ExprPoly)> {
    if !expr_contains_var(expr, var) {
        return Ok((ExprPoly::from_constant(expr.clone()), ExprPoly::one()));
    }
    match expr {
        Expr::Variable(name) if name == var => {
            let mut coeffs = BTreeMap::new();
            coeffs.insert(1, one());
            Ok((ExprPoly { coeffs }, ExprPoly::one()))
        }
        Expr::Constant(_) => Ok((ExprPoly::from_constant(expr.clone()), ExprPoly::one())),
        Expr::Add(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            let numer = an * bd.clone() + bn * ad.clone();
            let denom = ad * bd;
            Ok((numer, denom))
        }
        Expr::Sub(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            let numer = an * bd.clone() - bn * ad.clone();
            let denom = ad * bd;
            Ok((numer, denom))
        }
        Expr::Mul(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            Ok((an * bn, ad * bd))
        }
        Expr::Div(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            Ok((an * bd, ad * bn))
        }
        Expr::Neg(inner) => {
            let (n, d) = expr_to_rational_polys(inner, var)?;
            Ok((-n, d))
        }
        Expr::Pow(base, exp) => {
            let power = extract_integer(exp).ok_or_else(|| {
                CasError::Unsupported("non-integer exponent in rational expression".to_string())
            })?;
            let (bn, bd) = expr_to_rational_polys(base, var)?;
            if power == 0 {
                return Ok((ExprPoly::one(), ExprPoly::one()));
            }
            let abs_power = abs_i64_to_usize(power)?;
            let mut numer = bn.pow(abs_power);
            let mut denom = bd.pow(abs_power);
            if power < 0 {
                std::mem::swap(&mut numer, &mut denom);
            }
            Ok((numer, denom))
        }
        _ => Err(CasError::Unsupported(
            "non-rational expression in conversion".to_string(),
        )),
    }
}

fn simplify_poly_coeffs(poly: ExprPoly) -> ExprPoly {
    let mut coeffs = BTreeMap::new();
    for (exp, coeff) in poly.coeff_entries() {
        let simplified = simplify_fully(coeff);
        if !simplified.is_zero() {
            coeffs.insert(exp, simplified);
        }
    }
    ExprPoly { coeffs }
}

fn poly_from_power(exp: usize) -> ExprPoly {
    let mut coeffs = BTreeMap::new();
    coeffs.insert(exp, one());
    ExprPoly { coeffs }
}

fn poly_from_coeff(exp: usize, coeff: Expr) -> ExprPoly {
    if coeff.is_zero() {
        return ExprPoly::zero();
    }
    let mut coeffs = BTreeMap::new();
    coeffs.insert(exp, coeff);
    ExprPoly { coeffs }
}

fn poly_to_expr(poly: &ExprPoly, var: &str) -> Expr {
    if poly.is_zero() {
        return zero();
    }
    let mut terms = Vec::new();
    for (exp, coeff) in poly.coeff_entries() {
        let term = if exp == 0 {
            coeff
        } else {
            let pow = if exp == 1 {
                Expr::Variable(var.to_string())
            } else {
                Expr::Pow(
                    Expr::Variable(var.to_string()).boxed(),
                    Expr::Constant(Rational::from_integer(BigInt::from(exp as i64))).boxed(),
                )
            };
            if coeff.is_one() {
                pow
            } else if expr_is_negative_one(&coeff) {
                Expr::Neg(pow.boxed())
            } else {
                Expr::Mul(coeff.boxed(), pow.boxed())
            }
        };
        terms.push(term);
    }
    terms.sort();
    terms
        .into_iter()
        .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
        .unwrap_or_else(zero)
}

fn expr_contains_var(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Variable(name) => name == var,
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => expr_contains_var(a, var) || expr_contains_var(b, var),
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
        | Expr::Log(inner) => expr_contains_var(inner, var),
        Expr::Constant(_) => false,
    }
}

fn expr_depends_on(expr: &Expr, base_var: &str, symbols: &HashSet<String>) -> bool {
    match expr {
        Expr::Variable(name) => name == base_var || symbols.contains(name),
        Expr::Constant(_) => false,
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => expr_depends_on(a, base_var, symbols) || expr_depends_on(b, base_var, symbols),
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
        | Expr::Log(inner) => expr_depends_on(inner, base_var, symbols),
    }
}

fn expr_in_field(expr: &Expr, base_var: &str, symbols: &HashSet<String>) -> bool {
    if !expr_depends_on(expr, base_var, symbols) {
        return true;
    }
    match expr {
        Expr::Variable(_) => true,
        Expr::Constant(_) => true,
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b) => expr_in_field(a, base_var, symbols) && expr_in_field(b, base_var, symbols),
        Expr::Neg(inner) => expr_in_field(inner, base_var, symbols),
        Expr::Pow(base, exp) => extract_integer(exp).is_some() && expr_in_field(base, base_var, symbols),
        _ => false,
    }
}

fn algebraic_minimal_poly(base_symbol: &Expr, degree: usize) -> ExprPoly {
    let mut coeffs = BTreeMap::new();
    coeffs.insert(degree, one());
    coeffs.insert(0, simplify_fully(Expr::Neg(base_symbol.clone().boxed())));
    simplify_poly_coeffs(ExprPoly { coeffs })
}

fn algebraic_derivative(
    minimal: &ExprPoly,
    tower: &Tower,
    symbol: &str,
    symbols: &HashSet<String>,
) -> Result<Expr> {
    let m_t = expr_poly_derivative_t(minimal);
    if expr_poly_is_zero(&m_t) {
        return Err(CasError::Unsupported(
            "algebraic minimal polynomial derivative is zero".to_string(),
        ));
    }
    let m_x = algebraic_coeff_derivative(minimal, tower, symbols)?;
    let inv_m_t = expr_poly_mod_inverse(&m_t, minimal).ok_or_else(|| {
        CasError::Unsupported("algebraic minimal polynomial not squarefree".to_string())
    })?;
    let deriv_poly = expr_poly_mod(
        &simplify_poly_coeffs(m_x * inv_m_t.scale(&Expr::Constant(
            -Rational::one(),
        ))),
        minimal,
    );
    Ok(poly_to_expr(&deriv_poly, symbol))
}

fn algebraic_coeff_derivative(
    poly: &ExprPoly,
    tower: &Tower,
    symbols: &HashSet<String>,
) -> Result<ExprPoly> {
    let mut result = ExprPoly::zero();
    for (exp, coeff) in poly.coeff_entries() {
        let coeff_deriv = derive_expr_inner(&coeff, tower, symbols)?;
        if !coeff_deriv.is_zero() {
            result = result + poly_from_coeff(exp, coeff_deriv);
        }
    }
    Ok(simplify_poly_coeffs(result))
}

fn reduce_algebraic_rational(
    numer: &ExprPoly,
    denom: &ExprPoly,
    minimal: &ExprPoly,
) -> Result<(ExprPoly, ExprPoly)> {
    let numer = simplify_poly_coeffs(numer.clone());
    let denom = simplify_poly_coeffs(denom.clone());
    let numer_mod = expr_poly_mod(&numer, minimal);
    let denom_mod = expr_poly_mod(&denom, minimal);
    if expr_poly_is_zero(&denom_mod) {
        return Err(CasError::Unsupported("division by zero".to_string()));
    }
    if expr_poly_is_one(&denom_mod) {
        return Ok((numer_mod, ExprPoly::one()));
    }
    let inv = expr_poly_mod_inverse(&denom_mod, minimal)
        .ok_or_else(|| CasError::Unsupported("non-invertible denominator".to_string()))?;
    let reduced = expr_poly_mod(&simplify_poly_coeffs(numer_mod * inv), minimal);
    Ok((reduced, ExprPoly::one()))
}

fn extract_integer(exp: &Expr) -> Option<i64> {
    match exp {
        Expr::Constant(c) if c.is_integer() => c.to_integer().to_i64(),
        Expr::Neg(inner) => extract_integer(inner).map(|value| -value),
        _ => None,
    }
}

fn abs_i64_to_usize(value: i64) -> Result<usize> {
    value
        .checked_abs()
        .and_then(|abs| usize::try_from(abs).ok())
        .ok_or_else(|| CasError::Unsupported("exponent overflow".to_string()))
}

fn expr_is_negative_one(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(c) if *c == -Rational::one())
}

fn extract_rational_exp(expr: &Expr) -> Option<Rational> {
    match expr {
        Expr::Constant(c) => Some(c.clone()),
        Expr::Neg(inner) => extract_rational_exp(inner).map(|c| -c),
        _ => None,
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

fn expr_poly_is_zero(poly: &ExprPoly) -> bool {
    simplify_poly_coeffs(poly.clone()).is_zero()
}

fn expr_poly_is_one(poly: &ExprPoly) -> bool {
    let simplified = simplify_poly_coeffs(poly.clone());
    simplified.degree() == Some(0) && simplify_fully(simplified.coeff(0)).is_one()
}

fn expr_poly_div_rem(dividend: &ExprPoly, divisor: &ExprPoly) -> Option<(ExprPoly, ExprPoly)> {
    if expr_poly_is_zero(divisor) {
        return None;
    }
    let mut remainder = simplify_poly_coeffs(dividend.clone());
    let mut quotient = ExprPoly::zero();
    let divisor_degree = divisor.degree()?;
    let divisor_lc = simplify_fully(divisor.leading_coeff());
    if divisor_lc.is_zero() {
        return None;
    }
    if divisor_degree == 0 {
        let scale = Expr::Div(
            Expr::Constant(Rational::one()).boxed(),
            divisor_lc.boxed(),
        );
        let scaled = simplify_poly_coeffs(dividend.scale(&scale));
        return Some((scaled, ExprPoly::zero()));
    }

    while let Some(r_deg) = remainder.degree() {
        if r_deg < divisor_degree {
            break;
        }
        let power = r_deg - divisor_degree;
        let coeff = simplify_fully(Expr::Div(
            remainder.leading_coeff().boxed(),
            divisor_lc.clone().boxed(),
        ));
        let term = poly_from_coeff(power, coeff);
        quotient = simplify_poly_coeffs(quotient + term.clone());
        remainder = simplify_poly_coeffs(remainder - term * divisor.clone());
    }

    Some((simplify_poly_coeffs(quotient), simplify_poly_coeffs(remainder)))
}

fn expr_poly_mod(poly: &ExprPoly, modulus: &ExprPoly) -> ExprPoly {
    if expr_poly_is_zero(modulus) {
        return poly.clone();
    }
    let (_, remainder) = expr_poly_div_rem(poly, modulus).unwrap_or((ExprPoly::zero(), poly.clone()));
    remainder
}

fn expr_poly_extended_gcd(
    a: &ExprPoly,
    b: &ExprPoly,
) -> Option<(ExprPoly, ExprPoly, ExprPoly)> {
    let mut r0 = a.clone();
    let mut r1 = b.clone();
    let mut s0 = ExprPoly::one();
    let mut s1 = ExprPoly::zero();
    let mut t0 = ExprPoly::zero();
    let mut t1 = ExprPoly::one();

    while !expr_poly_is_zero(&r1) {
        let (q, r) = expr_poly_div_rem(&r0, &r1)?;
        r0 = r1;
        r1 = r;
        let s2 = simplify_poly_coeffs(s0.clone() - q.clone() * s1.clone());
        let t2 = simplify_poly_coeffs(t0.clone() - q * t1.clone());
        s0 = s1;
        s1 = s2;
        t0 = t1;
        t1 = t2;
    }

    if expr_poly_is_zero(&r0) {
        return None;
    }
    let lc = simplify_fully(r0.leading_coeff());
    if lc.is_zero() {
        return None;
    }
    let scale = Expr::Div(Expr::Constant(Rational::one()).boxed(), lc.boxed());
    Some((
        simplify_poly_coeffs(r0.scale(&scale)),
        simplify_poly_coeffs(s0.scale(&scale)),
        simplify_poly_coeffs(t0.scale(&scale)),
    ))
}

fn expr_poly_mod_inverse(value: &ExprPoly, modulus: &ExprPoly) -> Option<ExprPoly> {
    if expr_poly_is_zero(modulus) {
        return None;
    }
    let (gcd, _s, t) = expr_poly_extended_gcd(modulus, value)?;
    if expr_poly_is_one(&gcd) {
        return Some(expr_poly_mod(&t, modulus));
    }
    if gcd.degree() == Some(0) {
        let coeff = simplify_fully(gcd.coeff(0));
        if coeff.is_zero() {
            return None;
        }
        let scale = Expr::Div(Expr::Constant(Rational::one()).boxed(), coeff.boxed());
        return Some(expr_poly_mod(&simplify_poly_coeffs(t.scale(&scale)), modulus));
    }
    None
}

fn expr_poly_derivative_t(poly: &ExprPoly) -> ExprPoly {
    let mut coeffs = BTreeMap::new();
    for (exp, coeff) in poly.coeff_entries() {
        if exp == 0 {
            continue;
        }
        let factor = Rational::from_integer(BigInt::from(exp as i64));
        let scaled = simplify_fully(Expr::Mul(
            coeff.boxed(),
            Expr::Constant(factor).boxed(),
        ));
        if !scaled.is_zero() {
            coeffs.insert(exp - 1, scaled);
        }
    }
    ExprPoly { coeffs }
}
