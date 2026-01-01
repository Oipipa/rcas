use std::collections::btree_map::Entry;
use std::collections::BTreeMap;

use crate::expr::{Expr, Rational};
use crate::simplify::simplify;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

pub trait CoeffOps: Clone {
    fn zero() -> Self;
    fn one() -> Self;
    fn is_zero(&self) -> bool;
    fn is_one(&self) -> bool;
    fn add(&self, other: &Self) -> Self;
    fn sub(&self, other: &Self) -> Self;
    fn mul(&self, other: &Self) -> Self;
    fn neg(&self) -> Self;
}

impl CoeffOps for Rational {
    fn zero() -> Self {
        Zero::zero()
    }

    fn one() -> Self {
        One::one()
    }

    fn is_zero(&self) -> bool {
        Zero::is_zero(self)
    }

    fn is_one(&self) -> bool {
        One::is_one(self)
    }

    fn add(&self, other: &Self) -> Self {
        self.clone() + other.clone()
    }

    fn sub(&self, other: &Self) -> Self {
        self.clone() - other.clone()
    }

    fn mul(&self, other: &Self) -> Self {
        self.clone() * other.clone()
    }

    fn neg(&self) -> Self {
        -self.clone()
    }
}

impl CoeffOps for Expr {
    fn zero() -> Self {
        Expr::Constant(Zero::zero())
    }

    fn one() -> Self {
        Expr::Constant(One::one())
    }

    fn is_zero(&self) -> bool {
        self.is_zero()
    }

    fn is_one(&self) -> bool {
        self.is_one()
    }

    fn add(&self, other: &Self) -> Self {
        simplify(Expr::Add(self.clone().boxed(), other.clone().boxed()))
    }

    fn sub(&self, other: &Self) -> Self {
        simplify(Expr::Sub(self.clone().boxed(), other.clone().boxed()))
    }

    fn mul(&self, other: &Self) -> Self {
        simplify(Expr::Mul(self.clone().boxed(), other.clone().boxed()))
    }

    fn neg(&self) -> Self {
        simplify(Expr::Neg(self.clone().boxed()))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Polynomial<C> {
    pub(crate) coeffs: BTreeMap<usize, C>,
}

pub type Poly = Polynomial<Rational>;

impl<C: CoeffOps> Polynomial<C> {
    pub fn zero() -> Self {
        Polynomial {
            coeffs: BTreeMap::new(),
        }
    }

    pub fn one() -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(0, C::one());
        Polynomial { coeffs }
    }

    pub fn from_constant(c: C) -> Self {
        if c.is_zero() {
            return Polynomial::zero();
        }
        let mut coeffs = BTreeMap::new();
        coeffs.insert(0, c);
        Polynomial { coeffs }
    }

    pub fn degree(&self) -> Option<usize> {
        self.coeffs.keys().rev().next().cloned()
    }

    pub fn leading_coeff(&self) -> C {
        self.degree()
            .and_then(|d| self.coeffs.get(&d).cloned())
            .unwrap_or_else(C::zero)
    }

    pub fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    pub fn is_one(&self) -> bool {
        self.coeffs.len() == 1 && self.coeffs.get(&0).map(|c| c.is_one()).unwrap_or(false)
    }

    pub fn coeff(&self, power: usize) -> C {
        self.coeffs
            .get(&power)
            .cloned()
            .unwrap_or_else(C::zero)
    }

    pub fn coeff_entries(&self) -> impl Iterator<Item = (usize, C)> + '_ {
        self.coeffs.iter().map(|(e, c)| (*e, c.clone()))
    }

    pub fn pow(&self, exp: usize) -> Self {
        if exp == 0 {
            return Polynomial::one();
        }
        let mut result = Polynomial::one();
        let mut base = self.clone();
        let mut n = exp;
        while n > 0 {
            if n % 2 == 1 {
                result = result * base.clone();
            }
            base = base.clone() * base;
            n /= 2;
        }
        result
    }

    pub fn scale(&self, k: &C) -> Self {
        if k.is_zero() {
            return Polynomial::zero();
        }
        let mut coeffs = BTreeMap::new();
        for (exp, coeff) in &self.coeffs {
            let scaled = coeff.mul(k);
            if !scaled.is_zero() {
                coeffs.insert(*exp, scaled);
            }
        }
        Polynomial { coeffs }
    }

    pub fn add(&self, other: &Self) -> Self {
        self.clone() + other.clone()
    }

    pub fn sub(&self, other: &Self) -> Self {
        self.clone() - other.clone()
    }

    pub fn mul(&self, other: &Self) -> Self {
        self.clone() * other.clone()
    }
}

impl<C: CoeffOps> std::ops::Add for Polynomial<C> {
    type Output = Polynomial<C>;
    fn add(self, rhs: Polynomial<C>) -> Polynomial<C> {
        let mut coeffs = self.coeffs;
        for (exp, coeff) in rhs.coeffs {
            match coeffs.entry(exp) {
                Entry::Vacant(entry) => {
                    if !coeff.is_zero() {
                        entry.insert(coeff);
                    }
                }
                Entry::Occupied(mut entry) => {
                    let updated = entry.get().add(&coeff);
                    if updated.is_zero() {
                        entry.remove();
                    } else {
                        *entry.get_mut() = updated;
                    }
                }
            }
        }
        Polynomial { coeffs }
    }
}

impl<C: CoeffOps> std::ops::Add<&Polynomial<C>> for Polynomial<C> {
    type Output = Polynomial<C>;
    fn add(self, rhs: &Polynomial<C>) -> Polynomial<C> {
        self + rhs.clone()
    }
}

impl<C: CoeffOps> std::ops::Sub for Polynomial<C> {
    type Output = Polynomial<C>;
    fn sub(self, rhs: Polynomial<C>) -> Polynomial<C> {
        let mut coeffs = self.coeffs;
        for (exp, coeff) in rhs.coeffs {
            match coeffs.entry(exp) {
                Entry::Vacant(entry) => {
                    if !coeff.is_zero() {
                        entry.insert(coeff.neg());
                    }
                }
                Entry::Occupied(mut entry) => {
                    let updated = entry.get().sub(&coeff);
                    if updated.is_zero() {
                        entry.remove();
                    } else {
                        *entry.get_mut() = updated;
                    }
                }
            }
        }
        Polynomial { coeffs }
    }
}

impl<C: CoeffOps> std::ops::Sub<&Polynomial<C>> for Polynomial<C> {
    type Output = Polynomial<C>;
    fn sub(self, rhs: &Polynomial<C>) -> Polynomial<C> {
        self - rhs.clone()
    }
}

impl<C: CoeffOps> std::ops::Mul for Polynomial<C> {
    type Output = Polynomial<C>;
    fn mul(self, rhs: Polynomial<C>) -> Polynomial<C> {
        let rhs_coeffs = rhs.coeffs;
        let mut coeffs = BTreeMap::new();
        for (exp_a, coeff_a) in self.coeffs {
            for (exp_b, coeff_b) in rhs_coeffs.iter() {
                let exp = exp_a + exp_b;
                let product = coeff_a.mul(coeff_b);
                if product.is_zero() {
                    continue;
                }
                match coeffs.entry(exp) {
                    Entry::Vacant(entry) => {
                        entry.insert(product);
                    }
                    Entry::Occupied(mut entry) => {
                        let updated = entry.get().add(&product);
                        if updated.is_zero() {
                            entry.remove();
                        } else {
                            *entry.get_mut() = updated;
                        }
                    }
                }
            }
        }
        Polynomial { coeffs }
    }
}

impl<C: CoeffOps> std::ops::Mul<&Polynomial<C>> for Polynomial<C> {
    type Output = Polynomial<C>;
    fn mul(self, rhs: &Polynomial<C>) -> Polynomial<C> {
        self * rhs.clone()
    }
}

impl<C: CoeffOps> std::ops::Neg for Polynomial<C> {
    type Output = Polynomial<C>;
    fn neg(self) -> Polynomial<C> {
        let mut coeffs = BTreeMap::new();
        for (exp, coeff) in self.coeffs {
            let negated = coeff.neg();
            if !negated.is_zero() {
                coeffs.insert(exp, negated);
            }
        }
        Polynomial { coeffs }
    }
}

impl Polynomial<Rational> {
    pub fn from_expr(expr: &Expr, var: &str) -> Option<Self> {
        if !contains_var(expr, var) {
            return extract_rational(expr).map(Polynomial::from_constant);
        }
        match expr {
            Expr::Variable(v) if v == var => {
                let mut coeffs = BTreeMap::new();
                coeffs.insert(1, One::one());
                Some(Polynomial { coeffs })
            }
            Expr::Constant(_) => Some(Polynomial::zero()),
            Expr::Add(a, b) => Some(Self::from_expr(a, var)? + Self::from_expr(b, var)?),
            Expr::Sub(a, b) => Some(Self::from_expr(a, var)? - Self::from_expr(b, var)?),
            Expr::Mul(a, b) => {
                let left = Self::from_expr(a, var)?;
                let right = Self::from_expr(b, var)?;
                Some(left * right)
            }
            Expr::Div(a, b) => {
                let denom = match &**b {
                    Expr::Constant(c) => c.clone(),
                    _ => return None,
                };
                let mut poly = Self::from_expr(a, var)?;
                for coeff in poly.coeffs.values_mut() {
                    *coeff /= denom.clone();
                }
                Some(poly)
            }
            Expr::Neg(inner) => Some(-Self::from_expr(inner, var)?),
            Expr::Pow(base, exp) => {
                let power = match extract_integer(exp) {
                    Some(k) if k >= 0 => k as usize,
                    _ => return None,
                };
                let base_poly = Self::from_expr(base, var)?;
                Some(base_poly.pow(power))
            }
            _ => None,
        }
    }

    pub fn derivative(&self) -> Self {
        let mut coeffs = BTreeMap::new();
        for (exp, coeff) in &self.coeffs {
            if *exp == 0 {
                continue;
            }
            let new_exp = exp - 1;
            let factor = Rational::from_integer(BigInt::from(*exp as i64));
            coeffs.insert(new_exp, coeff.clone() * factor);
        }
        Polynomial { coeffs }
    }

    pub fn monic(&self) -> Self {
        let lc = self.leading_coeff();
        if Zero::is_zero(&lc) {
            return self.clone();
        }
        self.scale(&(<Rational as One>::one() / lc))
    }

    pub fn evaluate(&self, x: &Rational) -> Rational {
        let mut acc: Rational = Zero::zero();
        let mut pow: Rational = One::one();
        for exp in 0..=self.degree().unwrap_or(0) {
            if let Some(coeff) = self.coeffs.get(&exp) {
                acc += coeff * pow.clone();
            }
            pow *= x.clone();
        }
        acc
    }

    pub fn div_rem(&self, divisor: &Self) -> (Self, Self) {
        if divisor.is_zero() {
            return (Polynomial::zero(), self.clone());
        }
        let mut remainder = self.clone();
        let mut quotient = Polynomial::zero();
        let divisor_degree = match divisor.degree() {
            Some(deg) => deg,
            None => return (Polynomial::zero(), remainder),
        };
        let divisor_lc = divisor.leading_coeff();

        while let Some(r_deg) = remainder.degree() {
            if r_deg < divisor_degree {
                break;
            }
            let power = r_deg - divisor_degree;
            let coeff = remainder.leading_coeff() / divisor_lc.clone();
            let mut term = BTreeMap::new();
            term.insert(power, coeff.clone());
            let term_poly = Polynomial { coeffs: term };
            quotient = quotient + term_poly.clone();
            remainder = remainder - &(term_poly * divisor.clone());
        }

        (quotient, remainder)
    }

    pub fn div_exact(&self, divisor: &Self) -> Option<Self> {
        let (q, r) = self.div_rem(divisor);
        if r.is_zero() {
            Some(q)
        } else {
            None
        }
    }

    pub fn linear_root(&self) -> Option<Rational> {
        if self.degree()? != 1 {
            return None;
        }
        let a = self.coeff(1);
        let b = self.coeff(0);
        if Zero::is_zero(&a) { None } else { Some(-b / a) }
    }

    pub fn to_expr(&self, var: &str) -> Expr {
        if self.is_zero() {
            return Expr::Constant(Zero::zero());
        }
        let mut terms: Vec<Expr> = Vec::new();
        for (exp, coeff) in &self.coeffs {
            let base = if *exp == 0 {
                Expr::Constant(coeff.clone())
            } else {
                let pow = if *exp == 1 {
                    Expr::Variable(var.to_string())
                } else {
                    Expr::Pow(
                        Expr::Variable(var.to_string()).boxed(),
                        Expr::Constant(Rational::from_integer(BigInt::from(*exp as i64))).boxed(),
                    )
                };
                if <Rational as One>::is_one(&coeff) {
                    pow
                } else {
                    Expr::Mul(Expr::Constant(coeff.clone()).boxed(), pow.boxed())
                }
            };
            terms.push(base);
        }
        terms.sort();
        terms
            .into_iter()
            .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
            .unwrap()
    }

    pub fn content(&self) -> Rational {
        self.content_and_primitive_part().0
    }

    pub fn primitive_part(&self) -> Self {
        self.content_and_primitive_part().1
    }

    pub fn content_and_primitive_part(&self) -> (Rational, Self) {
        if self.is_zero() {
            return (Zero::zero(), Polynomial::zero());
        }
        let mut lcm = BigInt::one();
        for coeff in self.coeffs.values() {
            lcm = lcm.lcm(coeff.denom());
        }

        let mut gcd_num = BigInt::zero();
        let mut scaled_nums = BTreeMap::new();
        for (exp, coeff) in &self.coeffs {
            let scaled = coeff * Rational::from_integer(lcm.clone());
            let num = scaled.numer().clone();
            let abs_num = num.abs();
            if gcd_num.is_zero() {
                gcd_num = abs_num;
            } else {
                gcd_num = gcd_num.gcd(&abs_num);
            }
            scaled_nums.insert(*exp, num);
        }

        if gcd_num.is_zero() {
            return (Zero::zero(), Polynomial::zero());
        }

        let mut coeffs = BTreeMap::new();
        for (exp, num) in scaled_nums {
            let reduced = num / gcd_num.clone();
            if !reduced.is_zero() {
                coeffs.insert(exp, Rational::from_integer(reduced));
            }
        }

        let mut primitive = Polynomial { coeffs };
        let mut content = Rational::new(gcd_num, lcm);
        if primitive.leading_coeff().is_negative() {
            primitive = primitive.scale(&Rational::from_integer((-1).into()));
            content = -content;
        }
        (content, primitive)
    }

    pub fn gcd(a: &Poly, b: &Poly) -> Poly {
        let mut r0 = a.clone();
        let mut r1 = b.clone();
        while !r1.is_zero() {
            let (_, r) = r0.div_rem(&r1);
            r0 = r1;
            r1 = r;
        }
        r0.monic()
    }

    pub fn square_free_decomposition(&self) -> Vec<(Poly, usize)> {
        if self.is_zero() || self.degree().unwrap_or(0) == 0 {
            return Vec::new();
        }

        let mut result = Vec::new();
        let mut i = 1;
        let mut g = Poly::gcd(self, &self.derivative());
        let mut y = self.div_exact(&g).unwrap_or_else(Poly::zero);

        while !y.is_one() {
            let z = Poly::gcd(&y, &g);
            let factor = y.div_exact(&z).unwrap_or_else(Poly::zero);
            if !factor.is_one() {
                result.push((factor, i));
            }
            y = z.clone();
            g = g.div_exact(&z).unwrap_or_else(Poly::zero);
            i += 1;
        }

        if !g.is_one() {
            let g_sqrt = g.square_free_decomposition();
            for (part, mult) in g_sqrt {
                result.push((part, mult + i - 1));
            }
        }

        result
    }
}

impl Polynomial<Expr> {
    pub fn from_expr(expr: &Expr, var: &str) -> Option<Self> {
        if !contains_var(expr, var) {
            return Some(Polynomial::from_constant(expr.clone()));
        }

        match expr {
            Expr::Variable(name) if name == var => {
                let mut coeffs = BTreeMap::new();
                coeffs.insert(1, Expr::Constant(One::one()));
                Some(Polynomial { coeffs })
            }
            Expr::Neg(inner) => {
                let poly = Self::from_expr(inner, var)?;
                Some(poly.scale(&Expr::Constant(-<Rational as One>::one())))
            }
            Expr::Add(a, b) => {
                let left = Self::from_expr(a, var)?;
                let right = Self::from_expr(b, var)?;
                Some(left.add(&right))
            }
            Expr::Sub(a, b) => {
                let left = Self::from_expr(a, var)?;
                let right = Self::from_expr(b, var)?;
                Some(left.sub(&right))
            }
            Expr::Mul(a, b) => {
                let left = Self::from_expr(a, var)?;
                let right = Self::from_expr(b, var)?;
                Some(left.mul(&right))
            }
            Expr::Div(a, b) if !contains_var(b, var) => {
                let numer = Self::from_expr(a, var)?;
                let scale = Expr::Div(Expr::Constant(One::one()).boxed(), b.clone().boxed());
                Some(numer.scale(&scale))
            }
            Expr::Pow(base, exp) => {
                let exponent = extract_rational(exp)?;
                if !exponent.is_integer() || exponent < Zero::zero() {
                    return None;
                }
                let power = exponent.to_integer();
                let power = power.to_usize()?;
                let base_poly = Self::from_expr(base, var)?;
                Some(base_poly.pow(power))
            }
            _ => None,
        }
    }
}

fn extract_integer(exp: &Expr) -> Option<i64> {
    match exp {
        Expr::Constant(c) if c.is_integer() => c.to_integer().to_i64(),
        _ => None,
    }
}

fn extract_rational(expr: &Expr) -> Option<Rational> {
    match expr {
        Expr::Constant(n) => Some(n.clone()),
        Expr::Neg(inner) => extract_rational(inner).map(|n| -n),
        _ => None,
    }
}

fn contains_var(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Variable(v) => v == var,
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) | Expr::Pow(a, b) => {
            contains_var(a, var) || contains_var(b, var)
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
        | Expr::Log(inner) => contains_var(inner, var),
        Expr::Constant(_) => false,
    }
}
