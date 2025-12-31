use std::collections::BTreeMap;

use crate::expr::{Expr, Rational};
use crate::simplify::simplify;
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Factorization {
    pub constant: Rational,
    pub factors: Vec<Factor>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Factor {
    pub poly: Poly,
    pub multiplicity: usize,
}

impl Factor {
    pub fn base_expr(&self, var: &str) -> Expr {
        self.poly.to_expr(var)
    }
}

impl Factorization {
    pub fn to_expr(&self, var: &str) -> Expr {
        if self.constant.is_zero() {
            return Expr::Constant(Rational::zero());
        }
        let mut expr = Expr::Constant(self.constant.clone());
        for factor in &self.factors {
            let base = factor.base_expr(var);
            let powered = if factor.multiplicity == 1 {
                base
            } else {
                Expr::Pow(
                    base.boxed(),
                    Expr::Constant(Rational::from_integer(BigInt::from(
                        factor.multiplicity as i64,
                    )))
                    .boxed(),
                )
            };
            expr = Expr::Mul(expr.boxed(), powered.boxed());
        }
        simplify(expr)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Poly {
    pub(crate) coeffs: BTreeMap<usize, Rational>,
}

impl Poly {
    pub fn zero() -> Self {
        Poly {
            coeffs: BTreeMap::new(),
        }
    }

    pub fn one() -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(0, Rational::one());
        Poly { coeffs }
    }

    pub fn from_expr(expr: &Expr, var: &str) -> Option<Self> {
        if !contains_var(expr, var) {
            return match expr {
                Expr::Constant(c) => Some(Poly::from_constant(c.clone())),
                _ => None,
            };
        }
        match expr {
            Expr::Variable(v) if v == var => {
                let mut coeffs = BTreeMap::new();
                coeffs.insert(1, Rational::one());
                Some(Poly { coeffs })
            }
            Expr::Constant(_) => Some(Poly::zero()),
            Expr::Add(a, b) => Some(Poly::from_expr(a, var)? + Poly::from_expr(b, var)?),
            Expr::Sub(a, b) => Some(Poly::from_expr(a, var)? - Poly::from_expr(b, var)?),
            Expr::Mul(a, b) => {
                let left = Poly::from_expr(a, var)?;
                let right = Poly::from_expr(b, var)?;
                Some(left * right)
            }
            Expr::Div(a, b) => {
                let denom = match &**b {
                    Expr::Constant(c) => c.clone(),
                    _ => return None,
                };
                let mut poly = Poly::from_expr(a, var)?;
                for coeff in poly.coeffs.values_mut() {
                    *coeff /= denom.clone();
                }
                Some(poly)
            }
            Expr::Neg(inner) => Some(-Poly::from_expr(inner, var)?),
            Expr::Pow(base, exp) => {
                let power = match extract_integer(exp) {
                    Some(k) if k >= 0 => k as usize,
                    _ => return None,
                };
                let base_poly = Poly::from_expr(base, var)?;
                Some(base_poly.pow(power))
            }
            _ => None,
        }
    }

    pub fn from_constant(c: Rational) -> Self {
        let mut coeffs = BTreeMap::new();
        if !c.is_zero() {
            coeffs.insert(0, c);
        }
        Poly { coeffs }
    }

    pub fn degree(&self) -> Option<usize> {
        self.coeffs.keys().rev().next().cloned()
    }

    pub fn leading_coeff(&self) -> Rational {
        self.degree()
            .and_then(|d| self.coeffs.get(&d).cloned())
            .unwrap_or_else(Rational::zero)
    }

    pub fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    pub fn is_one(&self) -> bool {
        self.coeffs.len() == 1 && self.coeffs.get(&0).map(|c| c.is_one()).unwrap_or(false)
    }

    pub fn coeff(&self, power: usize) -> Rational {
        self.coeffs
            .get(&power)
            .cloned()
            .unwrap_or_else(Rational::zero)
    }

    pub fn coeff_entries(&self) -> impl Iterator<Item = (usize, Rational)> + '_ {
        self.coeffs.iter().map(|(e, c)| (*e, c.clone()))
    }

    pub fn pow(&self, exp: usize) -> Self {
        if exp == 0 {
            return Poly::one();
        }
        let mut result = Poly::one();
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
        Poly { coeffs }
    }

    pub fn monic(&self) -> Self {
        let lc = self.leading_coeff();
        if lc.is_zero() {
            return self.clone();
        }
        self.scale(&(Rational::one() / lc))
    }

    pub fn scale(&self, k: &Rational) -> Self {
        if k.is_zero() {
            return Poly::zero();
        }
        let mut coeffs = BTreeMap::new();
        for (exp, coeff) in &self.coeffs {
            coeffs.insert(*exp, coeff.clone() * k.clone());
        }
        Poly { coeffs }
    }

    pub fn evaluate(&self, x: &Rational) -> Rational {
        let mut acc = Rational::zero();
        let mut pow = Rational::one();
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
            return (Poly::zero(), self.clone());
        }
        let mut remainder = self.clone();
        let mut quotient = Poly::zero();
        let divisor_lc = divisor.leading_coeff();

        while let (Some(r_deg), Some(div_deg)) = (remainder.degree(), divisor.degree()) {
            if r_deg < div_deg {
                break;
            }
            let power = r_deg - div_deg;
            let coeff = remainder.leading_coeff() / divisor_lc.clone();
            let mut term = BTreeMap::new();
            term.insert(power, coeff.clone());
            let term_poly = Poly { coeffs: term };
            quotient = quotient + term_poly.clone();
            remainder = remainder - &(term_poly * divisor.clone());
        }

        (quotient, remainder)
    }

    pub fn div_exact(&self, divisor: &Self) -> Option<Self> {
        let (q, r) = self.div_rem(divisor);
        if r.is_zero() { Some(q) } else { None }
    }

    pub fn linear_root(&self) -> Option<Rational> {
        if self.degree()? != 1 {
            return None;
        }
        let a = self.coeff(1);
        let b = self.coeff(0);
        if a.is_zero() { None } else { Some(-b / a) }
    }

    pub fn to_expr(&self, var: &str) -> Expr {
        if self.is_zero() {
            return Expr::Constant(Rational::zero());
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
                if coeff.is_one() {
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
}

impl std::ops::Add for Poly {
    type Output = Poly;
    fn add(self, rhs: Poly) -> Poly {
        let mut coeffs = self.coeffs.clone();
        for (exp, coeff) in rhs.coeffs {
            let entry = coeffs.entry(exp).or_insert_with(Rational::zero);
            *entry += coeff;
            if entry.is_zero() {
                coeffs.remove(&exp);
            }
        }
        Poly { coeffs }
    }
}

impl std::ops::Add<&Poly> for Poly {
    type Output = Poly;
    fn add(self, rhs: &Poly) -> Poly {
        self + rhs.clone()
    }
}

impl std::ops::Sub for Poly {
    type Output = Poly;
    fn sub(self, rhs: Poly) -> Poly {
        let mut coeffs = self.coeffs.clone();
        for (exp, coeff) in rhs.coeffs {
            let entry = coeffs.entry(exp).or_insert_with(Rational::zero);
            *entry -= coeff;
            if entry.is_zero() {
                coeffs.remove(&exp);
            }
        }
        Poly { coeffs }
    }
}

impl std::ops::Sub<&Poly> for Poly {
    type Output = Poly;
    fn sub(self, rhs: &Poly) -> Poly {
        self - rhs.clone()
    }
}

impl std::ops::Mul for Poly {
    type Output = Poly;
    fn mul(self, rhs: Poly) -> Poly {
        let mut coeffs = BTreeMap::new();
        for (exp_a, coeff_a) in self.coeffs {
            for (exp_b, coeff_b) in &rhs.coeffs {
                let exp = exp_a + exp_b;
                let entry = coeffs.entry(exp).or_insert_with(Rational::zero);
                *entry += coeff_a.clone() * coeff_b.clone();
                if entry.is_zero() {
                    coeffs.remove(&exp);
                }
            }
        }
        Poly { coeffs }
    }
}

impl std::ops::Neg for Poly {
    type Output = Poly;
    fn neg(self) -> Poly {
        let mut coeffs = BTreeMap::new();
        for (exp, coeff) in self.coeffs {
            coeffs.insert(exp, -coeff);
        }
        Poly { coeffs }
    }
}

impl std::ops::Mul<&Poly> for Poly {
    type Output = Poly;
    fn mul(self, rhs: &Poly) -> Poly {
        self * rhs.clone()
    }
}

pub fn factor_polynomial(expr: &Expr, var: &str) -> Option<Factorization> {
    let poly = Poly::from_expr(expr, var)?;
    if poly.is_zero() {
        return Some(Factorization {
            constant: Rational::zero(),
            factors: Vec::new(),
        });
    }

    let constant = poly.leading_coeff();
    let monic = poly.monic();
    let mut factors = Vec::new();

    let sf = square_free_parts(&monic);
    for (part, multiplicity) in sf {
        let mut stack = vec![part];
        while let Some(current) = stack.pop() {
            if current.degree() == Some(1) {
                factors.push(Factor {
                    poly: current,
                    multiplicity,
                });
                continue;
            }

            if let Some(root) = find_rational_root(&current) {
                let divider = Poly::from_expr(
                    &Expr::Sub(
                        Expr::Variable(var.to_string()).boxed(),
                        Expr::Constant(root.clone()).boxed(),
                    ),
                    var,
                )?;
                factors.push(Factor {
                    poly: divider.clone(),
                    multiplicity,
                });
                let next = current.div_exact(&divider)?;
                stack.push(next);
                continue;
            }

            if current.degree() == Some(4) {
                if let Some((a, b)) = split_quartic(&current) {
                    stack.push(a);
                    stack.push(b);
                    continue;
                }
            }

            factors.push(Factor {
                poly: current,
                multiplicity,
            });
        }
    }

    factors.sort_by(|a, b| {
        let deg_a = a.poly.degree().unwrap_or(0);
        let deg_b = b.poly.degree().unwrap_or(0);
        deg_a
            .cmp(&deg_b)
            .then_with(|| a.poly.to_expr(var).cmp(&b.poly.to_expr(var)))
    });

    Some(Factorization { constant, factors })
}

pub fn factor_polynomial_expr(expr: &Expr, var: &str) -> Option<Expr> {
    factor_polynomial(expr, var).map(|f| f.to_expr(var))
}

fn square_free_parts(poly: &Poly) -> Vec<(Poly, usize)> {
    let mut result = Vec::new();
    let mut i = 1;
    let mut g = Poly::gcd(poly, &poly.derivative());
    let mut y = poly.div_exact(&g).unwrap_or_else(Poly::zero);

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
        let g_sqrt = square_free_parts(&g);
        for (part, mult) in g_sqrt {
            result.push((part, mult + i - 1));
        }
    }

    result
}

fn find_rational_root(poly: &Poly) -> Option<Rational> {
    let degree = poly.degree()?;
    if degree == 0 {
        return None;
    }
    if degree == 1 {
        return poly.linear_root();
    }

    let (int_coeffs, _) = integer_coeffs(poly);
    let leading = int_coeffs.last()?.clone();
    let constant = int_coeffs.first()?.clone();

    let p_candidates = divisors(&constant);
    let q_candidates = divisors(&leading);

    let mut candidates = Vec::new();
    for p in &p_candidates {
        for q in &q_candidates {
            if q.is_zero() {
                continue;
            }
            let candidate = Rational::new(p.clone(), q.clone());
            candidates.push(candidate.clone());
            candidates.push(-candidate);
        }
    }
    candidates.sort();
    candidates.dedup();

    for candidate in candidates {
        if poly.evaluate(&candidate).is_zero() {
            return Some(candidate);
        }
    }
    None
}

fn integer_coeffs(poly: &Poly) -> (Vec<BigInt>, BigInt) {
    let mut lcm = BigInt::one();
    for coeff in poly.coeffs.values() {
        lcm = num_integer::lcm(lcm, coeff.denom().clone());
    }
    let degree = poly.degree().unwrap_or(0);
    let mut coeffs = vec![BigInt::zero(); degree + 1];
    for (exp, coeff) in &poly.coeffs {
        let scaled = coeff * Rational::from_integer(lcm.clone());
        coeffs[*exp] = scaled.numer().clone();
    }
    (coeffs, lcm)
}

fn divisors(n: &BigInt) -> Vec<BigInt> {
    let mut result = Vec::new();
    let abs_n = n.abs();
    if abs_n.is_zero() {
        return vec![BigInt::zero()];
    }
    let mut d = BigInt::one();
    while &d * &d <= abs_n {
        if (&abs_n % &d).is_zero() {
            result.push(d.clone());
            let other = &abs_n / &d;
            if other != d {
                result.push(other);
            }
        }
        d += 1;
    }
    result.sort();
    result
}

fn extract_integer(exp: &Expr) -> Option<i64> {
    match exp {
        Expr::Constant(c) if c.is_integer() => c.to_integer().to_i64(),
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
        | Expr::Exp(inner)
        | Expr::Log(inner) => contains_var(inner, var),
        Expr::Constant(_) => false,
    }
}

fn rational_divisors(r: &Rational) -> Vec<Rational> {
    let p_divs = divisors(r.numer());
    let q_divs = divisors(r.denom());
    let mut result = Vec::new();
    for p in &p_divs {
        for q in &q_divs {
            if q.is_zero() {
                continue;
            }
            let frac = Rational::new(p.clone(), q.clone());
            result.push(frac.clone());
            result.push(-frac);
        }
    }
    result.sort();
    result.dedup();
    result
}

fn perfect_square_rational(r: &Rational) -> Option<Rational> {
    if r.is_negative() {
        return None;
    }
    let num_root = integer_sqrt_exact(r.numer())?;
    let den_root = integer_sqrt_exact(r.denom())?;
    Some(Rational::new(num_root, den_root))
}

fn integer_sqrt_exact(n: &BigInt) -> Option<BigInt> {
    if n.is_negative() {
        return None;
    }
    let root = n.sqrt();
    if &root * &root == *n {
        Some(root)
    } else {
        None
    }
}

fn split_quartic(poly: &Poly) -> Option<(Poly, Poly)> {
    if poly.degree()? != 4 {
        return None;
    }
    if poly.leading_coeff() != Rational::one() {
        return None;
    }

    let p3 = poly.coeff(3);
    let p2 = poly.coeff(2);
    let p1 = poly.coeff(1);
    let p0 = poly.coeff(0);

    let candidates = rational_divisors(&p0);
    for b in &candidates {
        if b.is_zero() && !p0.is_zero() {
            continue;
        }
        for d in &candidates {
            if (b * d) != p0 {
                continue;
            }
            let ac = p2.clone() - b - d;
            let discriminant =
                p3.clone() * p3.clone() - Rational::from_integer(4.into()) * ac.clone();
            if let Some(sqrt) = perfect_square_rational(&discriminant) {
                let two = Rational::from_integer(2.into());
                let a1 = (p3.clone() + sqrt.clone()) / two.clone();
                let c1 = p3.clone() - a1.clone();
                if check_quartic_match(&a1, b, &c1, d, &p1) {
                    let f1 = Poly::from_expr(
                        &Expr::Add(
                            Expr::Add(
                                Expr::Pow(
                                    Expr::Variable("x".into()).boxed(),
                                    Expr::Constant(Rational::from_integer(2.into())).boxed(),
                                )
                                .boxed(),
                                Expr::Mul(
                                    Expr::Constant(a1.clone()).boxed(),
                                    Expr::Variable("x".into()).boxed(),
                                )
                                .boxed(),
                            )
                            .boxed(),
                            Expr::Constant(b.clone()).boxed(),
                        ),
                        "x",
                    )?;
                    let f2 = Poly::from_expr(
                        &Expr::Add(
                            Expr::Add(
                                Expr::Pow(
                                    Expr::Variable("x".into()).boxed(),
                                    Expr::Constant(Rational::from_integer(2.into())).boxed(),
                                )
                                .boxed(),
                                Expr::Mul(
                                    Expr::Constant(c1.clone()).boxed(),
                                    Expr::Variable("x".into()).boxed(),
                                )
                                .boxed(),
                            )
                            .boxed(),
                            Expr::Constant(d.clone()).boxed(),
                        ),
                        "x",
                    )?;
                    return Some((f1, f2));
                }

                let a2 = (p3.clone() - sqrt.clone()) / two.clone();
                let c2 = p3.clone() - a2.clone();
                if check_quartic_match(&a2, b, &c2, d, &p1) {
                    let f1 = Poly::from_expr(
                        &Expr::Add(
                            Expr::Add(
                                Expr::Pow(
                                    Expr::Variable("x".into()).boxed(),
                                    Expr::Constant(Rational::from_integer(2.into())).boxed(),
                                )
                                .boxed(),
                                Expr::Mul(
                                    Expr::Constant(a2.clone()).boxed(),
                                    Expr::Variable("x".into()).boxed(),
                                )
                                .boxed(),
                            )
                            .boxed(),
                            Expr::Constant(b.clone()).boxed(),
                        ),
                        "x",
                    )?;
                    let f2 = Poly::from_expr(
                        &Expr::Add(
                            Expr::Add(
                                Expr::Pow(
                                    Expr::Variable("x".into()).boxed(),
                                    Expr::Constant(Rational::from_integer(2.into())).boxed(),
                                )
                                .boxed(),
                                Expr::Mul(
                                    Expr::Constant(c2.clone()).boxed(),
                                    Expr::Variable("x".into()).boxed(),
                                )
                                .boxed(),
                            )
                            .boxed(),
                            Expr::Constant(d.clone()).boxed(),
                        ),
                        "x",
                    )?;
                    return Some((f1, f2));
                }
            }
        }
    }
    None
}

fn check_quartic_match(
    a: &Rational,
    b: &Rational,
    c: &Rational,
    d: &Rational,
    target_p1: &Rational,
) -> bool {
    let lhs = a * d + b * c;
    lhs == *target_p1
}

impl Poly {
    pub fn gcd(a: &Poly, b: &Poly) -> Poly {
        if b.is_zero() {
            return a.monic();
        }
        let (_, r) = a.div_rem(b);
        if r.is_zero() {
            return b.monic();
        }
        Poly::gcd(b, &r)
    }
}
