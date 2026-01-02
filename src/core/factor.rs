use crate::core::expr::{Expr, Rational};
pub use crate::core::polynomial::Poly;
use crate::simplify::simplify;
use num_bigint::BigInt;
use num_integer::Integer;
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

    for (part, multiplicity) in monic.square_free_decomposition() {
        if part.is_one() {
            continue;
        }
        let (_, primitive) = part.content_and_primitive_part();
        let int_poly = IntPoly::from_poly_exact(&primitive)?;
        for factor in factor_integer_polynomial(&int_poly) {
            let monic_factor = factor.to_monic_poly();
            if monic_factor.is_one() {
                continue;
            }
            factors.push(Factor {
                poly: monic_factor,
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

#[derive(Clone, Debug, PartialEq, Eq)]
struct IntPoly {
    coeffs: Vec<BigInt>,
}

impl IntPoly {
    fn new(mut coeffs: Vec<BigInt>) -> Self {
        while coeffs.last().map(|c| c.is_zero()).unwrap_or(false) {
            coeffs.pop();
        }
        IntPoly { coeffs }
    }

    fn zero() -> Self {
        IntPoly { coeffs: Vec::new() }
    }

    fn one() -> Self {
        IntPoly::new(vec![BigInt::one()])
    }

    fn degree(&self) -> Option<usize> {
        if self.coeffs.is_empty() {
            None
        } else {
            Some(self.coeffs.len() - 1)
        }
    }

    fn leading_coeff(&self) -> BigInt {
        self.coeffs.last().cloned().unwrap_or_else(BigInt::zero)
    }

    fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    fn is_one(&self) -> bool {
        self.coeffs.len() == 1 && self.coeffs[0].is_one()
    }

    fn sub(&self, other: &Self) -> Self {
        let len = self.coeffs.len().max(other.coeffs.len());
        let mut coeffs = vec![BigInt::zero(); len];
        for i in 0..len {
            let a = self.coeffs.get(i).cloned().unwrap_or_else(BigInt::zero);
            let b = other.coeffs.get(i).cloned().unwrap_or_else(BigInt::zero);
            coeffs[i] = a - b;
        }
        IntPoly::new(coeffs)
    }

    fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return IntPoly::zero();
        }
        let mut coeffs = vec![BigInt::zero(); self.coeffs.len() + other.coeffs.len() - 1];
        for (i, a) in self.coeffs.iter().enumerate() {
            for (j, b) in other.coeffs.iter().enumerate() {
                coeffs[i + j] += a * b;
            }
        }
        IntPoly::new(coeffs)
    }

    fn content(&self) -> BigInt {
        let mut gcd = BigInt::zero();
        for coeff in &self.coeffs {
            let abs = coeff.abs();
            if gcd.is_zero() {
                gcd = abs;
            } else {
                gcd = gcd.gcd(&abs);
            }
        }
        gcd
    }

    fn primitive_part(&self) -> Self {
        let content = self.content();
        if content.is_zero() || content.is_one() {
            return self.clone();
        }
        let coeffs = self
            .coeffs
            .iter()
            .map(|c| c / content.clone())
            .collect();
        IntPoly::new(coeffs)
    }

    fn mod_coeffs(&self, modulus: &BigInt) -> Self {
        let coeffs = self
            .coeffs
            .iter()
            .map(|c| mod_bigint(c, modulus))
            .collect();
        IntPoly::new(coeffs)
    }

    fn centered(&self, modulus: &BigInt) -> Self {
        let half = modulus / 2;
        let coeffs = self
            .coeffs
            .iter()
            .map(|c| {
                let mut value = mod_bigint(c, modulus);
                if value > half {
                    value -= modulus;
                }
                value
            })
            .collect();
        IntPoly::new(coeffs)
    }

    fn div_coeffs_exact(&self, divisor: &BigInt) -> Self {
        let coeffs = self
            .coeffs
            .iter()
            .map(|c| c / divisor)
            .collect();
        IntPoly::new(coeffs)
    }

    fn to_poly(&self) -> Poly {
        if self.is_zero() {
            return Poly::zero();
        }
        let mut coeffs = std::collections::BTreeMap::new();
        for (exp, coeff) in self.coeffs.iter().enumerate() {
            if !coeff.is_zero() {
                coeffs.insert(exp, Rational::from_integer(coeff.clone()));
            }
        }
        Poly { coeffs }
    }

    fn to_monic_poly(&self) -> Poly {
        if self.is_zero() {
            return Poly::zero();
        }
        let lc = Rational::from_integer(self.leading_coeff());
        self.to_poly().scale(&(Rational::one() / lc))
    }

    fn from_poly_exact(poly: &Poly) -> Option<Self> {
        if poly.is_zero() {
            return Some(IntPoly::zero());
        }
        let degree = poly.degree().unwrap_or(0);
        let mut coeffs = vec![BigInt::zero(); degree + 1];
        for (exp, coeff) in poly.coeff_entries() {
            if !coeff.denom().is_one() {
                return None;
            }
            coeffs[exp] = coeff.numer().clone();
        }
        Some(IntPoly::new(coeffs))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ModPoly {
    coeffs: Vec<u64>,
    p: u64,
}

impl ModPoly {
    fn new(mut coeffs: Vec<u64>, p: u64) -> Self {
        let modulus = p;
        for coeff in &mut coeffs {
            *coeff %= modulus;
        }
        while coeffs.last().map(|c| *c == 0).unwrap_or(false) {
            coeffs.pop();
        }
        ModPoly { coeffs, p }
    }

    fn zero(p: u64) -> Self {
        ModPoly::new(Vec::new(), p)
    }

    fn one(p: u64) -> Self {
        ModPoly::new(vec![1], p)
    }

    fn degree(&self) -> Option<usize> {
        if self.coeffs.is_empty() {
            None
        } else {
            Some(self.coeffs.len() - 1)
        }
    }

    fn leading_coeff(&self) -> u64 {
        *self.coeffs.last().unwrap_or(&0)
    }

    fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    fn is_one(&self) -> bool {
        self.coeffs.len() == 1 && self.coeffs[0] == 1
    }

    fn add(&self, other: &Self) -> Self {
        let len = self.coeffs.len().max(other.coeffs.len());
        let mut coeffs = vec![0u64; len];
        for i in 0..len {
            let a = self.coeffs.get(i).cloned().unwrap_or(0);
            let b = other.coeffs.get(i).cloned().unwrap_or(0);
            coeffs[i] = (a + b) % self.p;
        }
        ModPoly::new(coeffs, self.p)
    }

    fn sub(&self, other: &Self) -> Self {
        let len = self.coeffs.len().max(other.coeffs.len());
        let mut coeffs = vec![0u64; len];
        for i in 0..len {
            let a = self.coeffs.get(i).cloned().unwrap_or(0);
            let b = other.coeffs.get(i).cloned().unwrap_or(0);
            coeffs[i] = (self.p + a - (b % self.p)) % self.p;
        }
        ModPoly::new(coeffs, self.p)
    }

    fn scale(&self, k: u64) -> Self {
        if k % self.p == 0 {
            return ModPoly::zero(self.p);
        }
        let mut coeffs = Vec::with_capacity(self.coeffs.len());
        for coeff in &self.coeffs {
            let value = (*coeff as u128 * k as u128) % self.p as u128;
            coeffs.push(value as u64);
        }
        ModPoly::new(coeffs, self.p)
    }

    fn mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return ModPoly::zero(self.p);
        }
        let mut coeffs = vec![0u64; self.coeffs.len() + other.coeffs.len() - 1];
        for (i, a) in self.coeffs.iter().enumerate() {
            for (j, b) in other.coeffs.iter().enumerate() {
                let prod = (*a as u128 * *b as u128) % self.p as u128;
                let idx = i + j;
                let sum = (coeffs[idx] as u128 + prod) % self.p as u128;
                coeffs[idx] = sum as u64;
            }
        }
        ModPoly::new(coeffs, self.p)
    }

    fn monic(&self) -> Self {
        if self.is_zero() {
            return self.clone();
        }
        let lc = self.leading_coeff();
        let inv = modinv(lc, self.p);
        self.scale(inv)
    }

    fn derivative(&self) -> Self {
        if self.coeffs.len() <= 1 {
            return ModPoly::zero(self.p);
        }
        let mut coeffs = Vec::with_capacity(self.coeffs.len() - 1);
        for (i, coeff) in self.coeffs.iter().enumerate().skip(1) {
            let factor = (i as u64) % self.p;
            let value = (*coeff as u128 * factor as u128) % self.p as u128;
            coeffs.push(value as u64);
        }
        ModPoly::new(coeffs, self.p)
    }

    fn div_rem(&self, divisor: &Self) -> (Self, Self) {
        if divisor.is_zero() {
            return (ModPoly::zero(self.p), self.clone());
        }
        let mut remainder = self.clone();
        let mut quotient = ModPoly::zero(self.p);
        let divisor_deg = divisor.degree().unwrap_or(0);
        let divisor_lc = divisor.leading_coeff();
        let inv_lc = modinv(divisor_lc, self.p);

        while let Some(r_deg) = remainder.degree() {
            if r_deg < divisor_deg {
                break;
            }
            let power = r_deg - divisor_deg;
            let coeff = (remainder.leading_coeff() as u128 * inv_lc as u128) % self.p as u128;
            let mut term = vec![0u64; power + 1];
            term[power] = coeff as u64;
            let term_poly = ModPoly::new(term, self.p);
            quotient = quotient.add(&term_poly);
            let subtrahend = term_poly.mul(divisor);
            remainder = remainder.sub(&subtrahend);
        }

        (quotient, remainder)
    }

    fn div_exact(&self, divisor: &Self) -> Option<Self> {
        let (q, r) = self.div_rem(divisor);
        if r.is_zero() {
            Some(q)
        } else {
            None
        }
    }

    fn gcd(&self, other: &Self) -> Self {
        let mut r0 = self.clone();
        let mut r1 = other.clone();
        while !r1.is_zero() {
            let (_, r) = r0.div_rem(&r1);
            r0 = r1;
            r1 = r;
        }
        r0.monic()
    }
}

fn factor_integer_polynomial(poly: &IntPoly) -> Vec<IntPoly> {
    if poly.degree().unwrap_or(0) <= 1 {
        return vec![poly.clone()];
    }

    let poly = poly.primitive_part();
    if let Some((factor, quotient)) = rational_root_factor(&poly) {
        let mut result = vec![factor];
        result.extend(factor_integer_polynomial(&quotient));
        return result;
    }
    let primes: [u64; 25] = [
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
        79, 83, 89, 97,
    ];

    for &p in &primes {
        if p == 0 {
            continue;
        }
        let lc = poly.leading_coeff();
        if (&lc % BigInt::from(p)).is_zero() {
            continue;
        }
        let f_mod = mod_poly_from_int(&poly, p);
        if f_mod.is_zero() {
            continue;
        }
        if !is_square_free_mod(&f_mod) {
            continue;
        }

        let mod_factors = berlekamp_factor(&f_mod);
        if mod_factors.len() <= 1 {
            continue;
        }

        let bound = coefficient_bound(&poly);
        let (modulus, k) = prime_power_over_bound(p, &bound);
        let lifted = hensel_lift_factors(&poly, &mod_factors, p, k);
        let combined = recombine_factors(&poly, &lifted, &modulus);
        if combined.len() > 1 {
            let mut result = Vec::new();
            for factor in combined {
                if factor.degree().unwrap_or(0) <= 1 {
                    result.push(factor);
                } else {
                    result.extend(factor_integer_polynomial(&factor));
                }
            }
            return result;
        }
    }

    vec![poly.clone()]
}

fn coefficient_bound(poly: &IntPoly) -> BigInt {
    let max_coeff = poly
        .coeffs
        .iter()
        .map(|c| c.abs())
        .max()
        .unwrap_or_else(BigInt::zero);
    let degree = poly.degree().unwrap_or(0);
    let mut factor = BigInt::one();
    for _ in 0..degree {
        factor <<= 1;
    }
    max_coeff * factor
}

fn prime_power_over_bound(p: u64, bound: &BigInt) -> (BigInt, usize) {
    let mut modulus = BigInt::from(p);
    let mut k = 1usize;
    let target = bound * 2;
    while &modulus <= &target {
        modulus *= p;
        k += 1;
    }
    (modulus, k)
}

fn mod_poly_from_int(poly: &IntPoly, p: u64) -> ModPoly {
    let coeffs = poly
        .coeffs
        .iter()
        .map(|c| mod_bigint_u64(c, p))
        .collect();
    ModPoly::new(coeffs, p)
}

fn is_square_free_mod(poly: &ModPoly) -> bool {
    let deriv = poly.derivative();
    if deriv.is_zero() {
        return false;
    }
    poly.gcd(&deriv).is_one()
}

fn berlekamp_factor(poly: &ModPoly) -> Vec<ModPoly> {
    let lc = poly.leading_coeff();
    let monic = poly.monic();
    if monic.degree().unwrap_or(0) <= 1 {
        return vec![poly.clone()];
    }

    let mut factors = berlekamp_factor_monic(&monic);
    if lc != 1 && !factors.is_empty() {
        factors[0] = factors[0].scale(lc);
    }
    factors
}

fn berlekamp_factor_monic(poly: &ModPoly) -> Vec<ModPoly> {
    if poly.degree().unwrap_or(0) <= 1 {
        return vec![poly.clone()];
    }

    let basis = berlekamp_basis(poly);
    if basis.len() <= 1 {
        return vec![poly.clone()];
    }

    for vector in &basis {
        let candidate = ModPoly::new(vector.clone(), poly.p);
        if candidate.degree().unwrap_or(0) == 0 {
            continue;
        }
        for a in 0..poly.p {
            let mut shifted = candidate.clone();
            if shifted.coeffs.is_empty() {
                shifted.coeffs.push(0);
            }
            shifted.coeffs[0] = (shifted.coeffs[0] + poly.p - a) % poly.p;
            let g = poly.gcd(&shifted);
            if g.degree().unwrap_or(0) > 0 && g.degree() < poly.degree() {
                let other = poly.div_exact(&g).unwrap_or_else(|| ModPoly::one(poly.p));
                let mut left = berlekamp_factor_monic(&g);
                let mut right = berlekamp_factor_monic(&other);
                left.append(&mut right);
                return left;
            }
        }
    }

    if basis.len() > 2 {
        let polys: Vec<ModPoly> = basis
            .iter()
            .cloned()
            .map(|vec| ModPoly::new(vec, poly.p))
            .filter(|p| p.degree().unwrap_or(0) > 0)
            .collect();
        for i in 0..polys.len() {
            for j in (i + 1)..polys.len() {
                for a in 0..poly.p {
                    for b in 0..poly.p {
                        if a == 0 && b == 0 {
                            continue;
                        }
                        let candidate = polys[i].scale(a).add(&polys[j].scale(b));
                        for c in 0..poly.p {
                            let mut shifted = candidate.clone();
                            if shifted.coeffs.is_empty() {
                                shifted.coeffs.push(0);
                            }
                            shifted.coeffs[0] = (shifted.coeffs[0] + poly.p - c) % poly.p;
                            let g = poly.gcd(&shifted);
                            if g.degree().unwrap_or(0) > 0 && g.degree() < poly.degree() {
                                let other =
                                    poly.div_exact(&g).unwrap_or_else(|| ModPoly::one(poly.p));
                                let mut left = berlekamp_factor_monic(&g);
                                let mut right = berlekamp_factor_monic(&other);
                                left.append(&mut right);
                                return left;
                            }
                        }
                    }
                }
            }
        }
    }

    vec![poly.clone()]
}

fn berlekamp_basis(poly: &ModPoly) -> Vec<Vec<u64>> {
    let n = poly.degree().unwrap_or(0);
    if n == 0 {
        return vec![vec![1]];
    }

    let x = ModPoly::new(vec![0, 1], poly.p);
    let x_p = pow_mod_poly(&x, poly.p as u64, poly);
    let mut powers = Vec::with_capacity(n);
    let mut current = ModPoly::one(poly.p);
    for _ in 0..n {
        powers.push(current.clone());
        current = current.mul(&x_p).div_rem(poly).1;
    }

    let mut matrix = vec![vec![0u64; n]; n];
    for (col, power) in powers.iter().enumerate() {
        for (row, coeff) in power.coeffs.iter().enumerate() {
            if row < n {
                matrix[row][col] = *coeff % poly.p;
            }
        }
    }

    for i in 0..n {
        matrix[i][i] = (matrix[i][i] + poly.p - 1) % poly.p;
    }

    nullspace(matrix, poly.p)
}

fn nullspace(mut matrix: Vec<Vec<u64>>, p: u64) -> Vec<Vec<u64>> {
    let n = matrix.len();
    if n == 0 {
        return vec![Vec::new()];
    }
    let m = matrix[0].len();
    let mut pivot_cols = Vec::new();
    let mut row = 0usize;

    for col in 0..m {
        let mut pivot = None;
        for r in row..n {
            if matrix[r][col] != 0 {
                pivot = Some(r);
                break;
            }
        }
        if pivot.is_none() {
            continue;
        }
        let pivot_row = pivot.unwrap();
        matrix.swap(row, pivot_row);
        let inv = modinv(matrix[row][col], p);
        for c in col..m {
            matrix[row][c] = (matrix[row][c] as u128 * inv as u128 % p as u128) as u64;
        }
        for r in 0..n {
            if r == row {
                continue;
            }
            let factor = matrix[r][col];
            if factor == 0 {
                continue;
            }
            for c in col..m {
                let value = (p as i128
                    + matrix[r][c] as i128
                    - (factor as i128 * matrix[row][c] as i128) % p as i128)
                    % p as i128;
                matrix[r][c] = value as u64;
            }
        }
        pivot_cols.push(col);
        row += 1;
        if row == n {
            break;
        }
    }

    let mut pivot_set = vec![false; m];
    for &col in &pivot_cols {
        pivot_set[col] = true;
    }

    let mut basis = Vec::new();
    for free_col in 0..m {
        if pivot_set[free_col] {
            continue;
        }
        let mut vec = vec![0u64; m];
        vec[free_col] = 1;
        for (r, &col) in pivot_cols.iter().enumerate() {
            let value = matrix[r][free_col];
            if value != 0 {
                vec[col] = (p - value) % p;
            }
        }
        basis.push(vec);
    }

    if basis.is_empty() {
        basis.push(vec![0u64; m]);
    }

    basis
}

fn pow_mod_poly(base: &ModPoly, exp: u64, modulus: &ModPoly) -> ModPoly {
    let mut result = ModPoly::one(base.p);
    let mut base_pow = base.clone();
    let mut e = exp;
    while e > 0 {
        if e % 2 == 1 {
            result = result.mul(&base_pow).div_rem(modulus).1;
        }
        base_pow = base_pow.mul(&base_pow).div_rem(modulus).1;
        e /= 2;
    }
    result
}

fn modinv(a: u64, p: u64) -> u64 {
    let mut t: i128 = 0;
    let mut new_t: i128 = 1;
    let mut r: i128 = p as i128;
    let mut new_r: i128 = (a % p) as i128;
    while new_r != 0 {
        let quotient = r / new_r;
        let tmp_t = t - quotient * new_t;
        t = new_t;
        new_t = tmp_t;
        let tmp_r = r - quotient * new_r;
        r = new_r;
        new_r = tmp_r;
    }
    if r > 1 {
        0
    } else {
        let mut result = t;
        if result < 0 {
            result += p as i128;
        }
        result as u64
    }
}

fn hensel_lift_factors(
    poly: &IntPoly,
    factors: &[ModPoly],
    p: u64,
    k: usize,
) -> Vec<IntPoly> {
    if factors.len() == 1 {
        return vec![poly.mod_coeffs(&pow_bigint(p, k))];
    }
    let mid = factors.len() / 2;
    let left = &factors[..mid];
    let right = &factors[mid..];

    let g0 = product_mod_poly(left, p);
    let h0 = product_mod_poly(right, p);
    let (g_lift, h_lift) = hensel_lift_pair(poly, &g0, &h0, p, k);

    let mut lifted_left = hensel_lift_factors(&g_lift, left, p, k);
    let mut lifted_right = hensel_lift_factors(&h_lift, right, p, k);
    lifted_left.append(&mut lifted_right);
    lifted_left
}

fn hensel_lift_pair(
    poly: &IntPoly,
    g0: &ModPoly,
    h0: &ModPoly,
    p: u64,
    k: usize,
) -> (IntPoly, IntPoly) {
    let p_big = BigInt::from(p);
    let modulus_target = pow_bigint(p, k);
    let mut modulus = p_big.clone();
    let mut g = int_from_mod(g0);
    let mut h = int_from_mod(h0);

    let (s, t) = bezout_mod_poly(g0, h0);

    while modulus < modulus_target {
        let new_modulus = &modulus * &p_big;
        let prod = g.mul(&h);
        let e = poly.sub(&prod);
        let e_div = e.div_coeffs_exact(&modulus);
        let e_mod = mod_poly_from_int(&e_div, p);
        let delta_g = t.mul(&e_mod);
        let delta_h = s.mul(&e_mod);

        g = add_scaled_mod(&g, &delta_g, &modulus, &new_modulus);
        h = add_scaled_mod(&h, &delta_h, &modulus, &new_modulus);
        modulus = new_modulus;
    }

    (g.mod_coeffs(&modulus_target), h.mod_coeffs(&modulus_target))
}

fn bezout_mod_poly(a: &ModPoly, b: &ModPoly) -> (ModPoly, ModPoly) {
    let mut r0 = a.clone();
    let mut r1 = b.clone();
    let mut s0 = ModPoly::one(a.p);
    let mut s1 = ModPoly::zero(a.p);
    let mut t0 = ModPoly::zero(a.p);
    let mut t1 = ModPoly::one(a.p);

    while !r1.is_zero() {
        let (q, r) = r0.div_rem(&r1);
        r0 = r1;
        r1 = r;
        let s2 = s0.sub(&q.mul(&s1));
        s0 = s1;
        s1 = s2;
        let t2 = t0.sub(&q.mul(&t1));
        t0 = t1;
        t1 = t2;
    }

    let lc = r0.leading_coeff();
    if lc != 1 && lc != 0 {
        let inv = modinv(lc, a.p);
        s0 = s0.scale(inv);
        t0 = t0.scale(inv);
    }

    (s0, t0)
}

fn product_mod_poly(factors: &[ModPoly], p: u64) -> ModPoly {
    let mut acc = ModPoly::one(p);
    for factor in factors {
        acc = acc.mul(factor);
    }
    acc
}

fn recombine_factors(poly: &IntPoly, factors: &[IntPoly], modulus: &BigInt) -> Vec<IntPoly> {
    let mut remaining: Vec<IntPoly> = factors.iter().cloned().collect();
    let mut result = Vec::new();
    let mut current = poly.clone();

    let mut size = 1usize;
    while size <= remaining.len() / 2 {
        let found = find_subset(&remaining, size, modulus, &current);
        if let Some((factor, subset)) = found {
            if let Some(quotient) = div_exact_int(&current, &factor) {
                result.push(factor);
                current = quotient;
                let mut next_remaining = Vec::new();
                for (idx, f) in remaining.into_iter().enumerate() {
                    if !subset.contains(&idx) {
                        next_remaining.push(f);
                    }
                }
                remaining = next_remaining;
                size = 1;
                continue;
            }
        }
        size += 1;
    }

    if !current.is_one() && !current.is_zero() {
        result.push(current);
    }

    result
}

fn find_subset(
    factors: &[IntPoly],
    size: usize,
    modulus: &BigInt,
    poly: &IntPoly,
) -> Option<(IntPoly, Vec<usize>)> {
    let mut selected = Vec::new();
    let product = IntPoly::one();
    search_subset(
        factors,
        size,
        0,
        modulus,
        poly,
        product,
        &mut selected,
    )
}

fn search_subset(
    factors: &[IntPoly],
    size: usize,
    start: usize,
    modulus: &BigInt,
    poly: &IntPoly,
    current: IntPoly,
    selected: &mut Vec<usize>,
) -> Option<(IntPoly, Vec<usize>)> {
    if size == 0 {
        let candidate = current.centered(modulus).primitive_part();
        if candidate.degree().unwrap_or(0) > 0 && div_exact_int(poly, &candidate).is_some() {
            return Some((candidate, selected.clone()));
        }
        return None;
    }

    for idx in start..=factors.len().saturating_sub(size) {
        selected.push(idx);
        let next = mul_mod_int(&current, &factors[idx], modulus);
        if let Some(found) = search_subset(factors, size - 1, idx + 1, modulus, poly, next, selected)
        {
            return Some(found);
        }
        selected.pop();
    }

    None
}

fn mul_mod_int(a: &IntPoly, b: &IntPoly, modulus: &BigInt) -> IntPoly {
    let prod = a.mul(b);
    prod.mod_coeffs(modulus)
}

fn div_exact_int(poly: &IntPoly, divisor: &IntPoly) -> Option<IntPoly> {
    if divisor.is_zero() {
        return None;
    }
    let poly_q = poly.to_poly();
    let divisor_q = divisor.to_poly();
    let quotient = poly_q.div_exact(&divisor_q)?;
    IntPoly::from_poly_exact(&quotient)
}

fn add_scaled_mod(
    base: &IntPoly,
    delta: &ModPoly,
    scale: &BigInt,
    modulus: &BigInt,
) -> IntPoly {
    let mut coeffs = base.coeffs.clone();
    if coeffs.len() < delta.coeffs.len() {
        coeffs.resize(delta.coeffs.len(), BigInt::zero());
    }
    for (i, coeff) in delta.coeffs.iter().enumerate() {
        let addition = BigInt::from(*coeff) * scale;
        coeffs[i] += addition;
        coeffs[i] = mod_bigint(&coeffs[i], modulus);
    }
    IntPoly::new(coeffs)
}

fn rational_root_factor(poly: &IntPoly) -> Option<(IntPoly, IntPoly)> {
    let degree = poly.degree().unwrap_or(0);
    if degree <= 1 || poly.is_zero() {
        return None;
    }

    if !poly.coeffs.is_empty() && poly.coeffs[0].is_zero() {
        let mut coeffs = poly.coeffs.clone();
        coeffs.remove(0);
        let quotient = IntPoly::new(coeffs);
        let factor = IntPoly::new(vec![BigInt::zero(), BigInt::one()]);
        return Some((factor, quotient));
    }

    let constant = poly.coeffs.first()?.clone();
    let leading = poly.leading_coeff();
    let p_candidates = divisors(&constant);
    let q_candidates = divisors(&leading);
    let poly_q = poly.to_poly();

    for p in &p_candidates {
        for q in &q_candidates {
            if q.is_zero() {
                continue;
            }
            let root = Rational::new(p.clone(), q.clone());
            if poly_q.evaluate(&root).is_zero() {
                let factor = IntPoly::new(vec![-p.clone(), q.clone()]);
                let quotient = div_exact_int(poly, &factor)?;
                return Some((factor, quotient));
            }
            let neg_root = Rational::new(-p.clone(), q.clone());
            if poly_q.evaluate(&neg_root).is_zero() {
                let factor = IntPoly::new(vec![p.clone(), q.clone()]);
                let quotient = div_exact_int(poly, &factor)?;
                return Some((factor, quotient));
            }
        }
    }

    None
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
    result
}

fn int_from_mod(poly: &ModPoly) -> IntPoly {
    let coeffs = poly
        .coeffs
        .iter()
        .map(|c| BigInt::from(*c))
        .collect();
    IntPoly::new(coeffs)
}

fn mod_bigint(value: &BigInt, modulus: &BigInt) -> BigInt {
    value.mod_floor(modulus)
}

fn mod_bigint_u64(value: &BigInt, modulus: u64) -> u64 {
    let modulus_big = BigInt::from(modulus);
    let reduced = value.mod_floor(&modulus_big);
    reduced.to_u64().unwrap_or(0)
}

fn pow_bigint(p: u64, k: usize) -> BigInt {
    let mut result = BigInt::one();
    for _ in 0..k {
        result *= p;
    }
    result
}
