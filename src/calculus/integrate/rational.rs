use crate::core::expr::{Expr, Rational};
use crate::core::factor::{factor_polynomial, Factorization, Poly};
use crate::simplify::simplify;
use super::{flatten_product, log_abs, rebuild_product};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;

pub fn rational_kind(expr: &Expr, var: &str) -> Option<bool> {
    let (num, den) = as_division(expr)?;

    Poly::from_expr(&num, var)?;
    let den_poly = Poly::from_expr(&den, var)?;
    if den_poly.is_zero() {
        return None;
    }

    let degree = den_poly.degree()?;
    if degree == 0 {
        return None;
    }

    let linear = factor_polynomial(&den, var)
        .map(|f| f.factors.iter().all(|factor| factor.poly.degree() == Some(1)))
        .unwrap_or(false);
    Some(linear)
}

pub fn is_rational(expr: &Expr, var: &str) -> bool {
    rational_kind(expr, var).is_some()
}

pub fn integrate(expr: &Expr, var: &str) -> Option<Expr> {
    let (num, den) = as_division(expr)?;

    let mut num_poly = Poly::from_expr(&num, var)?;
    let mut den_poly = Poly::from_expr(&den, var)?;
    if den_poly.is_zero() || den_poly.degree()? == 0 {
        return None;
    }

    let gcd = Poly::gcd(&num_poly, &den_poly);
    if !gcd.is_one() {
        num_poly = num_poly.div_exact(&gcd)?;
        den_poly = den_poly.div_exact(&gcd)?;
    }

    let den_lc = den_poly.leading_coeff();
    if !den_lc.is_one() {
        let scale = Rational::one() / den_lc;
        num_poly = num_poly.scale(&scale);
        den_poly = den_poly.scale(&scale);
    }

    let (quotient, remainder) = num_poly.div_rem(&den_poly);
    let mut pieces: Vec<Expr> = Vec::new();

    if !quotient.is_zero() {
        let q_expr = quotient.to_expr(var);
        let poly_int = super::polynomial::integrate(&q_expr, var)?;
        pieces.push(poly_int);
    }

    if remainder.is_zero() {
        return Some(simplify(sum_exprs(pieces)));
    }

    let (hermite_terms, reduced_terms) = hermite_reduce(&remainder, &den_poly, var)?;
    pieces.extend(hermite_terms);

    for (num_term, den_term) in reduced_terms {
        if num_term.is_zero() {
            continue;
        }
        let mut partial_fraction = integrate_cyclotomic_quartic_quintic(&num_term, &den_term, var);
        if let Some(factorization) = factor_polynomial(&den_term.to_expr(var), var) {
            if !factorization.constant.is_zero()
                && factorization
                    .factors
                    .iter()
                    .all(|f| matches!(f.poly.degree(), Some(1 | 2)))
            {
                let scaled_num =
                    num_term.scale(&(Rational::one() / factorization.constant.clone()));
                let denominator = build_denominator(&factorization);
                partial_fraction = integrate_partial_fraction(
                    &scaled_num,
                    &denominator,
                    &factorization,
                    var,
                );
            }
        }

        let term = match partial_fraction {
            Some(expr) => expr,
            None => integrate_rothstein_trager(&num_term, &den_term, var)?,
        };
        pieces.push(term);
    }

    Some(simplify(sum_exprs(pieces)))
}

fn build_denominator(factorization: &Factorization) -> Poly {
    let mut result = Poly::one();
    for factor in &factorization.factors {
        result = result * factor.poly.pow(factor.multiplicity);
    }
    result
}

fn integrate_partial_fraction(
    remainder: &Poly,
    denominator: &Poly,
    factorization: &Factorization,
    var: &str,
) -> Option<Expr> {
    let basis = basis_for_system(denominator, factorization, var)?;
    let degree = denominator.degree()?;
    if basis.len() != degree {
        return None;
    }

    let mut matrix: Vec<Vec<Rational>> = vec![vec![Rational::zero(); degree + 1]; degree];
    for (col, poly) in basis.iter().enumerate() {
        for (exp, coeff) in poly.coeff_entries() {
            if exp < degree {
                matrix[exp][col] += coeff;
            }
        }
    }
    for (exp, coeff) in remainder.coeff_entries() {
        if exp < degree {
            matrix[exp][degree] = coeff;
        }
    }

    let solution = solve_linear_system(matrix)?;
    let mut terms: Vec<Expr> = Vec::new();
    let mut idx = 0;

    for factor in &factorization.factors {
        match factor.poly.degree()? {
            1 => {
                for power in 1..=factor.multiplicity {
                    let coeff = solution.get(idx)?.clone();
                    idx += 1;
                    if coeff.is_zero() {
                        continue;
                    }
                    terms.push(integrate_linear_term(coeff, &factor.poly, power, var)?);
                }
            }
            2 => {
                for power in 1..=factor.multiplicity {
                    let coeff_x = solution.get(idx)?.clone();
                    let coeff_const = solution.get(idx + 1)?.clone();
                    idx += 2;
                    if coeff_x.is_zero() && coeff_const.is_zero() {
                        continue;
                    }
                    terms.push(integrate_quadratic_term(
                        coeff_x,
                        coeff_const,
                        &factor.poly,
                        power,
                        var,
                    )?);
                }
            }
            _ => return None,
        }
    }

    if idx != solution.len() {
        return None;
    }

    Some(simplify(sum_exprs(terms)))
}

fn hermite_reduce(
    remainder: &Poly,
    denominator: &Poly,
    var: &str,
) -> Option<(Vec<Expr>, Vec<(Poly, Poly)>)> {
    let parts = denominator.square_free_decomposition();
    if parts.is_empty() {
        return Some((Vec::new(), Vec::new()));
    }

    let mut terms: Vec<Expr> = Vec::new();
    let mut reduced_terms: Vec<(Poly, Poly)> = Vec::new();

    for (squarefree, multiplicity) in parts {
        let denom_part = squarefree.pow(multiplicity);
        let other = denominator.div_exact(&denom_part)?;
        let inv_other = if other.is_one() {
            Poly::one()
        } else {
            poly_mod_inverse(&other, &denom_part)?
        };
        let num_part = poly_mod(&(remainder.clone() * inv_other), &denom_part);
        let (mut hermite_terms, reduced_num) =
            hermite_reduce_factor(num_part, &squarefree, multiplicity, var)?;
        terms.append(&mut hermite_terms);
        if !reduced_num.is_zero() {
            reduced_terms.push((reduced_num, squarefree));
        }
    }

    Some((terms, reduced_terms))
}

fn hermite_reduce_factor(
    mut numerator: Poly,
    squarefree: &Poly,
    multiplicity: usize,
    var: &str,
) -> Option<(Vec<Expr>, Poly)> {
    if multiplicity == 0 {
        return None;
    }
    if multiplicity == 1 {
        return Some((Vec::new(), numerator));
    }

    let derivative = squarefree.derivative();
    if derivative.is_zero() {
        return None;
    }
    let inv_derivative = poly_mod_inverse(&derivative, squarefree)?;
    let mut terms: Vec<Expr> = Vec::new();
    let mut power = multiplicity;

    while power > 1 {
        let k_minus_one = Rational::from_integer(BigInt::from((power - 1) as i64));
        let remainder = poly_mod(&numerator, squarefree);
        let u = if remainder.is_zero() {
            Poly::zero()
        } else {
            let scaled = remainder * inv_derivative.clone();
            let scaled = scaled.scale(&(Rational::one() / k_minus_one.clone()));
            poly_mod(&scaled.scale(&Rational::from_integer((-1).into())), squarefree)
        };

        if !u.is_zero() {
            let term = rational_power_term(&u, squarefree, power - 1, var);
            terms.push(simplify(term));
            let u_prime = u.derivative();
            let u_scaled = u.scale(&k_minus_one);
            let numerator_adjust =
                u_prime * squarefree.clone() - u_scaled * derivative.clone();
            let reduced = numerator - numerator_adjust;
            numerator = reduced.div_exact(squarefree)?;
        } else {
            numerator = numerator.div_exact(squarefree)?;
        }

        power -= 1;
    }

    Some((terms, numerator))
}

fn rational_power_term(num: &Poly, den: &Poly, power: usize, var: &str) -> Expr {
    let numerator = num.to_expr(var);
    let exponent = Rational::from_integer(BigInt::from(-(power as i64)));
    let pow = Expr::Pow(
        den.to_expr(var).boxed(),
        Expr::Constant(exponent).boxed(),
    );
    Expr::Mul(numerator.boxed(), pow.boxed())
}

fn poly_mod(poly: &Poly, modulus: &Poly) -> Poly {
    if modulus.is_zero() {
        return poly.clone();
    }
    let (_, remainder) = poly.div_rem(modulus);
    remainder
}

fn poly_mod_inverse(value: &Poly, modulus: &Poly) -> Option<Poly> {
    if modulus.is_zero() {
        return None;
    }
    let (gcd, _s, t) = poly_extended_gcd(modulus, value);
    if !gcd.is_one() {
        return None;
    }
    Some(poly_mod(&t, modulus))
}

fn poly_extended_gcd(a: &Poly, b: &Poly) -> (Poly, Poly, Poly) {
    let mut r0 = a.clone();
    let mut r1 = b.clone();
    let mut s0 = Poly::one();
    let mut s1 = Poly::zero();
    let mut t0 = Poly::zero();
    let mut t1 = Poly::one();

    while !r1.is_zero() {
        let (q, r) = r0.div_rem(&r1);
        r0 = r1;
        r1 = r;
        let s2 = s0.clone() - q.clone() * s1.clone();
        let t2 = t0.clone() - q * t1.clone();
        s0 = s1;
        s1 = s2;
        t0 = t1;
        t1 = t2;
    }

    if r0.is_zero() {
        return (Poly::zero(), Poly::zero(), Poly::zero());
    }

    let lc = r0.leading_coeff();
    if lc.is_zero() {
        return (Poly::zero(), Poly::zero(), Poly::zero());
    }
    let scale = Rational::one() / lc;
    (r0.scale(&scale), s0.scale(&scale), t0.scale(&scale))
}

fn integrate_rothstein_trager(numerator: &Poly, denominator: &Poly, var: &str) -> Option<Expr> {
    if numerator.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let mut a = numerator.clone();
    let mut b = denominator.clone();
    if b.is_zero() {
        return None;
    }

    let lc = b.leading_coeff();
    if !lc.is_one() {
        let scale = Rational::one() / lc;
        a = a.scale(&scale);
        b = b.scale(&scale);
    }

    let gcd = Poly::gcd(&a, &b);
    if !gcd.is_one() {
        a = a.div_exact(&gcd)?;
        b = b.div_exact(&gcd)?;
    }

    a = poly_mod(&a, &b);
    if a.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let b_prime = b.derivative();
    if b_prime.is_zero() {
        return None;
    }

    let a_t_coeffs = coeffs_a_minus_t_bprime(&a, &b_prime);
    let b_coeffs = poly_coeffs_const(&b);
    let resultant = resultant_from_coeffs(&b_coeffs, &a_t_coeffs)?;
    if resultant.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let factorization = factor_polynomial(&resultant.to_expr("t"), "t")?;
    if factorization.constant.is_zero() {
        return None;
    }

    let mut terms = Vec::new();
    for factor in factorization.factors {
        let s = factor.poly;
        let degree = s.degree().unwrap_or(0);
        if degree == 0 {
            continue;
        }
        if degree != 1 {
            // Algebraic residues need algebraic constants, which Expr cannot represent yet.
            return None;
        }
        let gcd_coeffs = poly_x_gcd_mod(&b_coeffs, &a_t_coeffs, &s)?;
        let g_t_coeffs = transpose_coeffs_x_t(&gcd_coeffs);
        if g_t_coeffs.is_empty() {
            continue;
        }
        let s_t_coeffs = poly_coeffs_const(&s);
        let res_xt = resultant_from_coeffs(&s_t_coeffs, &g_t_coeffs)?;
        if res_xt.degree().unwrap_or(0) == 0 {
            continue;
        }
        let leading = s.coeff(1);
        if leading.is_zero() {
            return None;
        }
        let coeff = -s.coeff(0) / leading;
        terms.push(Expr::Mul(
            Expr::Constant(coeff).boxed(),
            log_abs(res_xt.to_expr(var)).boxed(),
        ));
    }

    Some(simplify(sum_exprs(terms)))
}

fn coeffs_a_minus_t_bprime(a: &Poly, b_prime: &Poly) -> Vec<Poly> {
    let a_coeffs = poly_coeffs_rational(a);
    let b_coeffs = poly_coeffs_rational(b_prime);
    let max_len = a_coeffs.len().max(b_coeffs.len());
    let mut coeffs = Vec::with_capacity(max_len);
    for idx in 0..max_len {
        let a_coeff = a_coeffs.get(idx).cloned().unwrap_or_else(Rational::zero);
        let b_coeff = b_coeffs.get(idx).cloned().unwrap_or_else(Rational::zero);
        coeffs.push(poly_linear_t(a_coeff, -b_coeff));
    }
    trim_poly_coeffs(&mut coeffs);
    coeffs
}

fn poly_coeffs_rational(poly: &Poly) -> Vec<Rational> {
    if poly.is_zero() {
        return Vec::new();
    }
    let degree = poly.degree().unwrap_or(0);
    let mut coeffs = vec![Rational::zero(); degree + 1];
    for (exp, coeff) in poly.coeff_entries() {
        coeffs[exp] = coeff;
    }
    coeffs
}

fn poly_coeffs_const(poly: &Poly) -> Vec<Poly> {
    if poly.is_zero() {
        return Vec::new();
    }
    let degree = poly.degree().unwrap_or(0);
    let mut coeffs = vec![Poly::zero(); degree + 1];
    for (exp, coeff) in poly.coeff_entries() {
        coeffs[exp] = Poly::from_constant(coeff);
    }
    coeffs
}

fn poly_linear_t(constant: Rational, t_coeff: Rational) -> Poly {
    let mut coeffs = BTreeMap::new();
    if !constant.is_zero() {
        coeffs.insert(0, constant);
    }
    if !t_coeff.is_zero() {
        coeffs.insert(1, t_coeff);
    }
    Poly { coeffs }
}

fn poly_monomial(coeff: Rational, exp: usize) -> Poly {
    if coeff.is_zero() {
        return Poly::zero();
    }
    let mut coeffs = BTreeMap::new();
    coeffs.insert(exp, coeff);
    Poly { coeffs }
}

fn trim_poly_coeffs(coeffs: &mut Vec<Poly>) {
    while coeffs.last().map(|c| c.is_zero()).unwrap_or(false) {
        coeffs.pop();
    }
}

fn resultant_from_coeffs(f_coeffs: &[Poly], g_coeffs: &[Poly]) -> Option<Poly> {
    let mut f = f_coeffs.to_vec();
    let mut g = g_coeffs.to_vec();
    trim_poly_coeffs(&mut f);
    trim_poly_coeffs(&mut g);
    if f.is_empty() || g.is_empty() {
        return Some(Poly::zero());
    }

    let f_deg = f.len() - 1;
    let g_deg = g.len() - 1;
    if f_deg == 0 {
        return Some(f[0].pow(g_deg));
    }
    if g_deg == 0 {
        return Some(g[0].pow(f_deg));
    }

    let f_desc: Vec<Poly> = f.iter().rev().cloned().collect();
    let g_desc: Vec<Poly> = g.iter().rev().cloned().collect();
    let size = f_deg + g_deg;
    let mut matrix = vec![vec![Poly::zero(); size]; size];

    for row in 0..g_deg {
        for (col, coeff) in f_desc.iter().enumerate() {
            matrix[row][row + col] = coeff.clone();
        }
    }
    for row in 0..f_deg {
        for (col, coeff) in g_desc.iter().enumerate() {
            matrix[g_deg + row][row + col] = coeff.clone();
        }
    }

    det_bareiss(matrix)
}

fn det_bareiss(mut matrix: Vec<Vec<Poly>>) -> Option<Poly> {
    let n = matrix.len();
    if n == 0 {
        return Some(Poly::one());
    }

    let mut denom = Poly::one();
    for k in 0..(n - 1) {
        let mut pivot_row = None;
        let mut pivot_col = None;
        'search: for i in k..n {
            for j in k..n {
                if !matrix[i][j].is_zero() {
                    pivot_row = Some(i);
                    pivot_col = Some(j);
                    break 'search;
                }
            }
        }

        let (pivot_row, pivot_col) = match (pivot_row, pivot_col) {
            (Some(r), Some(c)) => (r, c),
            _ => return Some(Poly::zero()),
        };

        if pivot_row != k {
            matrix.swap(k, pivot_row);
        }
        if pivot_col != k {
            for row in matrix.iter_mut() {
                row.swap(k, pivot_col);
            }
        }

        let pivot = matrix[k][k].clone();
        if pivot.is_zero() {
            return Some(Poly::zero());
        }

        for i in (k + 1)..n {
            for j in (k + 1)..n {
                let term =
                    matrix[i][j].clone() * pivot.clone()
                        - matrix[i][k].clone() * matrix[k][j].clone();
                if k == 0 {
                    matrix[i][j] = term;
                } else {
                    if denom.is_zero() {
                        return None;
                    }
                    matrix[i][j] = term.div_exact(&denom)?;
                }
            }
        }

        for i in (k + 1)..n {
            matrix[i][k] = Poly::zero();
            matrix[k][i] = Poly::zero();
        }

        denom = pivot;
    }

    Some(matrix[n - 1][n - 1].clone())
}

fn mod_poly_add(a: &Poly, b: &Poly, modulus: &Poly) -> Poly {
    poly_mod(&(a.clone() + b.clone()), modulus)
}

fn mod_poly_sub(a: &Poly, b: &Poly, modulus: &Poly) -> Poly {
    poly_mod(&(a.clone() - b.clone()), modulus)
}

fn mod_poly_mul(a: &Poly, b: &Poly, modulus: &Poly) -> Poly {
    poly_mod(&(a.clone() * b.clone()), modulus)
}

fn mod_poly_inv(value: &Poly, modulus: &Poly) -> Option<Poly> {
    if value.is_zero() {
        return None;
    }
    let reduced = poly_mod(value, modulus);
    if reduced.is_zero() {
        return None;
    }
    poly_mod_inverse(&reduced, modulus)
}

fn poly_x_gcd_mod(a: &[Poly], b: &[Poly], modulus: &Poly) -> Option<Vec<Poly>> {
    let mut r0 = a.iter().map(|c| poly_mod(c, modulus)).collect::<Vec<_>>();
    let mut r1 = b.iter().map(|c| poly_mod(c, modulus)).collect::<Vec<_>>();
    trim_poly_coeffs(&mut r0);
    trim_poly_coeffs(&mut r1);

    while !r1.is_empty() {
        let (_, r) = poly_x_div_rem_mod(&r0, &r1, modulus)?;
        r0 = r1;
        r1 = r;
    }

    if r0.is_empty() {
        return Some(Vec::new());
    }
    let lc = r0.last().cloned().unwrap_or_else(Poly::zero);
    if lc.is_zero() {
        return Some(Vec::new());
    }
    let inv_lc = mod_poly_inv(&lc, modulus)?;
    for coeff in r0.iter_mut() {
        *coeff = mod_poly_mul(coeff, &inv_lc, modulus);
    }
    trim_poly_coeffs(&mut r0);
    Some(r0)
}

fn poly_x_div_rem_mod(
    dividend: &[Poly],
    divisor: &[Poly],
    modulus: &Poly,
) -> Option<(Vec<Poly>, Vec<Poly>)> {
    let mut remainder = dividend.to_vec();
    let mut divisor = divisor.to_vec();
    trim_poly_coeffs(&mut remainder);
    trim_poly_coeffs(&mut divisor);
    if divisor.is_empty() {
        return None;
    }

    let divisor_deg = divisor.len() - 1;
    let divisor_lc = divisor[divisor_deg].clone();
    let inv_lc = mod_poly_inv(&divisor_lc, modulus)?;
    let mut quotient = if remainder.len() > divisor_deg {
        vec![Poly::zero(); remainder.len() - divisor_deg]
    } else {
        Vec::new()
    };

    while !remainder.is_empty() && remainder.len() - 1 >= divisor_deg {
        let power = remainder.len() - 1 - divisor_deg;
        let lead = remainder.last().cloned().unwrap_or_else(Poly::zero);
        let coeff = mod_poly_mul(&lead, &inv_lc, modulus);
        if power < quotient.len() {
            quotient[power] = mod_poly_add(&quotient[power], &coeff, modulus);
        }

        for i in 0..=divisor_deg {
            let idx = power + i;
            let prod = mod_poly_mul(&coeff, &divisor[i], modulus);
            remainder[idx] = mod_poly_sub(&remainder[idx], &prod, modulus);
        }
        trim_poly_coeffs(&mut remainder);
    }

    trim_poly_coeffs(&mut quotient);
    Some((quotient, remainder))
}

fn transpose_coeffs_x_t(coeffs_x: &[Poly]) -> Vec<Poly> {
    let mut max_deg = 0;
    for coeff in coeffs_x {
        if let Some(deg) = coeff.degree() {
            max_deg = max_deg.max(deg);
        }
    }
    if coeffs_x.is_empty() {
        return Vec::new();
    }

    let mut coeffs_t = vec![Poly::zero(); max_deg + 1];
    for (x_exp, coeff_t) in coeffs_x.iter().enumerate() {
        for (t_exp, t_coeff) in coeff_t.coeff_entries() {
            if t_coeff.is_zero() {
                continue;
            }
            let term = poly_monomial(t_coeff, x_exp);
            coeffs_t[t_exp] = coeffs_t[t_exp].clone() + term;
        }
    }
    trim_poly_coeffs(&mut coeffs_t);
    coeffs_t
}

fn as_division(expr: &Expr) -> Option<(Expr, Expr)> {
    match expr {
        Expr::Div(a, b) => Some(((*a.clone()), (*b.clone()))),
        _ => {
            let (const_factor, factors) = flatten_product(expr);
            if const_factor.is_zero() {
                return Some((
                    Expr::Constant(Rational::zero()),
                    Expr::Constant(Rational::one()),
                ));
            }
            let mut numerator: Vec<Expr> = Vec::new();
            let mut denominator: Vec<Expr> = Vec::new();
            for f in factors {
                match f {
                    Expr::Pow(base, exp) => {
                        if let Expr::Constant(ref k) = *exp {
                            if k.is_negative() {
                                let flipped = Expr::Pow(
                                    base.clone(),
                                    Expr::Constant(-k.clone()).boxed(),
                                );
                                denominator.push(flipped);
                                continue;
                            }
                        }
                        numerator.push(Expr::Pow(base.clone(), exp.clone()));
                    }
                    other => numerator.push(other),
                }
            }
            let num_expr = rebuild_product(const_factor.clone(), numerator);
            let den_expr = if denominator.is_empty() {
                Expr::Constant(Rational::one())
            } else {
                rebuild_product(Rational::one(), denominator)
            };
            Some((num_expr, den_expr))
        }
    }
}

fn basis_for_system(
    denominator: &Poly,
    factorization: &Factorization,
    var: &str,
) -> Option<Vec<Poly>> {
    let mut basis = Vec::new();
    let x_poly = Poly::from_expr(&Expr::Variable(var.to_string()), var)?;

    for factor in &factorization.factors {
        let degree = factor.poly.degree()?;
        for power in 1..=factor.multiplicity {
            let divisor = factor.poly.pow(power);
            let term = denominator.div_exact(&divisor)?;
            match degree {
                1 => basis.push(term),
                2 => {
                    basis.push(term.clone() * x_poly.clone());
                    basis.push(term);
                }
                _ => return None,
            }
        }
    }

    Some(basis)
}

fn integrate_linear_term(coeff: Rational, factor: &Poly, power: usize, var: &str) -> Option<Expr> {
    if coeff.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }
    let leading = factor.coeff(1);
    if leading.is_zero() {
        return None;
    }
    let base = factor.to_expr(var);
    let base_monic = Expr::Add(
        Expr::Variable(var.to_string()).boxed(),
        Expr::Constant(factor.coeff(0) / leading.clone()).boxed(),
    );
    if power == 1 {
        return Some(Expr::Mul(
            Expr::Constant(coeff / leading.clone()).boxed(),
            log_abs(base_monic).boxed(),
        ));
    }

    let exponent = Rational::from_integer(BigInt::from(1_i64 - power as i64));
    let pow = Expr::Pow(base.boxed(), Expr::Constant(exponent.clone()).boxed());
    let scale = coeff
        / (leading * Rational::from_integer(BigInt::from(1_i64 - power as i64)));
    Some(Expr::Mul(Expr::Constant(scale).boxed(), pow.boxed()))
}

fn integrate_quadratic_term(
    coeff_x: Rational,
    coeff_const: Rational,
    factor: &Poly,
    power: usize,
    var: &str,
) -> Option<Expr> {
    if coeff_x.is_zero() && coeff_const.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let a = factor.coeff(2);
    if a.is_zero() {
        return None;
    }
    let b = factor.coeff(1);
    let two = Rational::from_integer(2.into());
    let alpha = coeff_x.clone() / (two.clone() * a.clone());
    let beta = coeff_const.clone() - alpha.clone() * b.clone();

    let q_expr = factor.to_expr(var);
    let mut parts: Vec<Expr> = Vec::new();

    if !alpha.is_zero() {
        if power == 1 {
            parts.push(Expr::Mul(
                Expr::Constant(alpha.clone()).boxed(),
                log_abs(q_expr.clone()).boxed(),
            ));
        } else {
            let exponent = Rational::from_integer(BigInt::from(1_i64 - power as i64));
            let pow = Expr::Pow(q_expr.clone().boxed(), Expr::Constant(exponent.clone()).boxed());
            let scale = alpha
                / Rational::from_integer(BigInt::from(1_i64 - power as i64));
            parts.push(Expr::Mul(Expr::Constant(scale).boxed(), pow.boxed()));
        }
    }

    if !beta.is_zero() {
        let inv = integrate_quadratic_inverse(factor, power, var)?;
        parts.push(Expr::Mul(
            Expr::Constant(beta).boxed(),
            inv.boxed(),
        ));
    }

    Some(simplify(sum_exprs(parts)))
}

fn integrate_quadratic_inverse(factor: &Poly, power: usize, var: &str) -> Option<Expr> {
    if power == 0 {
        return None;
    }

    let a = factor.coeff(2);
    if a.is_zero() {
        return None;
    }
    let b = factor.coeff(1);
    let c = factor.coeff(0);

    let four = Rational::from_integer(4.into());
    let delta = four * a.clone() * c.clone() - b.clone() * b.clone();
    if delta.is_zero() {
        return None;
    }

    let q_expr = factor.to_expr(var);
    let deriv_expr = factor.derivative().to_expr(var);

    if power == 1 {
        if delta.is_positive() {
            let sqrt_delta = Expr::Pow(
                Expr::Constant(delta.clone()).boxed(),
                Expr::Constant(Rational::new(1.into(), 2.into())).boxed(),
            );
            let leading = Expr::Div(
                Expr::Constant(Rational::from_integer(2.into())).boxed(),
                sqrt_delta.clone().boxed(),
            );
            let atan_arg = Expr::Div(deriv_expr.boxed(), sqrt_delta.clone().boxed());
            let atan_expr = Expr::Atan(atan_arg.boxed());
            return Some(Expr::Mul(leading.boxed(), atan_expr.boxed()));
        }

        let disc = -delta.clone();
        let sqrt_disc = Expr::Pow(
            Expr::Constant(disc.clone()).boxed(),
            Expr::Constant(Rational::new(1.into(), 2.into())).boxed(),
        );
        let ratio = Expr::Div(
            Expr::Sub(deriv_expr.clone().boxed(), sqrt_disc.clone().boxed()).boxed(),
            Expr::Add(deriv_expr.boxed(), sqrt_disc.clone().boxed()).boxed(),
        );
        let leading = Expr::Div(
            Expr::Constant(Rational::one()).boxed(),
            sqrt_disc.clone().boxed(),
        );
        return Some(Expr::Mul(leading.boxed(), log_abs(ratio).boxed()));
    }

    let k_minus_one = Rational::from_integer(BigInt::from(power as i64 - 1));
    let denom_coeff = k_minus_one.clone() * delta.clone();
    let q_power = Expr::Pow(
        q_expr.clone().boxed(),
        Expr::Constant(Rational::from_integer(BigInt::from(power as i64 - 1))).boxed(),
    );
    let first_term = Expr::Div(
        deriv_expr.boxed(),
        Expr::Mul(Expr::Constant(denom_coeff.clone()).boxed(), q_power.boxed()).boxed(),
    );

    let two = Rational::from_integer(2.into());
    let recur_coeff = (two.clone() * a.clone())
        * Rational::from_integer(BigInt::from(2 * power as i64 - 3))
        / denom_coeff;
    let previous = integrate_quadratic_inverse(factor, power - 1, var)?;
    let scaled_prev = Expr::Mul(Expr::Constant(recur_coeff).boxed(), previous.boxed());

    Some(simplify(Expr::Add(first_term.boxed(), scaled_prev.boxed())))
}

fn solve_linear_system(mut matrix: Vec<Vec<Rational>>) -> Option<Vec<Rational>> {
    if matrix.is_empty() {
        return None;
    }
    let rows = matrix.len();
    let cols = matrix[0].len() - 1;

    let mut row = 0;
    for col in 0..cols {
        let mut pivot = row;
        while pivot < rows && matrix[pivot][col].is_zero() {
            pivot += 1;
        }
        if pivot == rows {
            continue;
        }
        matrix.swap(row, pivot);
        let pivot_val = matrix[row][col].clone();
        for c in col..=cols {
            matrix[row][c] /= pivot_val.clone();
        }
        for r in 0..rows {
            if r == row {
                continue;
            }
            let factor = matrix[r][col].clone();
            if factor.is_zero() {
                continue;
            }
            for c in col..=cols {
                let value = matrix[r][c].clone() - factor.clone() * matrix[row][c].clone();
                matrix[r][c] = value;
            }
        }
        row += 1;
        if row == rows {
            break;
        }
    }

    let mut solution = vec![Rational::zero(); cols];
    for i in 0..cols.min(rows) {
        solution[i] = matrix[i][cols].clone();
    }
    Some(solution)
}

fn sum_exprs(exprs: Vec<Expr>) -> Expr {
    let filtered: Vec<Expr> = exprs
        .into_iter()
        .filter(|e| !matches!(e, Expr::Constant(c) if c.is_zero()))
        .collect();

    if filtered.is_empty() {
        return Expr::Constant(Rational::zero());
    }

    filtered
        .into_iter()
        .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
        .unwrap()
}

#[derive(Clone, Debug)]
struct QuadExt {
    a: Rational,
    b: Rational,
    d: Rational,
}

impl QuadExt {
    fn new(a: Rational, b: Rational, d: Rational) -> Self {
        Self { a, b, d }
    }

    fn zero(d: &Rational) -> Self {
        Self {
            a: Rational::zero(),
            b: Rational::zero(),
            d: d.clone(),
        }
    }

    fn one(d: &Rational) -> Self {
        Self {
            a: Rational::one(),
            b: Rational::zero(),
            d: d.clone(),
        }
    }

    fn from_rational(value: Rational, d: &Rational) -> Self {
        Self {
            a: value,
            b: Rational::zero(),
            d: d.clone(),
        }
    }

    fn is_zero(&self) -> bool {
        self.a.is_zero() && self.b.is_zero()
    }

    fn inv(&self) -> Option<Self> {
        let denom = self.a.clone() * self.a.clone() - self.b.clone() * self.b.clone() * self.d.clone();
        if denom.is_zero() {
            return None;
        }
        let scale = Rational::one() / denom;
        Some(Self {
            a: self.a.clone() * scale.clone(),
            b: -self.b.clone() * scale,
            d: self.d.clone(),
        })
    }

    fn to_expr(&self) -> Expr {
        if self.b.is_zero() {
            return Expr::Constant(self.a.clone());
        }
        let sqrt_d = sqrt_rational_expr(&self.d);
        let coeff_b = Expr::Constant(self.b.clone());
        let b_term = Expr::Mul(coeff_b.boxed(), sqrt_d.boxed());
        if self.a.is_zero() {
            return b_term;
        }
        Expr::Add(Expr::Constant(self.a.clone()).boxed(), b_term.boxed())
    }
}

impl std::ops::Neg for QuadExt {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            a: -self.a,
            b: -self.b,
            d: self.d,
        }
    }
}

impl std::ops::Add for QuadExt {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        debug_assert_eq!(self.d, other.d);
        Self {
            a: self.a + other.a,
            b: self.b + other.b,
            d: self.d,
        }
    }
}

impl std::ops::Sub for QuadExt {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        debug_assert_eq!(self.d, other.d);
        Self {
            a: self.a - other.a,
            b: self.b - other.b,
            d: self.d,
        }
    }
}

impl std::ops::Mul for QuadExt {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        debug_assert_eq!(self.d, other.d);
        let a = self.a.clone() * other.a.clone() + self.b.clone() * other.b.clone() * self.d.clone();
        let b = self.a * other.b + self.b * other.a;
        Self { a, b, d: self.d }
    }
}

impl std::ops::Div for QuadExt {
    type Output = Self;

    fn div(self, other: Self) -> Self::Output {
        let inv = other.inv().expect("division by zero in QuadExt");
        self * inv
    }
}

#[derive(Clone, Debug)]
struct QuadPoly {
    coeffs: Vec<QuadExt>,
}

impl QuadPoly {
    fn from_coeffs(mut coeffs: Vec<QuadExt>) -> Self {
        while coeffs.last().map(|c| c.is_zero()).unwrap_or(false) {
            coeffs.pop();
        }
        Self { coeffs }
    }

    fn coeff(&self, exp: usize, d: &Rational) -> QuadExt {
        self.coeffs.get(exp).cloned().unwrap_or_else(|| QuadExt::zero(d))
    }

    fn mul(&self, other: &Self, d: &Rational) -> Self {
        if self.coeffs.is_empty() || other.coeffs.is_empty() {
            return Self { coeffs: Vec::new() };
        }
        let mut coeffs = vec![QuadExt::zero(d); self.coeffs.len() + other.coeffs.len() - 1];
        for (i, a) in self.coeffs.iter().enumerate() {
            for (j, b) in other.coeffs.iter().enumerate() {
                let idx = i + j;
                coeffs[idx] = coeffs[idx].clone() + a.clone() * b.clone();
            }
        }
        Self::from_coeffs(coeffs)
    }

    fn to_expr(&self, var: &str, _d: &Rational) -> Expr {
        if self.coeffs.is_empty() {
            return Expr::Constant(Rational::zero());
        }
        let x = Expr::Variable(var.to_string());
        let mut terms = Vec::new();
        for (exp, coeff) in self.coeffs.iter().enumerate() {
            if coeff.is_zero() {
                continue;
            }
            let base = match exp {
                0 => Expr::Constant(Rational::one()),
                1 => x.clone(),
                _ => Expr::Pow(x.clone().boxed(), Expr::integer(exp as i64).boxed()),
            };
            terms.push(Expr::Mul(coeff.to_expr().boxed(), base.boxed()));
        }
        sum_exprs(terms)
    }
}

fn sqrt_rational_expr(value: &Rational) -> Expr {
    Expr::Pow(
        Expr::Constant(value.clone()).boxed(),
        Expr::Constant(Rational::new(1.into(), 2.into())).boxed(),
    )
}

fn quad_poly_from_rational(poly: &Poly, d: &Rational) -> QuadPoly {
    if poly.is_zero() {
        return QuadPoly { coeffs: Vec::new() };
    }
    let degree = poly.degree().unwrap_or(0);
    let mut coeffs = vec![QuadExt::zero(d); degree + 1];
    for (exp, coeff) in poly.coeff_entries() {
        coeffs[exp] = QuadExt::from_rational(coeff, d);
    }
    QuadPoly::from_coeffs(coeffs)
}

fn solve_linear_system_quad(mut matrix: Vec<Vec<QuadExt>>, d: &Rational) -> Option<Vec<QuadExt>> {
    if matrix.is_empty() {
        return None;
    }
    let rows = matrix.len();
    let cols = matrix[0].len() - 1;

    let mut row = 0;
    for col in 0..cols {
        let mut pivot = row;
        while pivot < rows && matrix[pivot][col].is_zero() {
            pivot += 1;
        }
        if pivot == rows {
            continue;
        }
        matrix.swap(row, pivot);
        let pivot_val = matrix[row][col].clone();
        let inv = pivot_val.inv()?;
        for c in col..=cols {
            matrix[row][c] = matrix[row][c].clone() * inv.clone();
        }
        for r in 0..rows {
            if r == row {
                continue;
            }
            let factor = matrix[r][col].clone();
            if factor.is_zero() {
                continue;
            }
            for c in col..=cols {
                let value = matrix[r][c].clone() - factor.clone() * matrix[row][c].clone();
                matrix[r][c] = value;
            }
        }
        row += 1;
        if row == rows {
            break;
        }
    }

    let mut solution = vec![QuadExt::zero(d); cols];
    for i in 0..cols.min(rows) {
        solution[i] = matrix[i][cols].clone();
    }
    Some(solution)
}

fn integrate_cyclotomic_quartic_quintic(
    numerator: &Poly,
    denominator: &Poly,
    var: &str,
) -> Option<Expr> {
    if poly_is_x4_plus_one(denominator) {
        return integrate_x4_plus_one(numerator, var);
    }
    if poly_is_x5_plus_one(denominator) {
        return integrate_x5_plus_one(numerator, var);
    }
    None
}

fn poly_is_x4_plus_one(poly: &Poly) -> bool {
    if poly.degree() != Some(4) {
        return false;
    }
    if poly.coeff(4) != Rational::one() || poly.coeff(0) != Rational::one() {
        return false;
    }
    for (exp, coeff) in poly.coeff_entries() {
        if exp != 0 && exp != 4 && !coeff.is_zero() {
            return false;
        }
    }
    true
}

fn poly_is_x5_plus_one(poly: &Poly) -> bool {
    if poly.degree() != Some(5) {
        return false;
    }
    if poly.coeff(5) != Rational::one() || poly.coeff(0) != Rational::one() {
        return false;
    }
    for (exp, coeff) in poly.coeff_entries() {
        if exp != 0 && exp != 5 && !coeff.is_zero() {
            return false;
        }
    }
    true
}

fn integrate_x4_plus_one(numerator: &Poly, var: &str) -> Option<Expr> {
    let d = Rational::from_integer(2.into());
    let sqrt = QuadExt::new(Rational::zero(), Rational::one(), d.clone());
    let one = QuadExt::one(&d);
    let minus_sqrt = QuadExt::new(Rational::zero(), -Rational::one(), d.clone());

    let q_pos = QuadPoly::from_coeffs(vec![one.clone(), sqrt.clone(), one.clone()]);
    let q_neg = QuadPoly::from_coeffs(vec![one.clone(), minus_sqrt.clone(), one.clone()]);
    let x_poly = QuadPoly::from_coeffs(vec![QuadExt::zero(&d), one.clone()]);

    let basis = vec![
        q_neg.mul(&x_poly, &d),
        q_neg.clone(),
        q_pos.mul(&x_poly, &d),
        q_pos.clone(),
    ];

    let degree = 4;
    let mut matrix = vec![vec![QuadExt::zero(&d); degree + 1]; degree];
    for (col, poly) in basis.iter().enumerate() {
        for exp in 0..degree {
            let coeff = poly.coeff(exp, &d);
            if !coeff.is_zero() {
                matrix[exp][col] = matrix[exp][col].clone() + coeff;
            }
        }
    }

    let num_quad = quad_poly_from_rational(numerator, &d);
    for exp in 0..degree {
        let coeff = num_quad.coeff(exp, &d);
        if !coeff.is_zero() {
            matrix[exp][degree] = coeff;
        }
    }

    let solution = solve_linear_system_quad(matrix, &d)?;
    if solution.len() != degree {
        return None;
    }

    let mut terms = Vec::new();
    let term = integrate_quadratic_term_quad(
        solution[0].clone(),
        solution[1].clone(),
        &q_pos,
        var,
        &d,
    )?;
    terms.push(term);
    let term = integrate_quadratic_term_quad(
        solution[2].clone(),
        solution[3].clone(),
        &q_neg,
        var,
        &d,
    )?;
    terms.push(term);

    Some(simplify(sum_exprs(terms)))
}

fn integrate_x5_plus_one(numerator: &Poly, var: &str) -> Option<Expr> {
    let d = Rational::from_integer(5.into());
    let sqrt = QuadExt::new(Rational::zero(), Rational::one(), d.clone());
    let one = QuadExt::one(&d);
    let two = QuadExt::from_rational(Rational::from_integer(2.into()), &d);

    let neg_one = QuadExt::from_rational(Rational::from_integer((-1).into()), &d);
    let a = (neg_one.clone() - sqrt.clone()) / two.clone();
    let b = (neg_one + sqrt.clone()) / two;

    let q_a = QuadPoly::from_coeffs(vec![one.clone(), a, one.clone()]);
    let q_b = QuadPoly::from_coeffs(vec![one.clone(), b, one.clone()]);
    let x_poly = QuadPoly::from_coeffs(vec![QuadExt::zero(&d), one.clone()]);
    let linear = QuadPoly::from_coeffs(vec![one.clone(), one.clone()]);

    let term_linear = q_a.mul(&q_b, &d);
    let term_q_a = linear.mul(&q_b, &d);
    let term_q_b = linear.mul(&q_a, &d);

    let basis = vec![
        term_linear,
        term_q_a.mul(&x_poly, &d),
        term_q_a,
        term_q_b.mul(&x_poly, &d),
        term_q_b,
    ];

    let degree = 5;
    let mut matrix = vec![vec![QuadExt::zero(&d); degree + 1]; degree];
    for (col, poly) in basis.iter().enumerate() {
        for exp in 0..degree {
            let coeff = poly.coeff(exp, &d);
            if !coeff.is_zero() {
                matrix[exp][col] = matrix[exp][col].clone() + coeff;
            }
        }
    }

    let num_quad = quad_poly_from_rational(numerator, &d);
    for exp in 0..degree {
        let coeff = num_quad.coeff(exp, &d);
        if !coeff.is_zero() {
            matrix[exp][degree] = coeff;
        }
    }

    let solution = solve_linear_system_quad(matrix, &d)?;
    if solution.len() != degree {
        return None;
    }

    let mut terms = Vec::new();
    let linear_expr = Expr::Add(
        Expr::Variable(var.to_string()).boxed(),
        Expr::Constant(Rational::one()).boxed(),
    );
    if !solution[0].is_zero() {
        terms.push(Expr::Mul(
            solution[0].to_expr().boxed(),
            log_abs(linear_expr).boxed(),
        ));
    }

    let term = integrate_quadratic_term_quad(
        solution[1].clone(),
        solution[2].clone(),
        &q_a,
        var,
        &d,
    )?;
    terms.push(term);
    let term = integrate_quadratic_term_quad(
        solution[3].clone(),
        solution[4].clone(),
        &q_b,
        var,
        &d,
    )?;
    terms.push(term);

    Some(simplify(sum_exprs(terms)))
}

fn integrate_quadratic_term_quad(
    coeff_x: QuadExt,
    coeff_const: QuadExt,
    factor: &QuadPoly,
    var: &str,
    d: &Rational,
) -> Option<Expr> {
    if coeff_x.is_zero() && coeff_const.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let a = factor.coeff(2, d);
    if a.is_zero() {
        return None;
    }
    let b = factor.coeff(1, d);
    let c = factor.coeff(0, d);
    let two = QuadExt::from_rational(Rational::from_integer(2.into()), d);
    let alpha = coeff_x.clone() / (two.clone() * a.clone());
    let beta = coeff_const - alpha.clone() * b.clone();

    let q_expr = factor.to_expr(var, d);
    let mut parts: Vec<Expr> = Vec::new();

    if !alpha.is_zero() {
        parts.push(Expr::Mul(alpha.to_expr().boxed(), log_abs(q_expr.clone()).boxed()));
    }

    if !beta.is_zero() {
        let four = QuadExt::from_rational(Rational::from_integer(4.into()), d);
        let delta = four * a.clone() * c - b.clone() * b.clone();
        let sqrt_delta = Expr::Pow(
            delta.to_expr().boxed(),
            Expr::Constant(Rational::new(1.into(), 2.into())).boxed(),
        );
        let leading = Expr::Div(
            Expr::Constant(Rational::from_integer(2.into())).boxed(),
            sqrt_delta.clone().boxed(),
        );
        let deriv_expr = Expr::Add(
            Expr::Mul((two * a).to_expr().boxed(), Expr::Variable(var.to_string()).boxed()).boxed(),
            b.to_expr().boxed(),
        );
        let atan_arg = Expr::Div(deriv_expr.boxed(), sqrt_delta.boxed());
        let atan_expr = Expr::Atan(atan_arg.boxed());
        parts.push(Expr::Mul(
            beta.to_expr().boxed(),
            Expr::Mul(leading.boxed(), atan_expr.boxed()).boxed(),
        ));
    }

    Some(simplify(sum_exprs(parts)))
}
