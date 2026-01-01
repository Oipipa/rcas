use crate::expr::{Expr, Rational};
use crate::factor::{factor_polynomial, Factorization, Poly};
use crate::simplify::simplify;
use super::{flatten_product, log_abs, rebuild_product};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

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
        let factorization = factor_polynomial(&den_term.to_expr(var), var)?;
        if factorization.constant.is_zero() {
            return None;
        }

        if !factorization
            .factors
            .iter()
            .all(|f| matches!(f.poly.degree(), Some(1 | 2)))
        {
            return None;
        }

        let scaled_num = num_term.scale(&(Rational::one() / factorization.constant.clone()));
        let denominator = build_denominator(&factorization);
        let pf = integrate_partial_fraction(&scaled_num, &denominator, &factorization, var)?;
        pieces.push(pf);
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
