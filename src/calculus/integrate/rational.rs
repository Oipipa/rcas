use crate::expr::{Expr, Rational};
use crate::factor::{Poly, factor_polynomial};
use crate::simplify::simplify;
use num_bigint::BigInt;
use num_traits::{One, Zero};

pub fn is_rational(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Div(num, den) => {
            let num_poly = Poly::from_expr(num, var);
            let den_poly = Poly::from_expr(den, var);
            match (num_poly, den_poly) {
                (Some(_), Some(d)) => d.degree() == Some(1),
                _ => false,
            }
        }
        _ => false,
    }
}

pub fn integrate(expr: &Expr, var: &str) -> Option<Expr> {
    let (num, den) = match expr {
        Expr::Div(a, b) => (a, b),
        _ => return None,
    };

    let num_poly = Poly::from_expr(num, var)?;
    let den_poly = Poly::from_expr(den, var)?;
    if den_poly.is_zero() {
        return None;
    }

    let (quotient, remainder) = num_poly.div_rem(&den_poly);
    let mut pieces: Vec<Expr> = Vec::new();
    if !quotient.is_zero() {
        let q_expr = quotient.to_expr(var);
        if let Some(poly_int) = super::polynomial::integrate(&q_expr, var) {
            pieces.push(poly_int);
        } else {
            return None;
        }
    }

    if remainder.is_zero() {
        return Some(simplify(sum_exprs(pieces)));
    }

    let factorization = factor_polynomial(den, var)?;
    if factorization.constant.is_zero() {
        return None;
    }
    if !factorization
        .factors
        .iter()
        .all(|f| f.poly.degree() == Some(1))
    {
        return None;
    }

    let pf = integrate_partial_fraction(&remainder, &den_poly, &factorization, var)?;
    pieces.push(pf);
    Some(simplify(sum_exprs(pieces)))
}

fn integrate_partial_fraction(
    remainder: &Poly,
    denominator: &Poly,
    factorization: &crate::factor::Factorization,
    var: &str,
) -> Option<Expr> {
    let unknowns: usize = factorization.factors.iter().map(|f| f.multiplicity).sum();
    if unknowns == 0 {
        return None;
    }

    let mut basis: Vec<Poly> = Vec::new();
    for factor in &factorization.factors {
        let mut divisor = Poly::one();
        for _ in 0..factor.multiplicity {
            divisor = divisor * factor.poly.clone();
            let (term, rem) = denominator.div_rem(&divisor);
            if !rem.is_zero() {
                return None;
            }
            basis.push(term);
        }
    }

    let degree = denominator.degree().unwrap_or(0);
    if degree == 0 {
        return None;
    }
    let mut matrix: Vec<Vec<Rational>> = vec![vec![Rational::zero(); unknowns + 1]; degree];

    for (col, poly) in basis.iter().enumerate() {
        for (exp, coeff) in poly.coeffs.iter() {
            if *exp < degree {
                matrix[*exp][col] += coeff.clone();
            }
        }
    }

    for (exp, coeff) in remainder.coeffs.iter() {
        if *exp < degree {
            matrix[*exp][unknowns] = coeff.clone();
        }
    }

    let solution = solve_linear_system(matrix)?;
    let mut terms: Vec<Expr> = Vec::new();
    let mut idx = 0;
    for factor in &factorization.factors {
        let root = factor.poly.linear_root()?;
        let base = Expr::Sub(
            Expr::Variable(var.to_string()).boxed(),
            Expr::Constant(root.clone()).boxed(),
        );
        for k in 1..=factor.multiplicity {
            let coeff = solution.get(idx)?.clone();
            idx += 1;
            if coeff.is_zero() {
                continue;
            }
            if k == 1 {
                terms.push(Expr::Mul(
                    Expr::Constant(coeff).boxed(),
                    Expr::Log(base.clone().boxed()).boxed(),
                ));
            } else {
                let exponent = Rational::from_integer(BigInt::from(1 - k as i64));
                let pow = Expr::Pow(
                    base.clone().boxed(),
                    Expr::Constant(exponent.clone()).boxed(),
                );
                let scale =
                    Rational::one() / Rational::from_integer(BigInt::from(1_i64 - k as i64));
                let combined = coeff * scale;
                terms.push(Expr::Mul(Expr::Constant(combined).boxed(), pow.boxed()));
            }
        }
    }

    Some(simplify(sum_exprs(terms)))
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
    for i in 0..cols {
        solution[i] = matrix[i][cols].clone();
    }
    Some(solution)
}

fn sum_exprs(exprs: Vec<Expr>) -> Expr {
    if exprs.is_empty() {
        return Expr::Constant(Rational::zero());
    }
    exprs
        .into_iter()
        .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
        .unwrap()
}
