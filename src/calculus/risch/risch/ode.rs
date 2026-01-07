use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{One, Zero};

use crate::calculus::risch::diff_field::Tower;
use crate::core::expr::{Expr, Rational};
use crate::core::polynomial::Poly;
use crate::simplify::simplify_fully;

use super::expr_poly::expr_to_rational_polys_rational;
use super::integrate::integrate_in_tower_simple;
use super::tower::is_constant_in_tower;

pub(super) fn solve_risch_linear_ode(
    coeff: &Expr,
    exp: i64,
    a_expr: &Expr,
    var: &str,
    base_tower: &Tower,
) -> Option<Expr> {
    if exp == 0 {
        return integrate_in_tower_simple(coeff, var, base_tower);
    }
    let factor = Expr::Constant(Rational::from_integer(BigInt::from(exp)));
    let scaled_a = simplify_fully(Expr::Mul(factor.boxed(), a_expr.clone().boxed()));
    solve_linear_ode_in_base(&scaled_a, coeff, var, base_tower)
}

fn solve_linear_ode_in_base(
    a_expr: &Expr,
    b_expr: &Expr,
    var: &str,
    base_tower: &Tower,
) -> Option<Expr> {
    let a_simplified = simplify_fully(a_expr.clone());
    if a_simplified.is_zero() {
        return integrate_in_tower_simple(b_expr, var, base_tower);
    }

    if let Some(true) = is_constant_in_tower(&a_simplified, base_tower) {
        if let Some(true) = is_constant_in_tower(b_expr, base_tower) {
            return Some(simplify_fully(Expr::Div(
                b_expr.clone().boxed(),
                a_simplified.boxed(),
            )));
        }
    }

    if base_tower.extensions().is_empty() {
        return solve_linear_rational_ode_rational(&a_simplified, b_expr, var);
    }

    None
}

fn solve_linear_rational_ode_rational(a_expr: &Expr, b_expr: &Expr, var: &str) -> Option<Expr> {
    let (a_num, a_den) = expr_to_rational_polys_rational(a_expr, var)?;
    let (b_num, b_den) = expr_to_rational_polys_rational(b_expr, var)?;
    if a_den.is_zero() || b_den.is_zero() {
        return None;
    }

    let gcd = Poly::gcd(&a_den, &b_den);
    let denom = if gcd.is_one() {
        a_den.clone() * b_den.clone()
    } else {
        let prod = a_den.clone() * b_den.clone();
        prod.div_exact(&gcd)?
    };

    let scale_a = denom.div_exact(&a_den)?;
    let scale_b = denom.div_exact(&b_den)?;
    let a_scaled = a_num * scale_a;
    let b_scaled = b_num * scale_b;
    let denom_deriv = denom.derivative();
    let k = a_scaled - denom_deriv;
    let rhs = b_scaled * denom.clone();

    let rhs_deg = rhs.degree().unwrap_or(0);
    let denom_deg = denom.degree().unwrap_or(0);
    let bound = rhs_deg + denom_deg + 1;

    let mut basis = Vec::new();
    let mut max_lhs_deg = 0;
    for exp in 0..=bound {
        let mono = poly_monomial(Rational::one(), exp);
        let lhs = mono.derivative() * denom.clone() + mono.clone() * k.clone();
        max_lhs_deg = max_lhs_deg.max(lhs.degree().unwrap_or(0));
        basis.push(lhs);
    }

    let rows = max_lhs_deg.max(rhs.degree().unwrap_or(0)) + 1;
    let cols = bound + 1;
    let mut matrix = vec![vec![Rational::zero(); cols + 1]; rows];

    for (col, poly) in basis.iter().enumerate() {
        for (exp, coeff) in poly.coeff_entries() {
            if exp < rows {
                matrix[exp][col] = coeff;
            }
        }
    }
    for (exp, coeff) in rhs.coeff_entries() {
        if exp < rows {
            matrix[exp][cols] = coeff;
        }
    }

    let solution = solve_linear_system(matrix, cols)?;
    let mut coeffs = BTreeMap::new();
    for (exp, coeff) in solution.into_iter().enumerate() {
        if !coeff.is_zero() {
            coeffs.insert(exp, coeff);
        }
    }
    let numer = Poly { coeffs };
    if denom.is_one() {
        Some(numer.to_expr(var))
    } else {
        Some(Expr::Div(
            numer.to_expr(var).boxed(),
            denom.to_expr(var).boxed(),
        ))
    }
}

fn solve_linear_system(mut matrix: Vec<Vec<Rational>>, cols: usize) -> Option<Vec<Rational>> {
    let rows = matrix.len();
    let mut pivot_row = 0;
    let mut pivots = vec![None; cols];

    for col in 0..cols {
        let mut row = pivot_row;
        while row < rows && matrix[row][col].is_zero() {
            row += 1;
        }
        if row == rows {
            continue;
        }
        if row != pivot_row {
            matrix.swap(row, pivot_row);
        }
        let pivot = matrix[pivot_row][col].clone();
        if pivot.is_zero() {
            continue;
        }
        for j in col..=cols {
            matrix[pivot_row][j] = matrix[pivot_row][j].clone() / pivot.clone();
        }
        for r in 0..rows {
            if r == pivot_row {
                continue;
            }
            let factor = matrix[r][col].clone();
            if factor.is_zero() {
                continue;
            }
            for j in col..=cols {
                matrix[r][j] = matrix[r][j].clone() - factor.clone() * matrix[pivot_row][j].clone();
            }
        }
        pivots[col] = Some(pivot_row);
        pivot_row += 1;
        if pivot_row == rows {
            break;
        }
    }

    for r in 0..rows {
        let mut all_zero = true;
        for c in 0..cols {
            if !matrix[r][c].is_zero() {
                all_zero = false;
                break;
            }
        }
        if all_zero && !matrix[r][cols].is_zero() {
            return None;
        }
    }

    let mut solution = vec![Rational::zero(); cols];
    for col in (0..cols).rev() {
        if let Some(r) = pivots[col] {
            let mut value = matrix[r][cols].clone();
            for c in col + 1..cols {
                if !matrix[r][c].is_zero() {
                    value -= matrix[r][c].clone() * solution[c].clone();
                }
            }
            solution[col] = value;
        }
    }

    Some(solution)
}

fn poly_monomial(coeff: Rational, exp: usize) -> Poly {
    if coeff.is_zero() {
        return Poly::zero();
    }
    let mut coeffs = BTreeMap::new();
    coeffs.insert(exp, coeff);
    Poly { coeffs }
}
