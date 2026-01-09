use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{One, Zero};

use crate::calculus::risch::diff_field::{Tower, poly_derivative};
use crate::core::expr::{Expr, Rational};
use crate::core::polynomial::Poly;
use crate::simplify::{normalize, simplify_fully};

use super::expr_poly::{
    expr_poly_div_exact, expr_poly_div_rem, expr_poly_gcd, expr_poly_is_one, expr_poly_is_zero,
    expr_poly_to_expr, expr_to_rational_polys, expr_to_rational_polys_rational, simplify_expr_poly,
};
use super::integrate::integrate_in_tower_simple;
use super::tower::{derivative_in_tower, is_constant_in_tower, tower_prefix};
use super::ExprPoly;

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

    solve_linear_rational_ode_in_tower(&a_simplified, b_expr, base_tower)
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

pub(super) fn solve_linear_rational_ode_in_tower(
    a_expr: &Expr,
    b_expr: &Expr,
    base_tower: &Tower,
) -> Option<Expr> {
    let t_symbol = base_tower.top_symbol();
    let (a_num, a_den) = expr_to_rational_polys(a_expr, t_symbol)?;
    let (b_num, b_den) = expr_to_rational_polys(b_expr, t_symbol)?;
    if expr_poly_is_zero(&a_den) || expr_poly_is_zero(&b_den) {
        return None;
    }

    let (a_num, a_den) = normalize_constant_denominator(a_num, a_den)?;
    let (b_num, b_den) = normalize_constant_denominator(b_num, b_den)?;

    if expr_poly_is_one(&a_den) && expr_poly_is_one(&b_den) && a_num.degree().unwrap_or(0) == 0 {
        let a_const = simplify_fully(a_num.coeff(0));
        if let Some(poly) = solve_linear_poly_ode(&a_const, &b_num, base_tower) {
            let numer_expr = expr_poly_to_expr(&poly, t_symbol);
            return verify_linear_ode_solution(numer_expr, a_expr, b_expr, base_tower);
        }
    }

    let denom = if let Some(gcd) = expr_poly_gcd(&a_den, &b_den) {
        if expr_poly_is_one(&gcd) {
            a_den.clone() * b_den.clone()
        } else {
            let prod = a_den.clone() * b_den.clone();
            expr_poly_div_exact(&prod, &gcd)?
        }
    } else {
        return None;
    };

    let scale_a = expr_poly_div_exact(&denom, &a_den)?;
    let scale_b = expr_poly_div_exact(&denom, &b_den)?;
    let denom = reduce_algebraic_poly(denom, base_tower);
    let a_scaled = reduce_algebraic_poly(simplify_expr_poly(a_num * scale_a), base_tower);
    let b_scaled = reduce_algebraic_poly(simplify_expr_poly(b_num * scale_b), base_tower);
    let denom_deriv = poly_derivative(&denom, base_tower).ok()?;
    let denom_deriv = reduce_algebraic_poly(denom_deriv, base_tower);
    let k = reduce_algebraic_poly(simplify_expr_poly(a_scaled - denom_deriv), base_tower);
    let rhs = reduce_algebraic_poly(simplify_expr_poly(b_scaled * denom.clone()), base_tower);

    let rhs_deg = rhs.degree().unwrap_or(0);
    let denom_deg = denom.degree().unwrap_or(0);
    let bound = rhs_deg + denom_deg + 1;

    let mut basis = Vec::new();
    let mut max_lhs_deg = 0;
    for exp in 0..=bound {
        let mono = expr_poly_monomial(Expr::Constant(Rational::one()), exp);
        let mono_deriv = poly_derivative(&mono, base_tower).ok()?;
        let lhs = simplify_expr_poly(mono_deriv * denom.clone() + mono.clone() * k.clone());
        let lhs = reduce_algebraic_poly(lhs, base_tower);
        max_lhs_deg = max_lhs_deg.max(lhs.degree().unwrap_or(0));
        basis.push(lhs);
    }

    let rows = max_lhs_deg.max(rhs.degree().unwrap_or(0)) + 1;
    let cols = bound + 1;
    let mut matrix = vec![vec![Expr::Constant(Rational::zero()); cols + 1]; rows];

    for (col, poly) in basis.iter().enumerate() {
        for (exp, coeff) in poly.coeff_entries() {
            if exp < rows {
            matrix[exp][col] = simplify_ode_expr(coeff.clone());
            }
        }
    }
    for (exp, coeff) in rhs.coeff_entries() {
        if exp < rows {
            matrix[exp][cols] = simplify_ode_expr(coeff.clone());
        }
    }

    let solution = solve_linear_system_expr(matrix, cols)?;
    let mut coeffs = BTreeMap::new();
    for (exp, coeff) in solution.into_iter().enumerate() {
        if !expr_is_zero(&coeff) {
            coeffs.insert(exp, simplify_fully(coeff));
        }
    }
    let numer = ExprPoly { coeffs };
    let numer_expr = expr_poly_to_expr(&numer, t_symbol);
    let candidate = if expr_poly_is_one(&denom) {
        numer_expr
    } else {
        let denom_expr = expr_poly_to_expr(&denom, t_symbol);
        Expr::Div(numer_expr.boxed(), denom_expr.boxed())
    };

    verify_linear_ode_solution(candidate, a_expr, b_expr, base_tower)
}

fn reduce_algebraic_poly(poly: ExprPoly, base_tower: &Tower) -> ExprPoly {
    let Some(algebraic) = base_tower
        .extensions()
        .last()
        .and_then(|ext| ext.algebraic.as_ref())
    else {
        return poly;
    };
    if expr_poly_is_zero(&algebraic.minimal_poly) {
        return poly;
    }
    expr_poly_div_rem(&poly, &algebraic.minimal_poly)
        .map(|(_, rem)| rem)
        .unwrap_or(poly)
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

fn solve_linear_system_expr(mut matrix: Vec<Vec<Expr>>, cols: usize) -> Option<Vec<Expr>> {
    let rows = matrix.len();
    let mut pivot_row = 0;
    let mut pivots = vec![None; cols];

    for col in 0..cols {
        let mut row = pivot_row;
        while row < rows && expr_is_zero(&matrix[row][col]) {
            row += 1;
        }
        if row == rows {
            continue;
        }
        if row != pivot_row {
            matrix.swap(row, pivot_row);
        }
        let pivot = simplify_ode_expr(matrix[pivot_row][col].clone());
        if pivot.is_zero() {
            continue;
        }
        for j in col..=cols {
            matrix[pivot_row][j] = simplify_ode_expr(Expr::Div(
                matrix[pivot_row][j].clone().boxed(),
                pivot.clone().boxed(),
            ));
        }
        for r in 0..rows {
            if r == pivot_row {
                continue;
            }
            let factor = simplify_ode_expr(matrix[r][col].clone());
            if factor.is_zero() {
                continue;
            }
            for j in col..=cols {
                let scaled = simplify_ode_expr(Expr::Mul(
                    factor.clone().boxed(),
                    matrix[pivot_row][j].clone().boxed(),
                ));
                matrix[r][j] =
                    simplify_ode_expr(Expr::Sub(matrix[r][j].clone().boxed(), scaled.boxed()));
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
            if !expr_is_zero(&matrix[r][c]) {
                all_zero = false;
                break;
            }
        }
        if all_zero && !expr_is_zero(&matrix[r][cols]) {
            return None;
        }
    }

    let mut solution = vec![Expr::Constant(Rational::zero()); cols];
    for col in (0..cols).rev() {
        if let Some(r) = pivots[col] {
            let mut value = matrix[r][cols].clone();
            for c in col + 1..cols {
                if !expr_is_zero(&matrix[r][c]) {
                    let term = simplify_ode_expr(Expr::Mul(
                        matrix[r][c].clone().boxed(),
                        solution[c].clone().boxed(),
                    ));
                    value = simplify_ode_expr(Expr::Sub(value.boxed(), term.boxed()));
                }
            }
            solution[col] = simplify_ode_expr(value);
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

fn expr_poly_monomial(coeff: Expr, exp: usize) -> ExprPoly {
    if expr_is_zero(&coeff) {
        return ExprPoly::zero();
    }
    let mut coeffs = BTreeMap::new();
    coeffs.insert(exp, coeff);
    ExprPoly { coeffs }
}

fn solve_linear_poly_ode(
    a_const: &Expr,
    b_poly: &ExprPoly,
    base_tower: &Tower,
) -> Option<ExprPoly> {
    let ext_len = base_tower.extensions().len();
    let Some(lower_tower) = tower_prefix(base_tower, ext_len.saturating_sub(1)) else {
        return None;
    };
    let d_t = base_tower.top_derivative_expr();
    let max_deg = b_poly.degree().unwrap_or(0);
    let mut coeffs = BTreeMap::new();
    let mut next_coeff = Expr::Constant(Rational::zero());
    let base_var = base_tower.base_var().to_string();

    for deg in (0..=max_deg).rev() {
        let b_coeff = simplify_fully(b_poly.coeff(deg));
        let factor = Expr::Constant(Rational::from_integer(BigInt::from((deg + 1) as i64)));
        let delta = simplify_ode_expr(Expr::Mul(
            d_t.clone().boxed(),
            Expr::Mul(factor.boxed(), next_coeff.clone().boxed()).boxed(),
        ));
        let rhs = simplify_ode_expr(Expr::Sub(b_coeff.boxed(), delta.boxed()));
        let solved = solve_linear_ode_in_base(a_const, &rhs, &base_var, &lower_tower)?;
        coeffs.insert(deg, simplify_fully(solved.clone()));
        next_coeff = solved;
    }

    Some(ExprPoly { coeffs })
}

fn verify_linear_ode_solution(
    candidate: Expr,
    a_expr: &Expr,
    b_expr: &Expr,
    base_tower: &Tower,
) -> Option<Expr> {
    let y_deriv = derivative_in_tower(&candidate, base_tower)?;
    let lhs = simplify_ode_expr(Expr::Add(
        y_deriv.boxed(),
        Expr::Mul(a_expr.clone().boxed(), candidate.clone().boxed()).boxed(),
    ));
    let residual = simplify_ode_expr(Expr::Sub(lhs.boxed(), b_expr.clone().boxed()));
    if expr_is_zero(&residual) {
        Some(candidate)
    } else {
        None
    }
}

fn normalize_constant_denominator(
    numer: ExprPoly,
    denom: ExprPoly,
) -> Option<(ExprPoly, ExprPoly)> {
    if denom.degree().unwrap_or(0) == 0 {
        let coeff = simplify_fully(denom.coeff(0));
        if coeff.is_zero() {
            return None;
        }
        let scale = Expr::Div(
            Expr::Constant(Rational::one()).boxed(),
            coeff.boxed(),
        );
        let numer_scaled = simplify_expr_poly(numer.scale(&scale));
        return Some((numer_scaled, ExprPoly::one()));
    }
    Some((numer, denom))
}

fn expr_is_zero(expr: &Expr) -> bool {
    simplify_ode_expr(expr.clone()).is_zero()
}

fn simplify_ode_expr(expr: Expr) -> Expr {
    let simplified = simplify_fully(expr);
    normalize(simplified)
}
