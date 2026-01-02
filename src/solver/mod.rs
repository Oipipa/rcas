use std::collections::HashMap;

use crate::core::expr::{Expr, Rational};
use crate::simplify::simplify;
use num_traits::{One, Signed, Zero};

#[derive(Debug, Clone)]
pub enum SolveResult {
    Linear(LinearResult),
    NonLinear(NonLinearResult),
}

#[derive(Debug, Clone)]
pub enum LinearResult {
    Unique(LinearSolution),
    Infinite(LinearFamily),
    Inconsistent(LinearInconsistent),
}

#[derive(Debug, Clone)]
pub struct LinearSolution {
    pub variables: Vec<String>,
    pub values: Vec<Expr>,
    pub diagnostics: LinearDiagnostics,
}

#[derive(Debug, Clone)]
pub struct LinearFamily {
    pub variables: Vec<String>,
    pub particular: Vec<Expr>,
    pub params: Vec<String>,
    pub basis: Vec<Vec<Expr>>,
    pub diagnostics: LinearDiagnostics,
}

#[derive(Debug, Clone)]
pub struct LinearInconsistent {
    pub diagnostics: LinearDiagnostics,
}

#[derive(Debug, Clone, Default)]
pub struct LinearDiagnostics {
    pub rank: usize,
    pub pivot_rows: Vec<usize>,
    pub pivot_columns: Vec<usize>,
    pub free_columns: Vec<usize>,
    pub determinant: Option<Rational>,
    pub inconsistent_row: Option<usize>,
    pub normalized_equations: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct NonLinearResult {
    pub variables: Vec<String>,
    pub normalized_equations: Vec<Expr>,
    pub nonlinear_equations: Vec<usize>,
    pub status: NonLinearStatus,
}

#[derive(Debug, Clone)]
pub enum NonLinearStatus {
    Detected,
    NotImplemented,
}

struct LinearDecomposition {
    coeffs: Vec<Rational>,
    constant: Rational,
    residual: Expr,
}

/// Solve a system of equations provided as (lhs, rhs) pairs using the exact Gaussian elimination
/// pipeline. When non-linear content is detected, a NonLinearResult is returned to allow callers
/// to branch into numeric or factoring strategies.
pub fn solve_system(vars: Vec<impl Into<String>>, equations: Vec<(Expr, Expr)>) -> SolveResult {
    let variables: Vec<String> = vars.into_iter().map(Into::into).collect();
    let var_map: HashMap<String, usize> = variables
        .iter()
        .enumerate()
        .map(|(i, v)| (v.clone(), i))
        .collect();

    let eq_len = equations.len();
    let mut normalized_equations = Vec::with_capacity(eq_len);
    let mut decompositions = Vec::with_capacity(eq_len);
    let mut nonlinear_eqs = Vec::with_capacity(eq_len);

    for (idx, (lhs, rhs)) in equations.into_iter().enumerate() {
        let normalized = simplify(Expr::Sub(lhs.boxed(), rhs.boxed()));
        let decomp = decompose_linear(&normalized, &var_map);
        if !is_zero_expr(&decomp.residual) {
            nonlinear_eqs.push(idx);
        }
        normalized_equations.push(normalized);
        decompositions.push(decomp);
    }

    if !nonlinear_eqs.is_empty() {
        return SolveResult::NonLinear(NonLinearResult {
            variables,
            normalized_equations,
            nonlinear_equations: nonlinear_eqs,
            status: NonLinearStatus::Detected,
        });
    }

    let mut matrix = build_augmented(&decompositions, variables.len());
    let det_slot = if matrix.rows == variables.len() {
        Some(Rational::one())
    } else {
        None
    };
    let mut diagnostics = LinearDiagnostics {
        determinant: det_slot,
        normalized_equations: normalized_equations.clone(),
        ..LinearDiagnostics::default()
    };

    rref(&mut matrix, variables.len(), &mut diagnostics);
    diagnostics.free_columns = free_columns(variables.len(), &diagnostics.pivot_columns);

    if let Some(_offending) = diagnostics.inconsistent_row {
        return SolveResult::Linear(LinearResult::Inconsistent(LinearInconsistent {
            diagnostics,
        }));
    }

    if diagnostics.rank == variables.len() {
        let mut values = vec![Expr::Constant(Rational::zero()); variables.len()];
        for (&row, &col) in diagnostics
            .pivot_rows
            .iter()
            .zip(diagnostics.pivot_columns.iter())
        {
            values[col] = Expr::Constant(matrix.get(row, variables.len()).clone());
        }
        return SolveResult::Linear(LinearResult::Unique(LinearSolution {
            variables,
            values,
            diagnostics,
        }));
    }

    let params: Vec<String> = diagnostics
        .free_columns
        .iter()
        .enumerate()
        .map(|(i, _)| format!("t{}", i + 1))
        .collect();

    let mut particular = vec![Expr::Constant(Rational::zero()); variables.len()];
    for (&row, &col) in diagnostics
        .pivot_rows
        .iter()
        .zip(diagnostics.pivot_columns.iter())
    {
        particular[col] = Expr::Constant(matrix.get(row, variables.len()).clone());
    }

    let mut basis = Vec::new();
    for &free_col in &diagnostics.free_columns {
        let mut vec = vec![Expr::Constant(Rational::zero()); variables.len()];
        vec[free_col] = Expr::Constant(Rational::one());
        for (&row, &pivot_col) in diagnostics
            .pivot_rows
            .iter()
            .zip(diagnostics.pivot_columns.iter())
        {
            let coeff = matrix.get(row, free_col).clone();
            if !coeff.is_zero() {
                vec[pivot_col] = Expr::Constant(-coeff);
            }
        }
        basis.push(vec);
    }

    SolveResult::Linear(LinearResult::Infinite(LinearFamily {
        variables,
        particular,
        params,
        basis,
        diagnostics,
    }))
}

fn decompose_linear(expr: &Expr, var_map: &HashMap<String, usize>) -> LinearDecomposition {
    let mut coeffs = vec![Rational::zero(); var_map.len()];
    let mut constant = Rational::zero();
    let mut residual_terms = Vec::new();
    collect_linear_terms(
        expr,
        Rational::one(),
        &mut coeffs,
        &mut constant,
        &mut residual_terms,
        var_map,
    );
    let residual = if residual_terms.is_empty() {
        Expr::Constant(Rational::zero())
    } else {
        simplify(sum_exprs(residual_terms))
    };
    LinearDecomposition {
        coeffs,
        constant,
        residual,
    }
}

fn collect_linear_terms(
    expr: &Expr,
    scale: Rational,
    coeffs: &mut [Rational],
    constant: &mut Rational,
    residual_terms: &mut Vec<Expr>,
    var_map: &HashMap<String, usize>,
) {
    match expr {
        Expr::Constant(c) => {
            *constant += scale * c.clone();
        }
        Expr::Variable(name) => {
            if let Some(&idx) = var_map.get(name) {
                coeffs[idx] += scale;
            } else {
                residual_terms.push(scale_expr(scale, expr.clone()));
            }
        }
        Expr::Add(a, b) => {
            collect_linear_terms(a, scale.clone(), coeffs, constant, residual_terms, var_map);
            collect_linear_terms(b, scale, coeffs, constant, residual_terms, var_map);
        }
        Expr::Sub(a, b) => {
            collect_linear_terms(a, scale.clone(), coeffs, constant, residual_terms, var_map);
            collect_linear_terms(b, -scale, coeffs, constant, residual_terms, var_map);
        }
        Expr::Neg(a) => collect_linear_terms(a, -scale, coeffs, constant, residual_terms, var_map),
        Expr::Mul(a, b) => {
            if let Some(c) = constant_of(a) {
                collect_linear_terms(b, scale * c, coeffs, constant, residual_terms, var_map);
            } else if let Some(c) = constant_of(b) {
                collect_linear_terms(a, scale * c, coeffs, constant, residual_terms, var_map);
            } else {
                residual_terms.push(scale_expr(scale, expr.clone()));
            }
        }
        Expr::Div(a, b) => {
            if let Some(c) = constant_of(b) {
                collect_linear_terms(a, scale / c, coeffs, constant, residual_terms, var_map);
            } else {
                residual_terms.push(scale_expr(scale, expr.clone()));
            }
        }
        _ => residual_terms.push(scale_expr(scale, expr.clone())),
    }
}

fn constant_of(expr: &Expr) -> Option<Rational> {
    match expr {
        Expr::Constant(c) => Some(c.clone()),
        Expr::Neg(inner) => constant_of(inner).map(|c| -c),
        _ => None,
    }
}

fn scale_expr(scale: Rational, expr: Expr) -> Expr {
    if scale.is_zero() {
        Expr::Constant(Rational::zero())
    } else if scale.is_one() {
        expr
    } else {
        Expr::Mul(Expr::Constant(scale).boxed(), expr.boxed())
    }
}

fn sum_exprs(mut terms: Vec<Expr>) -> Expr {
    match terms.len() {
        0 => Expr::Constant(Rational::zero()),
        1 => terms.remove(0),
        _ => terms
            .into_iter()
            .reduce(|acc, t| Expr::Add(acc.boxed(), t.boxed()))
            .unwrap(),
    }
}

fn build_augmented(rows: &[LinearDecomposition], n_vars: usize) -> Matrix {
    let cols = n_vars + 1;
    let mut data = Vec::with_capacity(rows.len() * cols);
    for row in rows {
        for coeff in row.coeffs.iter().take(n_vars) {
            data.push(coeff.clone());
        }
        data.push(-row.constant.clone());
    }
    Matrix {
        rows: rows.len(),
        cols,
        data,
    }
}

fn rref(matrix: &mut Matrix, n_vars: usize, diag: &mut LinearDiagnostics) {
    let rows = matrix.rows;
    if rows == 0 {
        diag.rank = 0;
        return;
    }
    let cols = matrix.cols;
    let mut row = 0;
    for col in 0..n_vars {
        if row >= rows {
            break;
        }

        let mut pivot_row = None;
        let mut pivot_abs = Rational::zero();
        for r in row..rows {
            let value = matrix.get(r, col);
            if !value.is_zero() && value.clone().abs() > pivot_abs {
                pivot_abs = value.clone().abs();
                pivot_row = Some(r);
            }
        }

        let Some(pivot_idx) = pivot_row else {
            continue;
        };

        if pivot_idx != row {
            matrix.swap_rows(row, pivot_idx);
            if let Some(det) = diag.determinant.as_mut() {
                *det = -det.clone();
            }
        }

        let pivot_value = matrix.get(row, col).clone();
        if let Some(det) = diag.determinant.as_mut() {
            *det *= pivot_value.clone();
        }

        // Normalize pivot row.
        for c in col..cols {
            let cell = matrix.get_mut(row, c);
            *cell /= pivot_value.clone();
        }

        // Borrow slices for elimination.
        let row_start = row * cols;
        let (before, rest) = matrix.data.split_at_mut(row_start);
        let (pivot_row_slice, after) = rest.split_at_mut(cols);
        let pivot_row_ref: &[Rational] = &*pivot_row_slice;

        // eliminate above
        for rrow in before.chunks_exact_mut(cols) {
            let factor = rrow[col].clone();
            if factor.is_zero() {
                continue;
            }
            for c in col..cols {
                let rhs = &pivot_row_ref[c];
                rrow[c] -= &factor * rhs;
            }
        }

        // eliminate below
        for rrow in after.chunks_exact_mut(cols) {
            let factor = rrow[col].clone();
            if factor.is_zero() {
                continue;
            }
            for c in col..cols {
                let rhs = &pivot_row_ref[c];
                rrow[c] -= &factor * rhs;
            }
        }

        diag.pivot_rows.push(row);
        diag.pivot_columns.push(col);
        row += 1;
    }

    diag.rank = diag.pivot_columns.len();
    if let Some(det) = diag.determinant.as_mut() {
        if diag.rank < n_vars {
            *det = Rational::zero();
        }
    }

    for r in row..rows {
        let row_slice = matrix.row(r);
        let all_zero = (0..n_vars).all(|c| row_slice[c].is_zero());
        if all_zero && !row_slice[n_vars].is_zero() {
            diag.inconsistent_row = Some(r);
            break;
        }
    }
}

fn free_columns(n_vars: usize, pivots: &[usize]) -> Vec<usize> {
    let mut is_pivot = vec![false; n_vars];
    for &p in pivots {
        is_pivot[p] = true;
    }

    let mut free = Vec::new();
    for col in 0..n_vars {
        if !is_pivot[col] {
            free.push(col);
        }
    }
    free
}

fn is_zero_expr(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(c) if c.is_zero())
}

struct Matrix {
    rows: usize,
    cols: usize,
    data: Vec<Rational>,
}

impl Matrix {
    fn idx(&self, row: usize, col: usize) -> usize {
        row * self.cols + col
    }

    fn get(&self, row: usize, col: usize) -> &Rational {
        &self.data[self.idx(row, col)]
    }

    fn get_mut(&mut self, row: usize, col: usize) -> &mut Rational {
        let idx = self.idx(row, col);
        &mut self.data[idx]
    }

    fn swap_rows(&mut self, a: usize, b: usize) {
        if a == b {
            return;
        }
        let cols = self.cols;
        let start_a = a * cols;
        let start_b = b * cols;
        for offset in 0..cols {
            self.data.swap(start_a + offset, start_b + offset);
        }
    }

    fn row(&self, row: usize) -> &[Rational] {
        let start = self.idx(row, 0);
        &self.data[start..start + self.cols]
    }
}
