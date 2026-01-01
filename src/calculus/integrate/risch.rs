use std::collections::{BTreeMap, HashMap, HashSet};

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, ToPrimitive, Zero};

use crate::diff_field::{ExtensionKind, FieldElement, Tower};
use crate::expr::{Expr, Rational};
use crate::polynomial::{Poly, Polynomial};
use crate::simplify::simplify_fully;

use super::{NonElementaryKind, contains_var, polynomial, rational};

type ExprPoly = Polynomial<Expr>;

#[derive(Debug, Clone)]
pub enum RischOutcome {
    Integrated { result: Expr, note: String },
    NonElementary { kind: NonElementaryKind, note: String },
    Indeterminate { note: String },
}

enum RischStep {
    Integrated { result: Expr, note: String },
    NonElementary { note: String },
    Indeterminate { note: String },
}

pub fn analyze(expr: &Expr, var: &str) -> RischOutcome {
    let simplified = simplify_fully(expr.clone());
    if let Some(outcome) = analyze_algebraic(&simplified, var) {
        return outcome;
    }
    let tower = match build_tower(&simplified, var) {
        Ok(tower) => tower,
        Err(note) => {
            return RischOutcome::Indeterminate {
                note: format!("tower: {note}"),
            };
        }
    };

    if tower.extensions().is_empty() {
        return RischOutcome::Indeterminate {
            note: "no transcendental generators".to_string(),
        };
    }
    let expr_sym = tower.replace_generators(&simplified);
    match integrate_in_tower(&expr_sym, var, &tower) {
        RischStep::Integrated { result, note } => {
            let restored = tower.expand_symbols(&result);
            RischOutcome::Integrated {
                result: simplify_fully(restored),
                note,
            }
        }
        RischStep::NonElementary { note } => RischOutcome::NonElementary {
            kind: NonElementaryKind::SpecialFunctionNeeded,
            note,
        },
        RischStep::Indeterminate { note } => RischOutcome::Indeterminate { note },
    }
}

fn analyze_algebraic(expr: &Expr, var: &str) -> Option<RischOutcome> {
    let base = find_sqrt_base(expr, var)?;
    let base_poly = Poly::from_expr(&base, var)?;
    let degree = base_poly.degree().unwrap_or(0);
    if degree <= 1 {
        return None;
    }
    if degree > 2 {
        if let Some(result) = integrate_even_base_odd_substitution(expr, var, &base_poly) {
            return Some(RischOutcome::Integrated {
                result: simplify_fully(result),
                note: "algebraic even-base reduction".to_string(),
            });
        }
        return Some(RischOutcome::NonElementary {
            kind: NonElementaryKind::SpecialFunctionNeeded,
            note: "algebraic sqrt degree > 2".to_string(),
        });
    }

    if let Some(result) = integrate_algebraic_expr(expr, var, &base, &base_poly) {
        return Some(RischOutcome::Integrated {
            result: simplify_fully(result),
            note: "algebraic sqrt reduction".to_string(),
        });
    }

    Some(RischOutcome::Indeterminate {
        note: "algebraic sqrt not reducible".to_string(),
    })
}

fn integrate_even_base_odd_substitution(
    expr: &Expr,
    var: &str,
    base_poly: &Poly,
) -> Option<Expr> {
    let reduced_poly = even_poly_to_u(base_poly)?;
    if reduced_poly.degree().unwrap_or(0) > 2 {
        return None;
    }
    let rest = factor_out_var(expr, var)?;
    let u_var = "__u";
    let sqrt_u = Expr::Pow(
        Expr::Variable(u_var.to_string()).boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
            .boxed(),
    );
    let rest_u = simplify_fully(crate::simplify::normalize(crate::simplify::substitute(
        &rest, var, &sqrt_u,
    )));
    let base_expr_u = simplify_fully(reduced_poly.to_expr(u_var));
    let result_u = integrate_algebraic_expr(&rest_u, u_var, &base_expr_u, &reduced_poly)?;
    let half = Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()));
    let scaled = simplify_fully(Expr::Mul(half.boxed(), result_u.boxed()));
    let x_sq = Expr::Pow(
        Expr::Variable(var.to_string()).boxed(),
        Expr::integer(2).boxed(),
    );
    Some(simplify_fully(crate::simplify::substitute(
        &scaled, u_var, &x_sq,
    )))
}

fn integrate_in_tower(expr_sym: &Expr, var: &str, tower: &Tower) -> RischStep {
    if tower.extensions().is_empty() {
        return integrate_in_base(expr_sym, var)
            .map(|result| RischStep::Integrated {
                result,
                note: "risch base reduction".to_string(),
            })
            .unwrap_or_else(|| RischStep::Indeterminate {
                note: "base reduction unavailable".to_string(),
            });
    }

    let t_symbol = tower.top_symbol();
    if !contains_var(expr_sym, t_symbol) {
        let Some(base_tower) = tower_prefix(tower, tower.extensions().len() - 1) else {
            return RischStep::Indeterminate {
                note: "tower prefix failed".to_string(),
            };
        };
        return integrate_in_tower(expr_sym, var, &base_tower);
    }

    let extension = tower.extensions().last().expect("top extension");
    match extension.kind {
        ExtensionKind::Exp => integrate_exp_extension(expr_sym, var, tower),
        ExtensionKind::Log => integrate_log_extension(expr_sym, var, tower),
        ExtensionKind::Algebraic => integrate_algebraic_extension(expr_sym, var, tower),
    }
}

fn integrate_exp_extension(expr_sym: &Expr, var: &str, tower: &Tower) -> RischStep {
    let t_symbol = tower.top_symbol();
    let lower_symbols = lower_symbol_set(tower);
    let t_deriv = tower.top_derivative_expr();
    let Some(a_expr) = exp_derivative_coeff(&t_deriv, t_symbol) else {
        return RischStep::Indeterminate {
            note: "exp derivative coefficient unavailable".to_string(),
        };
    };

    if is_constant_wrt_base(&a_expr, var, &lower_symbols) {
        if let Some(result) =
            integrate_by_symbol_substitution(expr_sym, var, t_symbol, &t_deriv, &lower_symbols)
        {
            return RischStep::Integrated {
                result,
                note: "risch exp substitution".to_string(),
            };
        }
    }

    integrate_exp_rational(expr_sym, var, tower, &a_expr)
}

fn integrate_log_extension(expr_sym: &Expr, var: &str, tower: &Tower) -> RischStep {
    let t_symbol = tower.top_symbol();
    let lower_symbols = lower_symbol_set(tower);
    let t_deriv = tower.top_derivative_expr();
    if let Some(result) =
        integrate_by_symbol_substitution(expr_sym, var, t_symbol, &t_deriv, &lower_symbols)
    {
        return RischStep::Integrated {
            result,
            note: "risch log substitution".to_string(),
        };
    }

    integrate_log_rational(expr_sym, var, tower)
}

fn integrate_algebraic_extension(expr_sym: &Expr, var: &str, tower: &Tower) -> RischStep {
    let expanded = tower.expand_symbols(expr_sym);
    if let Some(outcome) = analyze_algebraic(&expanded, var) {
        return match outcome {
            RischOutcome::Integrated { result, note } => RischStep::Integrated { result, note },
            RischOutcome::NonElementary { note, .. } => RischStep::NonElementary { note },
            RischOutcome::Indeterminate { note } => RischStep::Indeterminate { note },
        };
    }
    RischStep::Indeterminate {
        note: "algebraic reduction unavailable".to_string(),
    }
}

fn integrate_in_base(expr: &Expr, var: &str) -> Option<Expr> {
    if !contains_var(expr, var) {
        return Some(Expr::Mul(
            expr.clone().boxed(),
            Expr::Variable(var.to_string()).boxed(),
        ));
    }
    polynomial::integrate(expr, var).or_else(|| rational::integrate(expr, var))
}

fn integrate_exp_rational(expr_sym: &Expr, var: &str, tower: &Tower, a_expr: &Expr) -> RischStep {
    let t_symbol = tower.top_symbol();
    let Some((mut numer, mut denom)) = expr_to_rational_polys(expr_sym, t_symbol) else {
        return RischStep::Indeterminate {
            note: "exp rational conversion failed".to_string(),
        };
    };
    if expr_poly_is_zero(&denom) {
        return RischStep::Indeterminate {
            note: "exp rational denominator zero".to_string(),
        };
    }

    let Some(base_tower) = tower_prefix(tower, tower.extensions().len() - 1) else {
        return RischStep::Indeterminate {
            note: "exp base tower unavailable".to_string(),
        };
    };

    if let Some(gcd) = expr_poly_gcd(&numer, &denom) {
        if !expr_poly_is_one(&gcd) {
            if let Some(new_numer) = expr_poly_div_exact(&numer, &gcd) {
                if let Some(new_denom) = expr_poly_div_exact(&denom, &gcd) {
                    numer = new_numer;
                    denom = new_denom;
                }
            }
        }
    }

    let denom_lc = simplify_fully(denom.leading_coeff());
    if !denom_lc.is_one() && !denom_lc.is_zero() {
        let scale = Expr::Div(
            Expr::Constant(Rational::one()).boxed(),
            denom_lc.boxed(),
        );
        numer = simplify_expr_poly(numer.scale(&scale));
        denom = simplify_expr_poly(denom.scale(&scale));
    }

    if denom.degree().unwrap_or(0) == 0 {
        let denom_const = simplify_fully(denom.coeff(0));
        if denom_const.is_zero() {
            return RischStep::Indeterminate {
                note: "exp rational zero denominator".to_string(),
            };
        }
        let scale = Expr::Div(
            Expr::Constant(Rational::one()).boxed(),
            denom_const.boxed(),
        );
        numer = simplify_expr_poly(numer.scale(&scale));
        denom = ExprPoly::one();
    }

    if let Some((pow, coeff)) = expr_poly_as_monomial(&denom) {
        let coeff = simplify_fully(coeff);
        if coeff.is_zero() {
            return RischStep::Indeterminate {
                note: "exp monomial denominator zero".to_string(),
            };
        }
        if !coeff.is_one() {
            let scale = Expr::Div(
                Expr::Constant(Rational::one()).boxed(),
                coeff.boxed(),
            );
            numer = simplify_expr_poly(numer.scale(&scale));
        }
        let mut terms = Vec::new();
        for (exp, coeff) in numer.coeff_entries() {
            let total_exp = exp as i64 - pow as i64;
            let Some(term) =
                integrate_exp_term(&coeff, total_exp, t_symbol, var, &base_tower, a_expr)
            else {
                return RischStep::Indeterminate {
                    note: "exp laurent coefficient solve failed".to_string(),
                };
            };
            terms.push(term);
        }
        return RischStep::Integrated {
            result: sum_exprs(terms),
            note: "risch exp laurent reduction".to_string(),
        };
    }

    let Some((quotient, remainder)) = expr_poly_div_rem(&numer, &denom) else {
        return RischStep::Indeterminate {
            note: "exp polynomial division failed".to_string(),
        };
    };

    let mut pieces = Vec::new();
    if !expr_poly_is_zero(&quotient) {
        let Some(poly_int) =
            integrate_exp_polynomial(&quotient, t_symbol, var, &base_tower, a_expr)
        else {
            return RischStep::Indeterminate {
                note: "exp polynomial integration failed".to_string(),
            };
        };
        pieces.push(poly_int);
    }

    if expr_poly_is_zero(&remainder) {
        return RischStep::Integrated {
            result: sum_exprs(pieces),
            note: "risch exp polynomial reduction".to_string(),
        };
    }

    let Some((mut hermite_terms, reduced_terms)) =
        hermite_reduce_expr(&remainder, &denom, t_symbol)
    else {
        return RischStep::Indeterminate {
            note: "exp hermite reduction failed".to_string(),
        };
    };
    pieces.append(&mut hermite_terms);

    for (mut num_term, mut den_term) in reduced_terms {
        if expr_poly_is_zero(&num_term) {
            continue;
        }
        let den_lc = simplify_fully(den_term.leading_coeff());
        if !den_lc.is_one() && !den_lc.is_zero() {
            let scale = Expr::Div(
                Expr::Constant(Rational::one()).boxed(),
                den_lc.boxed(),
            );
            num_term = simplify_expr_poly(num_term.scale(&scale));
            den_term = simplify_expr_poly(den_term.scale(&scale));
        }
        let degree = den_term.degree().unwrap_or(0);
        if degree == 0 {
            let num_expr = expr_poly_to_expr(&num_term, t_symbol);
            let Some(term) = integrate_in_tower_simple(&num_expr, var, &base_tower) else {
                return RischStep::Indeterminate {
                    note: "exp reduced base integration failed".to_string(),
                };
            };
            pieces.push(term);
            continue;
        }

        let num_expr = expr_poly_to_expr(&num_term, t_symbol);
        let den_expr = expr_poly_to_expr(&den_term, t_symbol);

        if degree == 1 {
            let s0 = den_term.coeff(0);
            let Some(ds0) = derivative_in_tower(&s0, &base_tower) else {
                return RischStep::Indeterminate {
                    note: "exp linear derivative failed".to_string(),
                };
            };
            let delta = simplify_fully(Expr::Sub(
                ds0.boxed(),
                Expr::Mul(a_expr.clone().boxed(), s0.boxed()).boxed(),
            ));
            if delta.is_zero() {
                return RischStep::NonElementary {
                    note: "exp linear residue check failed".to_string(),
                };
            }
            let c_expr = simplify_fully(Expr::Div(num_expr.clone().boxed(), delta.boxed()));
            let Some(is_const) = is_constant_in_tower(&c_expr, &base_tower) else {
                return RischStep::Indeterminate {
                    note: "exp linear residue constant check failed".to_string(),
                };
            };
            if !is_const {
                return RischStep::NonElementary {
                    note: "exp linear residue not constant".to_string(),
                };
            }
            let k_expr = simplify_fully(Expr::Neg(
                Expr::Mul(c_expr.clone().boxed(), a_expr.clone().boxed()).boxed(),
            ));
            let Some(base_term) = integrate_in_tower_simple(&k_expr, var, &base_tower) else {
                return RischStep::Indeterminate {
                    note: "exp linear base integration failed".to_string(),
                };
            };
            let log_term = Expr::Mul(c_expr.boxed(), super::log_abs(den_expr).boxed());
            pieces.push(simplify_fully(Expr::Add(log_term.boxed(), base_term.boxed())));
            continue;
        }

        let Some(log_term) = integrate_log_term_if_constant(&num_expr, &den_expr, tower) else {
            return RischStep::NonElementary {
                note: "exp residue not constant".to_string(),
            };
        };
        pieces.push(log_term);
    }

    RischStep::Integrated {
        result: sum_exprs(pieces),
        note: "risch exp hermite reduction".to_string(),
    }
}

fn integrate_log_rational(expr_sym: &Expr, var: &str, tower: &Tower) -> RischStep {
    let t_symbol = tower.top_symbol();
    let Some((mut numer, mut denom)) = expr_to_rational_polys(expr_sym, t_symbol) else {
        return RischStep::Indeterminate {
            note: "log rational conversion failed".to_string(),
        };
    };
    if expr_poly_is_zero(&denom) {
        return RischStep::Indeterminate {
            note: "log rational denominator zero".to_string(),
        };
    }

    let Some(base_tower) = tower_prefix(tower, tower.extensions().len() - 1) else {
        return RischStep::Indeterminate {
            note: "log base tower unavailable".to_string(),
        };
    };

    if let Some(gcd) = expr_poly_gcd(&numer, &denom) {
        if !expr_poly_is_one(&gcd) {
            if let Some(new_numer) = expr_poly_div_exact(&numer, &gcd) {
                if let Some(new_denom) = expr_poly_div_exact(&denom, &gcd) {
                    numer = new_numer;
                    denom = new_denom;
                }
            }
        }
    }

    let denom_lc = simplify_fully(denom.leading_coeff());
    if !denom_lc.is_one() && !denom_lc.is_zero() {
        let scale = Expr::Div(
            Expr::Constant(Rational::one()).boxed(),
            denom_lc.boxed(),
        );
        numer = simplify_expr_poly(numer.scale(&scale));
        denom = simplify_expr_poly(denom.scale(&scale));
    }

    if denom.degree().unwrap_or(0) == 0 {
        let denom_const = simplify_fully(denom.coeff(0));
        if denom_const.is_zero() {
            return RischStep::Indeterminate {
                note: "log rational zero denominator".to_string(),
            };
        }
        let scale = Expr::Div(
            Expr::Constant(Rational::one()).boxed(),
            denom_const.boxed(),
        );
        numer = simplify_expr_poly(numer.scale(&scale));
        denom = ExprPoly::one();
    }

    let Some((quotient, remainder)) = expr_poly_div_rem(&numer, &denom) else {
        return RischStep::Indeterminate {
            note: "log polynomial division failed".to_string(),
        };
    };

    let mut pieces = Vec::new();
    if !expr_poly_is_zero(&quotient) {
        let Some(poly_int) = integrate_log_polynomial(&quotient, t_symbol, var, tower, &base_tower)
        else {
            return RischStep::Indeterminate {
                note: "log polynomial integration failed".to_string(),
            };
        };
        pieces.push(poly_int);
    }

    if expr_poly_is_zero(&remainder) {
        return RischStep::Integrated {
            result: sum_exprs(pieces),
            note: "risch log polynomial reduction".to_string(),
        };
    }

    let Some((mut hermite_terms, reduced_terms)) =
        hermite_reduce_expr(&remainder, &denom, t_symbol)
    else {
        return RischStep::Indeterminate {
            note: "log hermite reduction failed".to_string(),
        };
    };
    pieces.append(&mut hermite_terms);

    for (mut num_term, mut den_term) in reduced_terms {
        if expr_poly_is_zero(&num_term) {
            continue;
        }
        let den_lc = simplify_fully(den_term.leading_coeff());
        if !den_lc.is_one() && !den_lc.is_zero() {
            let scale = Expr::Div(
                Expr::Constant(Rational::one()).boxed(),
                den_lc.boxed(),
            );
            num_term = simplify_expr_poly(num_term.scale(&scale));
            den_term = simplify_expr_poly(den_term.scale(&scale));
        }
        let degree = den_term.degree().unwrap_or(0);
        if degree == 0 {
            let num_expr = expr_poly_to_expr(&num_term, t_symbol);
            let Some(term) = integrate_in_tower_simple(&num_expr, var, &base_tower) else {
                return RischStep::Indeterminate {
                    note: "log reduced base integration failed".to_string(),
                };
            };
            pieces.push(term);
            continue;
        }

        let num_expr = expr_poly_to_expr(&num_term, t_symbol);
        let den_expr = expr_poly_to_expr(&den_term, t_symbol);
        let Some(log_term) = integrate_log_term_if_constant(&num_expr, &den_expr, tower) else {
            return RischStep::NonElementary {
                note: "log residue not constant".to_string(),
            };
        };
        pieces.push(log_term);
    }

    RischStep::Integrated {
        result: sum_exprs(pieces),
        note: "risch log hermite reduction".to_string(),
    }
}

fn integrate_exp_polynomial(
    poly: &ExprPoly,
    t_symbol: &str,
    var: &str,
    base_tower: &Tower,
    a_expr: &Expr,
) -> Option<Expr> {
    let mut terms = Vec::new();
    for (exp, coeff) in poly.coeff_entries() {
        let Some(term) =
            integrate_exp_term(&coeff, exp as i64, t_symbol, var, base_tower, a_expr)
        else {
            return None;
        };
        terms.push(term);
    }
    Some(sum_exprs(terms))
}

fn integrate_log_polynomial(
    poly: &ExprPoly,
    t_symbol: &str,
    var: &str,
    tower: &Tower,
    base_tower: &Tower,
) -> Option<Expr> {
    let mut coeffs: BTreeMap<usize, Expr> = poly.coeff_entries().collect();
    let max_deg = poly.degree().unwrap_or(0);
    let a_expr = tower.top_derivative_expr();
    let mut terms = Vec::new();

    for deg in (0..=max_deg).rev() {
        let coeff = coeffs
            .remove(&deg)
            .map(simplify_fully)
            .unwrap_or_else(|| Expr::Constant(Rational::zero()));
        if coeff.is_zero() {
            continue;
        }
        let y = integrate_in_tower_simple(&coeff, var, base_tower)?;
        let term = if deg == 0 {
            y.clone()
        } else {
            Expr::Mul(
                y.clone().boxed(),
                t_power_expr(t_symbol, deg as i64).boxed(),
            )
        };
        terms.push(term);
        if deg > 0 {
            let factor = Expr::Constant(Rational::from_integer(BigInt::from(deg as i64)));
            let delta = simplify_fully(Expr::Mul(
                factor.boxed(),
                Expr::Mul(y.boxed(), a_expr.clone().boxed()).boxed(),
            ));
            let prev = coeffs
                .remove(&(deg - 1))
                .unwrap_or_else(|| Expr::Constant(Rational::zero()));
            let updated = simplify_fully(Expr::Sub(prev.boxed(), delta.boxed()));
            if !updated.is_zero() {
                coeffs.insert(deg - 1, updated);
            }
        }
    }

    Some(sum_exprs(terms))
}

fn integrate_exp_term(
    coeff: &Expr,
    exp: i64,
    t_symbol: &str,
    var: &str,
    base_tower: &Tower,
    a_expr: &Expr,
) -> Option<Expr> {
    let y = solve_risch_linear_ode(coeff, exp, a_expr, var, base_tower)?;
    if exp == 0 {
        return Some(y);
    }
    let t_pow = t_power_expr(t_symbol, exp);
    Some(simplify_fully(Expr::Mul(y.boxed(), t_pow.boxed())))
}

fn integrate_in_tower_simple(expr: &Expr, var: &str, tower: &Tower) -> Option<Expr> {
    match integrate_in_tower(expr, var, tower) {
        RischStep::Integrated { result, .. } => Some(result),
        _ => None,
    }
}

fn solve_risch_linear_ode(
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SqrtBaseDetection {
    None,
    Found,
    Conflict,
}

fn find_sqrt_base(expr: &Expr, var: &str) -> Option<Expr> {
    let mut state = SqrtBaseDetection::None;
    let mut base: Option<Expr> = None;
    collect_sqrt_bases(expr, var, &mut state, &mut base);
    match state {
        SqrtBaseDetection::None => None,
        SqrtBaseDetection::Conflict => None,
        SqrtBaseDetection::Found => base,
    }
}

fn collect_sqrt_bases(
    expr: &Expr,
    var: &str,
    state: &mut SqrtBaseDetection,
    base: &mut Option<Expr>,
) {
    match expr {
        Expr::Pow(inner, exp) => {
            if let Expr::Constant(k) = &**exp {
                if is_half_integer(k) && contains_var(inner, var) {
                    let candidate = simplify_fully((**inner).clone());
                    match base {
                        None => {
                            *base = Some(candidate);
                            *state = SqrtBaseDetection::Found;
                        }
                        Some(existing) if *existing != candidate => {
                            *state = SqrtBaseDetection::Conflict;
                        }
                        _ => {}
                    }
                }
            }
            collect_sqrt_bases(inner, var, state, base);
            collect_sqrt_bases(exp, var, state, base);
        }
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b) => {
            collect_sqrt_bases(a, var, state, base);
            collect_sqrt_bases(b, var, state, base);
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
        | Expr::Exp(inner)
        | Expr::Log(inner)
        | Expr::Abs(inner) => collect_sqrt_bases(inner, var, state, base),
        Expr::Variable(_) | Expr::Constant(_) => {}
    }
}

fn integrate_algebraic_expr(
    expr: &Expr,
    var: &str,
    base_expr: &Expr,
    base_poly: &Poly,
) -> Option<Expr> {
    match expr {
        Expr::Add(a, b) => Some(Expr::Add(
            integrate_algebraic_expr(a, var, base_expr, base_poly)?.boxed(),
            integrate_algebraic_expr(b, var, base_expr, base_poly)?.boxed(),
        )),
        Expr::Sub(a, b) => Some(Expr::Sub(
            integrate_algebraic_expr(a, var, base_expr, base_poly)?.boxed(),
            integrate_algebraic_expr(b, var, base_expr, base_poly)?.boxed(),
        )),
        Expr::Neg(inner) => integrate_algebraic_expr(inner, var, base_expr, base_poly)
            .map(|res| Expr::Neg(res.boxed())),
        _ => integrate_algebraic_term(expr, var, base_expr, base_poly),
    }
}

fn integrate_algebraic_term(
    expr: &Expr,
    var: &str,
    base_expr: &Expr,
    base_poly: &Poly,
) -> Option<Expr> {
    let (const_factor, factors) = super::flatten_product(expr);
    if const_factor.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let base_norm = simplify_fully(base_expr.clone());
    let mut poly_power: i64 = 0;
    let mut sqrt_power: i64 = 0;
    let mut rest_factors = Vec::new();

    for factor in factors {
        match extract_base_powers(&factor, &base_norm) {
            Ok(Some((delta_poly, delta_sqrt))) => {
                poly_power += delta_poly;
                sqrt_power += delta_sqrt;
            }
            Ok(None) => rest_factors.push(factor),
            Err(()) => return None,
        }
    }

    let rest_expr = super::rebuild_product(const_factor, rest_factors);
    let mut rest_poly = Poly::from_expr(&rest_expr, var)?;
    if rest_poly.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }

    let sqrt_q = sqrt_power / 2;
    let sqrt_r = sqrt_power % 2;
    poly_power += sqrt_q;
    sqrt_power = sqrt_r;

    if sqrt_power == 0 {
        return None;
    }
    if sqrt_power != 1 && sqrt_power != -1 {
        return None;
    }

    if sqrt_power == -1 && poly_power < 0 {
        let denom_power = (-poly_power) as usize;
        return integrate_poly_over_sqrt_quadratic_power(&rest_poly, base_poly, var, denom_power);
    }

    if poly_power < 0 {
        let divisor = base_poly.pow((-poly_power) as usize);
        rest_poly = rest_poly.div_exact(&divisor)?;
        poly_power = 0;
    }

    let mut poly_total = rest_poly * base_poly.pow(poly_power as usize);
    if sqrt_power == 1 {
        poly_total = poly_total * base_poly.clone();
    }

    integrate_poly_over_sqrt_quadratic(&poly_total, base_poly, var)
}

fn factor_out_var(expr: &Expr, var: &str) -> Option<Expr> {
    let (const_factor, mut factors) = super::flatten_product(expr);
    let mut removed = false;
    let mut idx = 0;
    while idx < factors.len() {
        if matches!(&factors[idx], Expr::Variable(name) if name == var) {
            factors.remove(idx);
            removed = true;
            break;
        }
        idx += 1;
    }
    if !removed {
        let var_expr = Expr::Variable(var.to_string());
        let candidate = simplify_fully(Expr::Div(expr.clone().boxed(), var_expr.clone().boxed()));
        let rebuilt = simplify_fully(Expr::Mul(candidate.clone().boxed(), var_expr.boxed()));
        if simplify_fully(expr.clone()) == rebuilt {
            return Some(candidate);
        }
        return None;
    }
    Some(super::rebuild_product(const_factor, factors))
}

fn even_poly_to_u(poly: &Poly) -> Option<Poly> {
    let mut coeffs = BTreeMap::new();
    for (exp, coeff) in poly.coeff_entries() {
        if exp % 2 != 0 {
            return None;
        }
        coeffs.insert(exp / 2, coeff);
    }
    Some(Poly { coeffs })
}

#[cfg(test)]
mod algebraic_even_reduction_tests {
    use super::*;
    use crate::parser::parse_expr;

    #[test]
    fn reduces_quartic_even_base_odd_integrand() {
        let expr = parse_expr("x/(x^4+1)^(1/2)").unwrap();
        let base = parse_expr("x^4 + 1").unwrap();
        let base_poly = Poly::from_expr(&base, "x").unwrap();
        assert!(
            integrate_even_base_odd_substitution(&expr, "x", &base_poly).is_some(),
            "expected quartic even-base reduction to succeed"
        );
    }
}

fn extract_base_powers(
    factor: &Expr,
    base: &Expr,
) -> Result<Option<(i64, i64)>, ()> {
    if factor == base {
        return Ok(Some((1, 0)));
    }
    if let Expr::Pow(inner, exp) = factor {
        let inner_norm = simplify_fully((**inner).clone());
        if inner_norm != *base {
            return Ok(None);
        }
        let Expr::Constant(k) = &**exp else {
            return Err(());
        };
        return split_exponent(k).map(Some).ok_or(());
    }
    Ok(None)
}

fn split_exponent(exp: &Rational) -> Option<(i64, i64)> {
    if exp.is_integer() {
        return Some((exp.to_integer().to_i64()?, 0));
    }
    if !is_half_integer(exp) {
        return None;
    }
    let two = BigInt::from(2);
    let (q, r) = exp.numer().div_rem(&two);
    let q = q.to_i64()?;
    let r = r.to_i64()?;
    if r == 0 || r == 1 || r == -1 {
        Some((q, r))
    } else {
        None
    }
}

fn integrate_poly_over_sqrt_quadratic(poly: &Poly, base_poly: &Poly, var: &str) -> Option<Expr> {
    if poly.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }
    if base_poly.degree()? != 2 {
        return None;
    }
    let a = base_poly.coeff(2);
    if a.is_zero() {
        return None;
    }
    let b = base_poly.coeff(1);
    let c = base_poly.coeff(0);

    let two = Rational::from_integer(2.into());
    let four = Rational::from_integer(4.into());
    let h = b.clone() / (two.clone() * a.clone());
    let shift = -h.clone();
    let four_ac = four.clone() * a.clone() * c.clone();
    let b_sq = b.clone() * b.clone();
    let denom = four * a.clone() * a.clone();
    let d = (four_ac - b_sq) / denom;

    let shifted = poly_shift(poly, &shift);

    let u_expr = Expr::Add(
        Expr::Variable(var.to_string()).boxed(),
        Expr::Constant(h).boxed(),
    );
    let u_sq = Expr::Pow(u_expr.clone().boxed(), Expr::integer(2).boxed());
    let u2_plus_d = Expr::Add(u_sq.boxed(), Expr::Constant(d.clone()).boxed());
    let sqrt_expr = Expr::Pow(
        u2_plus_d.boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
            .boxed(),
    );

    let max_deg = shifted.degree().unwrap_or(0);
    let mut integrals: Vec<Expr> = Vec::with_capacity(max_deg + 1);
    integrals.push(super::log_abs(Expr::Add(
        u_expr.clone().boxed(),
        sqrt_expr.clone().boxed(),
    )));
    if max_deg >= 1 {
        integrals.push(sqrt_expr.clone());
    }
    for n in 2..=max_deg {
        let n_rat = Rational::from_integer(BigInt::from(n as i64));
        let term1 = Expr::Div(
            Expr::Mul(
                pow_expr(&u_expr, n - 1).boxed(),
                sqrt_expr.clone().boxed(),
            )
            .boxed(),
            Expr::Constant(n_rat.clone()).boxed(),
        );
        let coeff = Rational::from_integer(BigInt::from((n - 1) as i64)) * d.clone() / n_rat;
        let term2 = Expr::Mul(
            Expr::Constant(coeff).boxed(),
            integrals[n - 2].clone().boxed(),
        );
        let expr = Expr::Sub(term1.boxed(), term2.boxed());
        integrals.push(simplify_fully(expr));
    }

    let mut sum: Option<Expr> = None;
    for (exp, coeff) in shifted.coeff_entries() {
        if coeff.is_zero() {
            continue;
        }
        let term = Expr::Mul(
            Expr::Constant(coeff).boxed(),
            integrals[exp].clone().boxed(),
        );
        sum = Some(match sum {
            None => term,
            Some(acc) => Expr::Add(acc.boxed(), term.boxed()),
        });
    }
    let sum = sum.unwrap_or_else(|| Expr::Constant(Rational::zero()));
    let scale = Expr::Pow(
        Expr::Constant(a).boxed(),
        Expr::Constant(
            Rational::from_integer(BigInt::from(-1)) / Rational::from_integer(2.into()),
        )
            .boxed(),
    );
    Some(simplify_fully(Expr::Mul(scale.boxed(), sum.boxed())))
}

#[derive(Clone)]
struct QuadraticPowerContext {
    u_expr: Expr,
    u2_plus_d: Expr,
    sqrt_expr: Expr,
    log_expr: Expr,
    d: Rational,
}

fn integrate_poly_over_sqrt_quadratic_power(
    poly: &Poly,
    base_poly: &Poly,
    var: &str,
    power: usize,
) -> Option<Expr> {
    if power == 0 {
        return integrate_poly_over_sqrt_quadratic(poly, base_poly, var);
    }
    if poly.is_zero() {
        return Some(Expr::Constant(Rational::zero()));
    }
    if base_poly.degree()? != 2 {
        return None;
    }
    let a = base_poly.coeff(2);
    if a.is_zero() {
        return None;
    }
    let b = base_poly.coeff(1);
    let c = base_poly.coeff(0);

    let two = Rational::from_integer(2.into());
    let four = Rational::from_integer(4.into());
    let h = b.clone() / (two.clone() * a.clone());
    let shift = -h.clone();
    let four_ac = four.clone() * a.clone() * c.clone();
    let b_sq = b.clone() * b.clone();
    let denom = four * a.clone() * a.clone();
    let d = (four_ac - b_sq) / denom;

    let shifted = poly_shift(poly, &shift);

    let u_expr = Expr::Add(
        Expr::Variable(var.to_string()).boxed(),
        Expr::Constant(h).boxed(),
    );
    let u_sq = Expr::Pow(u_expr.clone().boxed(), Expr::integer(2).boxed());
    let u2_plus_d = Expr::Add(u_sq.boxed(), Expr::Constant(d.clone()).boxed());
    let sqrt_expr = Expr::Pow(
        u2_plus_d.clone().boxed(),
        Expr::Constant(Rational::from_integer(1.into()) / Rational::from_integer(2.into()))
            .boxed(),
    );
    let log_expr = super::log_abs(Expr::Add(
        u_expr.clone().boxed(),
        sqrt_expr.clone().boxed(),
    ));

    let ctx = QuadraticPowerContext {
        u_expr,
        u2_plus_d,
        sqrt_expr,
        log_expr,
        d,
    };
    let mut memo = HashMap::new();

    let mut sum: Option<Expr> = None;
    for (exp, coeff) in shifted.coeff_entries() {
        if coeff.is_zero() {
            continue;
        }
        let integral = monomial_integral(exp, power, &ctx, &mut memo)?;
        let term = Expr::Mul(Expr::Constant(coeff).boxed(), integral.boxed());
        sum = Some(match sum {
            None => term,
            Some(acc) => Expr::Add(acc.boxed(), term.boxed()),
        });
    }

    let sum = sum.unwrap_or_else(|| Expr::Constant(Rational::zero()));
    let scale_exp = Rational::from_integer(BigInt::from(-(2 * power as i64 + 1)))
        / Rational::from_integer(2.into());
    let scale = Expr::Pow(Expr::Constant(a).boxed(), Expr::Constant(scale_exp).boxed());
    Some(simplify_fully(Expr::Mul(scale.boxed(), sum.boxed())))
}

fn monomial_integral(
    exp: usize,
    power: usize,
    ctx: &QuadraticPowerContext,
    memo: &mut HashMap<(usize, usize), Expr>,
) -> Option<Expr> {
    if let Some(cached) = memo.get(&(exp, power)) {
        return Some(cached.clone());
    }

    if ctx.d.is_zero() {
        let k = exp as i64 - (2 * power as i64 + 1);
        let result = if k == -1 {
            super::log_abs(ctx.u_expr.clone())
        } else {
            let new_exp = k + 1;
            let denom = Rational::from_integer(BigInt::from(new_exp));
            let pow = pow_expr_signed(&ctx.u_expr, new_exp);
            Expr::Div(pow.boxed(), Expr::Constant(denom).boxed())
        };
        memo.insert((exp, power), result.clone());
        return Some(result);
    }

    let result = match exp {
        0 => {
            if power == 0 {
                ctx.log_expr.clone()
            } else {
                integral_zero(power, ctx, memo)?
            }
        }
        1 => integral_one(power, ctx),
        _ => {
            if power == 0 {
                integral_sqrt(exp, ctx, memo)?
            } else {
                let lower = monomial_integral(exp - 2, power - 1, ctx, memo)?;
                let same = monomial_integral(exp - 2, power, ctx, memo)?;
                Expr::Sub(
                    lower.boxed(),
                    Expr::Mul(Expr::Constant(ctx.d.clone()).boxed(), same.boxed()).boxed(),
                )
            }
        }
    };

    memo.insert((exp, power), result.clone());
    Some(result)
}

fn integral_zero(
    power: usize,
    ctx: &QuadraticPowerContext,
    memo: &mut HashMap<(usize, usize), Expr>,
) -> Option<Expr> {
    if power == 0 {
        return Some(ctx.log_expr.clone());
    }
    let denom = ctx.d.clone() * Rational::from_integer(BigInt::from(2 * power as i64 - 1));
    if denom.is_zero() {
        return None;
    }
    let coeff = Rational::one() / denom.clone();
    let exponent = Rational::from_integer(1.into()) / Rational::from_integer(2.into())
        - Rational::from_integer(BigInt::from(power as i64));
    let pow = Expr::Pow(
        ctx.u2_plus_d.clone().boxed(),
        Expr::Constant(exponent).boxed(),
    );
    let term1 = Expr::Mul(
        Expr::Constant(coeff).boxed(),
        Expr::Mul(ctx.u_expr.clone().boxed(), pow.boxed()).boxed(),
    );
    let recur_coeff =
        Rational::from_integer(BigInt::from(2 * (power as i64 - 1))) / denom;
    let prev = monomial_integral(0, power - 1, ctx, memo)?;
    let term2 = Expr::Mul(Expr::Constant(recur_coeff).boxed(), prev.boxed());
    Some(simplify_fully(Expr::Add(term1.boxed(), term2.boxed())))
}

fn integral_one(power: usize, ctx: &QuadraticPowerContext) -> Expr {
    let exponent = Rational::from_integer(1.into()) / Rational::from_integer(2.into())
        - Rational::from_integer(BigInt::from(power as i64));
    let denom = Rational::from_integer(BigInt::from(1 - 2 * power as i64));
    let pow = Expr::Pow(
        ctx.u2_plus_d.clone().boxed(),
        Expr::Constant(exponent).boxed(),
    );
    let coeff = Rational::one() / denom;
    simplify_fully(Expr::Mul(Expr::Constant(coeff).boxed(), pow.boxed()))
}

fn integral_sqrt(
    exp: usize,
    ctx: &QuadraticPowerContext,
    memo: &mut HashMap<(usize, usize), Expr>,
) -> Option<Expr> {
    if exp == 0 {
        return Some(ctx.log_expr.clone());
    }
    if exp == 1 {
        return Some(ctx.sqrt_expr.clone());
    }
    let n_rat = Rational::from_integer(BigInt::from(exp as i64));
    let term1 = Expr::Div(
        Expr::Mul(
            pow_expr(&ctx.u_expr, exp - 1).boxed(),
            ctx.sqrt_expr.clone().boxed(),
        )
        .boxed(),
        Expr::Constant(n_rat.clone()).boxed(),
    );
    let coeff = Rational::from_integer(BigInt::from((exp - 1) as i64)) * ctx.d.clone() / n_rat;
    let prev = monomial_integral(exp - 2, 0, ctx, memo)?;
    let term2 = Expr::Mul(Expr::Constant(coeff).boxed(), prev.boxed());
    Some(simplify_fully(Expr::Sub(term1.boxed(), term2.boxed())))
}

fn poly_shift(poly: &Poly, shift: &Rational) -> Poly {
    let mut coeffs = BTreeMap::new();
    for (exp, coeff) in poly.coeff_entries() {
        for k in 0..=exp {
            let bin = binomial(exp, k);
            let pow = rational_pow(shift, exp - k);
            let term_coeff = coeff.clone() * Rational::from_integer(bin) * pow;
            if term_coeff.is_zero() {
                continue;
            }
            match coeffs.get_mut(&k) {
                Some(existing) => *existing += term_coeff,
                None => {
                    coeffs.insert(k, term_coeff);
                }
            }
        }
    }
    Poly { coeffs }
}

fn rational_pow(base: &Rational, exp: usize) -> Rational {
    if exp == 0 {
        return Rational::one();
    }
    let mut result = Rational::one();
    let mut power = base.clone();
    let mut n = exp;
    while n > 0 {
        if n % 2 == 1 {
            result *= power.clone();
        }
        power *= power.clone();
        n /= 2;
    }
    result
}

fn binomial(n: usize, k: usize) -> BigInt {
    let k = k.min(n - k);
    let mut numer = BigInt::one();
    let mut denom = BigInt::one();
    for i in 0..k {
        numer *= BigInt::from((n - i) as i64);
        denom *= BigInt::from((i + 1) as i64);
    }
    numer / denom
}

fn pow_expr(base: &Expr, exp: usize) -> Expr {
    if exp == 0 {
        Expr::Constant(Rational::one())
    } else if exp == 1 {
        base.clone()
    } else {
        Expr::Pow(base.clone().boxed(), Expr::integer(exp as i64).boxed())
    }
}

fn pow_expr_signed(base: &Expr, exp: i64) -> Expr {
    if exp == 0 {
        Expr::Constant(Rational::one())
    } else {
        Expr::Pow(
            base.clone().boxed(),
            Expr::Constant(Rational::from_integer(BigInt::from(exp))).boxed(),
        )
    }
}

fn is_half_integer(exp: &Rational) -> bool {
    exp.denom() == &BigInt::from(2)
}

fn integrate_by_symbol_substitution(
    expr_sym: &Expr,
    var: &str,
    t_symbol: &str,
    t_deriv: &Expr,
    lower_symbols: &HashSet<String>,
) -> Option<Expr> {
    let ratio = simplify_fully(Expr::Div(expr_sym.clone().boxed(), t_deriv.clone().boxed()));
    if contains_var(&ratio, var) || contains_any_symbol(&ratio, lower_symbols) {
        return None;
    }

    polynomial::integrate(&ratio, t_symbol)
        .or_else(|| rational::integrate(&ratio, t_symbol))
}

fn exp_derivative_coeff(t_deriv: &Expr, t_symbol: &str) -> Option<Expr> {
    let poly = ExprPoly::from_expr(t_deriv, t_symbol)?;
    if poly.degree()? != 1 {
        return None;
    }
    let constant = poly.coeff(0);
    if !constant.is_zero() {
        return None;
    }
    let coeff = poly.coeff(1);
    if contains_var(&coeff, t_symbol) {
        return None;
    }
    Some(coeff)
}

fn poly_monomial(coeff: Rational, exp: usize) -> Poly {
    if coeff.is_zero() {
        return Poly::zero();
    }
    let mut coeffs = BTreeMap::new();
    coeffs.insert(exp, coeff);
    Poly { coeffs }
}

fn lower_symbol_set(tower: &Tower) -> HashSet<String> {
    let mut symbols: Vec<String> = tower.extensions().iter().map(|ext| ext.symbol.clone()).collect();
    if !symbols.is_empty() {
        symbols.pop();
    }
    symbols.into_iter().collect()
}

fn is_constant_wrt_base(expr: &Expr, var: &str, symbols: &HashSet<String>) -> bool {
    !contains_var(expr, var) && !contains_any_symbol(expr, symbols)
}

fn contains_any_symbol(expr: &Expr, symbols: &HashSet<String>) -> bool {
    match expr {
        Expr::Variable(name) => symbols.contains(name),
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => contains_any_symbol(a, symbols) || contains_any_symbol(b, symbols),
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
        | Expr::Exp(inner)
        | Expr::Log(inner)
        | Expr::Abs(inner) => contains_any_symbol(inner, symbols),
        Expr::Constant(_) => false,
    }
}

fn build_tower(expr: &Expr, var: &str) -> Result<Tower, String> {
    let mut generators = HashSet::new();
    let mut saw_abs_log = false;
    collect_generators(expr, var, &mut generators, &mut saw_abs_log);
    if saw_abs_log {
        return Err("log(abs(..)) not supported".to_string());
    }

    if generators.is_empty() {
        return Ok(Tower::new(var));
    }

    let mut gens_vec: Vec<Expr> = generators.into_iter().collect();
    gens_vec.sort();

    let mut deps: HashMap<Expr, Vec<Expr>> = HashMap::new();
    for gen_expr in &gens_vec {
        let arg = match gen_expr {
            Expr::Exp(inner) | Expr::Log(inner) => inner.as_ref(),
            Expr::Pow(base, _) if algebraic_degree_from_generator(gen_expr).is_some() => {
                base.as_ref()
            }
            _ => continue,
        };
        let mut dep_list = Vec::new();
        for other in &gens_vec {
            if other == gen_expr {
                continue;
            }
            if contains_subexpr(arg, other) {
                dep_list.push(other.clone());
            }
        }
        deps.insert(gen_expr.clone(), dep_list);
    }

    let mut ordered = Vec::new();
    let mut remaining = gens_vec.clone();
    while !remaining.is_empty() {
        let mut next_index = None;
        for (idx, gen_expr) in remaining.iter().enumerate() {
            let ready = deps
                .get(gen_expr)
                .map(|items| items.iter().all(|dep| ordered.contains(dep)))
                .unwrap_or(true);
            if ready {
                next_index = Some(idx);
                break;
            }
        }
        let Some(idx) = next_index else {
            return Err("cyclic generator dependencies".to_string());
        };
        ordered.push(remaining.remove(idx));
    }

    let mut tower = Tower::new(var);
    for gen_expr in ordered {
        match gen_expr {
            Expr::Exp(inner) => {
                tower
                    .push_exp((*inner).clone())
                    .map_err(|err| err.to_string())?;
            }
            Expr::Log(inner) => match &*inner {
                Expr::Abs(_) => return Err("log(abs(..)) not supported".to_string()),
                _ => {
                    tower
                        .push_log((*inner).clone())
                        .map_err(|err| err.to_string())?;
                }
            },
            other => {
                let Some((base_expr, degree)) = algebraic_degree_from_generator(&other) else {
                    continue;
                };
                tower
                    .push_algebraic_root(base_expr, degree)
                    .map_err(|err| err.to_string())?;
            }
        }
    }

    Ok(tower)
}

fn collect_generators(expr: &Expr, var: &str, out: &mut HashSet<Expr>, saw_abs_log: &mut bool) {
    match expr {
        Expr::Exp(inner) => {
            if contains_var(inner, var) {
                out.insert(expr.clone());
            }
            collect_generators(inner, var, out, saw_abs_log);
        }
        Expr::Log(inner) => {
            if matches!(&**inner, Expr::Abs(_)) {
                *saw_abs_log = true;
            }
            if contains_var(inner, var) {
                out.insert(expr.clone());
            }
            collect_generators(inner, var, out, saw_abs_log);
        }
        Expr::Pow(base, exp) => {
            if let Some(root) = algebraic_root_candidate(base, exp) {
                if contains_var(base, var) {
                    out.insert(root);
                }
            }
            collect_generators(base, var, out, saw_abs_log);
            collect_generators(exp, var, out, saw_abs_log);
        }
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) => {
            collect_generators(a, var, out, saw_abs_log);
            collect_generators(b, var, out, saw_abs_log);
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
        | Expr::Abs(inner) => {
            collect_generators(inner, var, out, saw_abs_log);
        }
        Expr::Variable(_) | Expr::Constant(_) => {}
    }
}

fn algebraic_root_candidate(base: &Expr, exp: &Expr) -> Option<Expr> {
    let exp = extract_rational_const(exp)?;
    if exp.is_integer() {
        return None;
    }
    let degree = exp.denom().to_usize()?;
    if degree < 2 {
        return None;
    }
    let root_exp =
        Rational::from_integer(1.into()) / Rational::from_integer(BigInt::from(degree));
    Some(Expr::Pow(
        base.clone().boxed(),
        Expr::Constant(root_exp).boxed(),
    ))
}

fn algebraic_degree_from_generator(expr: &Expr) -> Option<(Expr, usize)> {
    let Expr::Pow(base, exp) = expr else {
        return None;
    };
    let exp = extract_rational_const(exp)?;
    if exp.numer() != &BigInt::from(1) {
        return None;
    }
    let degree = exp.denom().to_usize()?;
    if degree < 2 {
        return None;
    }
    Some((*base.clone(), degree))
}

fn extract_rational_const(expr: &Expr) -> Option<Rational> {
    match expr {
        Expr::Constant(c) => Some(c.clone()),
        Expr::Neg(inner) => extract_rational_const(inner).map(|c| -c),
        _ => None,
    }
}

fn contains_subexpr(expr: &Expr, target: &Expr) -> bool {
    if expr == target {
        return true;
    }
    match expr {
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => contains_subexpr(a, target) || contains_subexpr(b, target),
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
        | Expr::Exp(inner)
        | Expr::Log(inner)
        | Expr::Abs(inner) => contains_subexpr(inner, target),
        Expr::Variable(_) | Expr::Constant(_) => false,
    }
}

fn tower_prefix(tower: &Tower, len: usize) -> Option<Tower> {
    if len > tower.extensions().len() {
        return None;
    }
    let mut base = Tower::new(tower.base_var().to_string());
    for ext in tower.extensions().iter().take(len) {
        match ext.kind {
            ExtensionKind::Exp => match &ext.generator {
                Expr::Exp(inner) => {
                    base.push_exp((**inner).clone()).ok()?;
                }
                _ => return None,
            },
            ExtensionKind::Log => match &ext.generator {
                Expr::Log(inner) => {
                    base.push_log((**inner).clone()).ok()?;
                }
                _ => return None,
            },
            ExtensionKind::Algebraic => {
                let algebraic = ext.algebraic.as_ref()?;
                base.push_algebraic_root(algebraic.base.clone(), algebraic.degree)
                    .ok()?;
            }
        }
    }
    Some(base)
}

fn derivative_in_tower(expr: &Expr, tower: &Tower) -> Option<Expr> {
    let elem = FieldElement::try_from_expr(expr, tower).ok()?;
    let deriv = elem.derivative().ok()?;
    Some(deriv.to_expr())
}

fn is_constant_in_tower(expr: &Expr, tower: &Tower) -> Option<bool> {
    let elem = FieldElement::try_from_expr(expr, tower).ok()?;
    elem.is_constant().ok()
}

fn integrate_log_term_if_constant(num: &Expr, denom: &Expr, tower: &Tower) -> Option<Expr> {
    let d_expr = derivative_in_tower(denom, tower)?;
    if simplify_fully(d_expr.clone()).is_zero() {
        return None;
    }
    let ratio = simplify_fully(Expr::Div(num.clone().boxed(), d_expr.boxed()));
    if !is_constant_in_tower(&ratio, tower)? {
        return None;
    }
    Some(simplify_fully(Expr::Mul(
        ratio.boxed(),
        super::log_abs(denom.clone()).boxed(),
    )))
}

fn t_power_expr(t_symbol: &str, exp: i64) -> Expr {
    let base = Expr::Variable(t_symbol.to_string());
    pow_expr_signed(&base, exp)
}

fn sum_exprs(terms: Vec<Expr>) -> Expr {
    terms
        .into_iter()
        .reduce(|a, b| Expr::Add(a.boxed(), b.boxed()))
        .unwrap_or_else(|| Expr::Constant(Rational::zero()))
}

fn is_negative_one_expr(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(c) if *c == -Rational::one())
}

fn expr_poly_as_monomial(poly: &ExprPoly) -> Option<(usize, Expr)> {
    let simplified = simplify_expr_poly(poly.clone());
    let mut iter = simplified
        .coeff_entries()
        .filter(|(_, coeff)| !simplify_fully(coeff.clone()).is_zero());
    let (exp, coeff) = iter.next()?;
    if iter.next().is_some() {
        return None;
    }
    Some((exp, coeff))
}

fn expr_poly_is_zero(poly: &ExprPoly) -> bool {
    simplify_expr_poly(poly.clone()).is_zero()
}

fn expr_poly_is_one(poly: &ExprPoly) -> bool {
    let simplified = simplify_expr_poly(poly.clone());
    simplified.degree() == Some(0) && simplify_fully(simplified.coeff(0)).is_one()
}

fn simplify_expr_poly(poly: ExprPoly) -> ExprPoly {
    let mut coeffs = BTreeMap::new();
    for (exp, coeff) in poly.coeff_entries() {
        let simplified = simplify_fully(coeff);
        if !simplified.is_zero() {
            coeffs.insert(exp, simplified);
        }
    }
    ExprPoly { coeffs }
}

fn expr_poly_to_expr(poly: &ExprPoly, var: &str) -> Expr {
    if expr_poly_is_zero(poly) {
        return Expr::Constant(Rational::zero());
    }
    let mut terms = Vec::new();
    for (exp, coeff) in poly.coeff_entries() {
        let coeff = simplify_fully(coeff);
        if coeff.is_zero() {
            continue;
        }
        let term = if exp == 0 {
            coeff
        } else {
            let pow = if exp == 1 {
                Expr::Variable(var.to_string())
            } else {
                Expr::Pow(
                    Expr::Variable(var.to_string()).boxed(),
                    Expr::integer(exp as i64).boxed(),
                )
            };
            if coeff.is_one() {
                pow
            } else if is_negative_one_expr(&coeff) {
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
        .unwrap_or_else(|| Expr::Constant(Rational::zero()))
}

fn expr_to_rational_polys(expr: &Expr, var: &str) -> Option<(ExprPoly, ExprPoly)> {
    if !contains_var(expr, var) {
        return Some((ExprPoly::from_constant(expr.clone()), ExprPoly::one()));
    }
    match expr {
        Expr::Variable(name) if name == var => {
            let mut coeffs = BTreeMap::new();
            coeffs.insert(1, Expr::Constant(Rational::one()));
            Some((ExprPoly { coeffs }, ExprPoly::one()))
        }
        Expr::Constant(_) => Some((ExprPoly::from_constant(expr.clone()), ExprPoly::one())),
        Expr::Add(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            let numer = an * bd.clone() + bn * ad.clone();
            let denom = ad * bd;
            Some((simplify_expr_poly(numer), simplify_expr_poly(denom)))
        }
        Expr::Sub(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            let numer = an * bd.clone() - bn * ad.clone();
            let denom = ad * bd;
            Some((simplify_expr_poly(numer), simplify_expr_poly(denom)))
        }
        Expr::Mul(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            Some((simplify_expr_poly(an * bn), simplify_expr_poly(ad * bd)))
        }
        Expr::Div(a, b) => {
            let (an, ad) = expr_to_rational_polys(a, var)?;
            let (bn, bd) = expr_to_rational_polys(b, var)?;
            Some((simplify_expr_poly(an * bd), simplify_expr_poly(ad * bn)))
        }
        Expr::Neg(inner) => {
            let (n, d) = expr_to_rational_polys(inner, var)?;
            Some((simplify_expr_poly(-n), d))
        }
        Expr::Pow(base, exp) => {
            let power = extract_integer_expr(exp)?;
            if power == 0 {
                return Some((ExprPoly::one(), ExprPoly::one()));
            }
            let abs_power = abs_i64_to_usize(power)?;
            let (bn, bd) = expr_to_rational_polys(base, var)?;
            let mut numer = bn.pow(abs_power);
            let mut denom = bd.pow(abs_power);
            if power < 0 {
                std::mem::swap(&mut numer, &mut denom);
            }
            Some((simplify_expr_poly(numer), simplify_expr_poly(denom)))
        }
        _ => None,
    }
}

fn expr_to_rational_polys_rational(expr: &Expr, var: &str) -> Option<(Poly, Poly)> {
    match expr {
        Expr::Variable(name) if name == var => {
            let mut coeffs = BTreeMap::new();
            coeffs.insert(1, Rational::one());
            Some((Poly { coeffs }, Poly::one()))
        }
        Expr::Constant(_) => Some((Poly::from_constant(expr_rational(expr)?), Poly::one())),
        Expr::Add(a, b) => {
            let (an, ad) = expr_to_rational_polys_rational(a, var)?;
            let (bn, bd) = expr_to_rational_polys_rational(b, var)?;
            Some((an * bd.clone() + bn * ad.clone(), ad * bd))
        }
        Expr::Sub(a, b) => {
            let (an, ad) = expr_to_rational_polys_rational(a, var)?;
            let (bn, bd) = expr_to_rational_polys_rational(b, var)?;
            Some((an * bd.clone() - bn * ad.clone(), ad * bd))
        }
        Expr::Mul(a, b) => {
            let (an, ad) = expr_to_rational_polys_rational(a, var)?;
            let (bn, bd) = expr_to_rational_polys_rational(b, var)?;
            Some((an * bn, ad * bd))
        }
        Expr::Div(a, b) => {
            let (an, ad) = expr_to_rational_polys_rational(a, var)?;
            let (bn, bd) = expr_to_rational_polys_rational(b, var)?;
            Some((an * bd, ad * bn))
        }
        Expr::Neg(inner) => {
            let (n, d) = expr_to_rational_polys_rational(inner, var)?;
            Some((-n, d))
        }
        Expr::Pow(base, exp) => {
            let power = extract_integer_expr(exp)?;
            if power == 0 {
                return Some((Poly::one(), Poly::one()));
            }
            let abs_power = abs_i64_to_usize(power)?;
            let (bn, bd) = expr_to_rational_polys_rational(base, var)?;
            let mut numer = bn.pow(abs_power);
            let mut denom = bd.pow(abs_power);
            if power < 0 {
                std::mem::swap(&mut numer, &mut denom);
            }
            Some((numer, denom))
        }
        _ => None,
    }
}

fn expr_rational(expr: &Expr) -> Option<Rational> {
    match expr {
        Expr::Constant(c) => Some(c.clone()),
        Expr::Neg(inner) => expr_rational(inner).map(|c| -c),
        _ => None,
    }
}

fn expr_poly_div_rem(dividend: &ExprPoly, divisor: &ExprPoly) -> Option<(ExprPoly, ExprPoly)> {
    if expr_poly_is_zero(divisor) {
        return None;
    }
    let mut remainder = simplify_expr_poly(dividend.clone());
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
        let scaled = simplify_expr_poly(dividend.scale(&scale));
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
        let term = expr_poly_monomial(coeff, power);
        quotient = simplify_expr_poly(quotient + term.clone());
        remainder = simplify_expr_poly(remainder - term * divisor.clone());
    }

    Some((simplify_expr_poly(quotient), simplify_expr_poly(remainder)))
}

fn expr_poly_div_exact(dividend: &ExprPoly, divisor: &ExprPoly) -> Option<ExprPoly> {
    let (q, r) = expr_poly_div_rem(dividend, divisor)?;
    if expr_poly_is_zero(&r) {
        Some(q)
    } else {
        None
    }
}

fn expr_poly_gcd(a: &ExprPoly, b: &ExprPoly) -> Option<ExprPoly> {
    if expr_poly_is_zero(a) {
        return Some(expr_poly_monic(b));
    }
    if expr_poly_is_zero(b) {
        return Some(expr_poly_monic(a));
    }
    if a.degree().unwrap_or(0) == 0 || b.degree().unwrap_or(0) == 0 {
        return Some(ExprPoly::one());
    }
    let mut r0 = simplify_expr_poly(a.clone());
    let mut r1 = simplify_expr_poly(b.clone());
    while !expr_poly_is_zero(&r1) {
        let (_, r) = expr_poly_div_rem(&r0, &r1)?;
        r0 = r1;
        r1 = r;
    }
    Some(expr_poly_monic(&r0))
}

fn expr_poly_monic(poly: &ExprPoly) -> ExprPoly {
    if expr_poly_is_zero(poly) {
        return poly.clone();
    }
    let lc = simplify_fully(poly.leading_coeff());
    if lc.is_zero() {
        return poly.clone();
    }
    let scale = Expr::Div(
        Expr::Constant(Rational::one()).boxed(),
        lc.boxed(),
    );
    simplify_expr_poly(poly.scale(&scale))
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

fn expr_poly_squarefree_decomposition(poly: &ExprPoly) -> Option<Vec<(ExprPoly, usize)>> {
    if expr_poly_is_zero(poly) || poly.degree().unwrap_or(0) == 0 {
        return Some(Vec::new());
    }
    let mut result = Vec::new();
    let mut i = 1;
    let derivative = expr_poly_derivative_t(poly);
    let mut g = expr_poly_gcd(poly, &derivative)?;
    let mut y = expr_poly_div_exact(poly, &g)?;

    while !expr_poly_is_one(&y) {
        let z = expr_poly_gcd(&y, &g)?;
        let factor = expr_poly_div_exact(&y, &z)?;
        if !expr_poly_is_one(&factor) {
            result.push((factor, i));
        }
        y = z.clone();
        g = expr_poly_div_exact(&g, &z)?;
        i += 1;
    }

    if !expr_poly_is_one(&g) {
        let g_sqrt = expr_poly_squarefree_decomposition(&g)?;
        for (part, mult) in g_sqrt {
            result.push((part, mult + i - 1));
        }
    }

    Some(result)
}

fn hermite_reduce_expr(
    remainder: &ExprPoly,
    denominator: &ExprPoly,
    t_symbol: &str,
) -> Option<(Vec<Expr>, Vec<(ExprPoly, ExprPoly)>)> {
    let parts = expr_poly_squarefree_decomposition(denominator)?;
    if parts.is_empty() {
        return Some((Vec::new(), Vec::new()));
    }

    let mut terms: Vec<Expr> = Vec::new();
    let mut reduced_terms: Vec<(ExprPoly, ExprPoly)> = Vec::new();

    for (squarefree, multiplicity) in parts {
        let denom_part = squarefree.pow(multiplicity);
        let other = expr_poly_div_exact(denominator, &denom_part)?;
        let inv_other = if expr_poly_is_one(&other) {
            ExprPoly::one()
        } else {
            expr_poly_mod_inverse(&other, &denom_part)?
        };
        let num_part = expr_poly_mod(&(remainder.clone() * inv_other), &denom_part);
        let (mut hermite_terms, reduced_num) =
            hermite_reduce_factor_expr(num_part, &squarefree, multiplicity, t_symbol)?;
        terms.append(&mut hermite_terms);
        if !expr_poly_is_zero(&reduced_num) {
            reduced_terms.push((reduced_num, squarefree));
        }
    }

    Some((terms, reduced_terms))
}

fn hermite_reduce_factor_expr(
    mut numerator: ExprPoly,
    squarefree: &ExprPoly,
    multiplicity: usize,
    t_symbol: &str,
) -> Option<(Vec<Expr>, ExprPoly)> {
    if multiplicity == 0 {
        return None;
    }
    if multiplicity == 1 {
        return Some((Vec::new(), numerator));
    }

    let derivative = expr_poly_derivative_t(squarefree);
    if expr_poly_is_zero(&derivative) {
        return None;
    }
    let inv_derivative = expr_poly_mod_inverse(&derivative, squarefree)?;
    let mut terms: Vec<Expr> = Vec::new();
    let mut power = multiplicity;

    while power > 1 {
        let k_minus_one = Rational::from_integer(BigInt::from((power - 1) as i64));
        let remainder = expr_poly_mod(&numerator, squarefree);
        let u = if expr_poly_is_zero(&remainder) {
            ExprPoly::zero()
        } else {
            let scaled = simplify_expr_poly(remainder * inv_derivative.clone());
            let scaled = simplify_expr_poly(scaled.scale(&Expr::Constant(
                Rational::one() / k_minus_one.clone(),
            )));
            let scaled = simplify_expr_poly(
                scaled.scale(&Expr::Constant(Rational::from_integer((-1).into()))),
            );
            expr_poly_mod(&scaled, squarefree)
        };

        if !expr_poly_is_zero(&u) {
            let term = expr_rational_power_term(&u, squarefree, power - 1, t_symbol);
            terms.push(simplify_fully(term));
            let u_prime = expr_poly_derivative_t(&u);
            let u_scaled = simplify_expr_poly(u.scale(&Expr::Constant(k_minus_one.clone())));
            let numerator_adjust =
                simplify_expr_poly(u_prime * squarefree.clone() - u_scaled * derivative.clone());
            let reduced = simplify_expr_poly(numerator - numerator_adjust);
            numerator = expr_poly_div_exact(&reduced, squarefree)?;
        } else {
            numerator = expr_poly_div_exact(&numerator, squarefree)?;
        }

        power -= 1;
    }

    Some((terms, numerator))
}

fn expr_rational_power_term(num: &ExprPoly, den: &ExprPoly, power: usize, var: &str) -> Expr {
    let numerator = expr_poly_to_expr(num, var);
    let exponent = Rational::from_integer(BigInt::from(-(power as i64)));
    let pow = Expr::Pow(
        expr_poly_to_expr(den, var).boxed(),
        Expr::Constant(exponent).boxed(),
    );
    Expr::Mul(numerator.boxed(), pow.boxed())
}

fn expr_poly_mod(poly: &ExprPoly, modulus: &ExprPoly) -> ExprPoly {
    if expr_poly_is_zero(modulus) {
        return poly.clone();
    }
    let (_, remainder) = expr_poly_div_rem(poly, modulus).unwrap_or((ExprPoly::zero(), poly.clone()));
    remainder
}

fn expr_poly_mod_inverse(value: &ExprPoly, modulus: &ExprPoly) -> Option<ExprPoly> {
    if expr_poly_is_zero(modulus) {
        return None;
    }
    let (gcd, _s, t) = expr_poly_extended_gcd(modulus, value)?;
    if !expr_poly_is_one(&gcd) {
        return None;
    }
    Some(expr_poly_mod(&t, modulus))
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
        let s2 = simplify_expr_poly(s0.clone() - q.clone() * s1.clone());
        let t2 = simplify_expr_poly(t0.clone() - q * t1.clone());
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
    let scale = Expr::Div(
        Expr::Constant(Rational::one()).boxed(),
        lc.boxed(),
    );
    Some((
        simplify_expr_poly(r0.scale(&scale)),
        simplify_expr_poly(s0.scale(&scale)),
        simplify_expr_poly(t0.scale(&scale)),
    ))
}

fn expr_poly_monomial(coeff: Expr, exp: usize) -> ExprPoly {
    if simplify_fully(coeff.clone()).is_zero() {
        return ExprPoly::zero();
    }
    let mut coeffs = BTreeMap::new();
    coeffs.insert(exp, coeff);
    ExprPoly { coeffs }
}

fn extract_integer_expr(exp: &Expr) -> Option<i64> {
    match exp {
        Expr::Constant(c) if c.is_integer() => c.to_integer().to_i64(),
        Expr::Neg(inner) => extract_integer_expr(inner).map(|value| -value),
        _ => None,
    }
}

fn abs_i64_to_usize(value: i64) -> Option<usize> {
    value
        .checked_abs()
        .and_then(|abs| usize::try_from(abs).ok())
}
