use std::collections::{BTreeMap, HashSet};

use num_bigint::BigInt;
use num_traits::{One, Zero};

use crate::calculus::integrate::{contains_var, log_abs, polynomial, rational};
use crate::calculus::risch::diff_field::{ExtensionKind, Tower};
use crate::core::expr::{Expr, Rational};
use crate::simplify::simplify_fully;

use super::algebraic::analyze_algebraic;
use super::expr_poly::{
    expr_poly_as_monomial, expr_poly_div_exact, expr_poly_div_rem, expr_poly_gcd,
    expr_poly_is_one, expr_poly_is_zero, expr_poly_to_expr, expr_to_rational_polys,
    hermite_reduce_expr, simplify_expr_poly,
};
use super::ode::solve_risch_linear_ode;
use super::tower::{
    contains_any_symbol, derivative_in_tower, is_constant_in_tower, is_constant_wrt_base,
    lower_symbol_set, tower_prefix,
};
use super::utils::pow_expr_signed;
use super::{ExprPoly, RischOutcome, RischStep};

pub(super) fn integrate_in_tower(expr_sym: &Expr, var: &str, tower: &Tower) -> RischStep {
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

pub(super) fn integrate_in_base(expr: &Expr, var: &str) -> Option<Expr> {
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
            let log_term = Expr::Mul(c_expr.boxed(), log_abs(den_expr).boxed());
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

pub(super) fn integrate_in_tower_simple(expr: &Expr, var: &str, tower: &Tower) -> Option<Expr> {
    match integrate_in_tower(expr, var, tower) {
        RischStep::Integrated { result, .. } => Some(result),
        _ => None,
    }
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

    polynomial::integrate(&ratio, t_symbol).or_else(|| rational::integrate(&ratio, t_symbol))
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
        log_abs(denom.clone()).boxed(),
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
