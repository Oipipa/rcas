use std::collections::HashSet;

use num_bigint::BigInt;

use crate::core::error::{CasError, Result};
use crate::core::expr::{Expr, Rational, one, zero};
use crate::simplify::simplify_fully;

use super::poly::{poly_from_coeff, poly_from_power, simplify_poly_coeffs};
use super::tower::Tower;
use super::utils::{expr_depends_on, extract_integer};
use super::ExprPoly;

pub(super) fn poly_derivative(poly: &ExprPoly, tower: &Tower) -> Result<ExprPoly> {
    let top = tower.top_symbol();
    let t_deriv_expr = tower.top_derivative_expr();
    let t_deriv_poly = ExprPoly::from_expr(&t_deriv_expr, top).ok_or_else(|| {
        CasError::Unsupported("top symbol derivative not polynomial".to_string())
    })?;

    let symbols = tower.symbol_set();
    let mut result = ExprPoly::zero();
    for (exp, coeff) in poly.coeff_entries() {
        let coeff_deriv = derive_expr_inner(&coeff, tower, &symbols)?;
        if !coeff_deriv.is_zero() {
            result = result + poly_from_coeff(exp, coeff_deriv);
        }
        if exp == 0 {
            continue;
        }
        let factor = Expr::Constant(Rational::from_integer(BigInt::from(exp as i64)));
        let scaled = simplify_fully(Expr::Mul(coeff.clone().boxed(), factor.boxed()));
        if scaled.is_zero() {
            continue;
        }
        let mut term = poly_from_power(exp - 1);
        term = term * t_deriv_poly.clone();
        term = term.scale(&scaled);
        result = result + term;
    }
    Ok(simplify_poly_coeffs(result))
}

pub(super) fn derive_expr_inner(
    expr: &Expr,
    tower: &Tower,
    symbols: &HashSet<String>,
) -> Result<Expr> {
    if !expr_depends_on(expr, tower.base_var(), symbols) {
        return Ok(zero());
    }
    let derived = match expr {
        Expr::Variable(name) if name == tower.base_var() => one(),
        Expr::Variable(name) => tower.symbol_derivative(name).unwrap_or_else(zero),
        Expr::Constant(_) => zero(),
        Expr::Add(a, b) => Expr::Add(
            derive_expr_inner(a, tower, symbols)?.boxed(),
            derive_expr_inner(b, tower, symbols)?.boxed(),
        ),
        Expr::Sub(a, b) => Expr::Sub(
            derive_expr_inner(a, tower, symbols)?.boxed(),
            derive_expr_inner(b, tower, symbols)?.boxed(),
        ),
        Expr::Mul(a, b) => {
            let da = derive_expr_inner(a, tower, symbols)?;
            let db = derive_expr_inner(b, tower, symbols)?;
            Expr::Add(
                Expr::Mul(da.boxed(), b.clone().boxed()).boxed(),
                Expr::Mul(a.clone().boxed(), db.boxed()).boxed(),
            )
        }
        Expr::Div(a, b) => {
            let da = derive_expr_inner(a, tower, symbols)?;
            let db = derive_expr_inner(b, tower, symbols)?;
            Expr::Div(
                Expr::Sub(
                    Expr::Mul(da.boxed(), b.clone().boxed()).boxed(),
                    Expr::Mul(a.clone().boxed(), db.boxed()).boxed(),
                )
                .boxed(),
                Expr::Pow(b.clone().boxed(), Expr::integer(2).boxed()).boxed(),
            )
        }
        Expr::Neg(inner) => Expr::Neg(derive_expr_inner(inner, tower, symbols)?.boxed()),
        Expr::Pow(base, exp) => {
            let power = extract_integer(exp).ok_or_else(|| {
                CasError::Unsupported("non-integer exponent in derivative".to_string())
            })?;
            if power == 0 {
                zero()
            } else {
                let coeff = Expr::Constant(Rational::from_integer(BigInt::from(power)));
                Expr::Mul(
                    coeff.boxed(),
                    Expr::Mul(
                        Expr::Pow(
                            base.clone().boxed(),
                            Expr::Constant(Rational::from_integer(BigInt::from(power - 1))).boxed(),
                        )
                        .boxed(),
                        derive_expr_inner(base, tower, symbols)?.boxed(),
                    )
                    .boxed(),
                )
            }
        }
        _ => {
            if expr_depends_on(expr, tower.base_var(), symbols) {
                return Err(CasError::Unsupported(
                    "unsupported expression in derivative".to_string(),
                ));
            }
            zero()
        }
    };
    Ok(simplify_fully(derived))
}
