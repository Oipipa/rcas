use crate::core::error::{CasError, Result};
use crate::core::expr::{Expr, one};
use crate::simplify::simplify_fully;

use super::algebraic::reduce_algebraic_rational;
use super::derive::poly_derivative;
use super::poly::{expr_to_rational_polys, poly_to_expr, simplify_poly_coeffs};
use super::tower::Tower;
use super::utils::abs_i64_to_usize;
use super::ExprPoly;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldElement {
    numer: ExprPoly,
    denom: ExprPoly,
    tower: Tower,
}

impl FieldElement {
    pub fn try_from_expr(expr: &Expr, tower: &Tower) -> Result<Self> {
        let simplified = simplify_fully(expr.clone());
        let replaced = tower.replace_generators(&simplified);
        if !tower.expr_in_field(&replaced) {
            return Err(CasError::Unsupported(
                "expression not in differential field".to_string(),
            ));
        }
        let top = tower.top_symbol();
        let (numer, denom) = expr_to_rational_polys(&replaced, top)?;
        FieldElement::from_polys(numer, denom, tower.clone())
    }

    pub fn to_expr(&self) -> Expr {
        let var = self.tower.top_symbol();
        let numer = poly_to_expr(&self.numer, var);
        let denom = poly_to_expr(&self.denom, var);
        if denom.is_one() {
            simplify_fully(numer)
        } else {
            simplify_fully(Expr::Div(numer.boxed(), denom.boxed()))
        }
    }

    pub fn to_original_expr(&self) -> Expr {
        let expr = self.to_expr();
        self.tower.expand_symbols(&expr)
    }

    pub fn is_zero(&self) -> bool {
        self.numer.is_zero()
    }

    pub fn is_constant(&self) -> Result<bool> {
        Ok(self.derivative()?.is_zero())
    }

    pub fn add(&self, other: &Self) -> Result<Self> {
        self.ensure_same_tower(other)?;
        let numer = self.numer.clone() * other.denom.clone()
            + other.numer.clone() * self.denom.clone();
        let denom = self.denom.clone() * other.denom.clone();
        FieldElement::from_polys(numer, denom, self.tower.clone())
    }

    pub fn sub(&self, other: &Self) -> Result<Self> {
        self.ensure_same_tower(other)?;
        let numer = self.numer.clone() * other.denom.clone()
            - other.numer.clone() * self.denom.clone();
        let denom = self.denom.clone() * other.denom.clone();
        FieldElement::from_polys(numer, denom, self.tower.clone())
    }

    pub fn mul(&self, other: &Self) -> Result<Self> {
        self.ensure_same_tower(other)?;
        let numer = self.numer.clone() * other.numer.clone();
        let denom = self.denom.clone() * other.denom.clone();
        FieldElement::from_polys(numer, denom, self.tower.clone())
    }

    pub fn div(&self, other: &Self) -> Result<Self> {
        self.ensure_same_tower(other)?;
        if other.numer.is_zero() {
            return Err(CasError::Unsupported("division by zero".to_string()));
        }
        let numer = self.numer.clone() * other.denom.clone();
        let denom = self.denom.clone() * other.numer.clone();
        FieldElement::from_polys(numer, denom, self.tower.clone())
    }

    pub fn neg(&self) -> Result<Self> {
        FieldElement::from_polys(-self.numer.clone(), self.denom.clone(), self.tower.clone())
    }

    pub fn pow_i64(&self, exp: i64) -> Result<Self> {
        if exp == 0 {
            return FieldElement::from_polys(ExprPoly::one(), ExprPoly::one(), self.tower.clone());
        }
        let power = abs_i64_to_usize(exp)?;
        let mut numer = self.numer.pow(power);
        let mut denom = self.denom.pow(power);
        if exp < 0 {
            std::mem::swap(&mut numer, &mut denom);
        }
        FieldElement::from_polys(numer, denom, self.tower.clone())
    }

    pub fn derivative(&self) -> Result<Self> {
        let numer_deriv = poly_derivative(&self.numer, &self.tower)?;
        let denom_deriv = poly_derivative(&self.denom, &self.tower)?;
        let numer = numer_deriv * self.denom.clone() - self.numer.clone() * denom_deriv;
        let denom = self.denom.clone() * self.denom.clone();
        FieldElement::from_polys(numer, denom, self.tower.clone())
    }

    fn from_polys(numer: ExprPoly, denom: ExprPoly, tower: Tower) -> Result<Self> {
        if denom.is_zero() {
            return Err(CasError::Unsupported("zero denominator".to_string()));
        }
        let mut numer = simplify_poly_coeffs(numer);
        let mut denom = simplify_poly_coeffs(denom);
        if denom.is_zero() {
            return Err(CasError::Unsupported("zero denominator".to_string()));
        }
        if numer.is_zero() {
            denom = ExprPoly::one();
            return Ok(FieldElement { numer, denom, tower });
        }

        if let Some(algebraic) = tower.top_algebraic() {
            let reduced = reduce_algebraic_rational(&numer, &denom, &algebraic.minimal_poly)?;
            numer = reduced.0;
            denom = reduced.1;
            if numer.is_zero() {
                denom = ExprPoly::one();
                return Ok(FieldElement { numer, denom, tower });
            }
        }

        let lc = denom.leading_coeff();
        if !lc.is_one() {
            let scale = Expr::Div(one().boxed(), lc.boxed());
            numer = numer.scale(&scale);
            denom = denom.scale(&scale);
            numer = simplify_poly_coeffs(numer);
            denom = simplify_poly_coeffs(denom);
        }

        Ok(FieldElement { numer, denom, tower })
    }

    fn ensure_same_tower(&self, other: &Self) -> Result<()> {
        if self.tower != other.tower {
            return Err(CasError::Unsupported(
                "mismatched differential towers".to_string(),
            ));
        }
        Ok(())
    }
}
