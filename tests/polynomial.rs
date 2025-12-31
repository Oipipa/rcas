use num_traits::Zero;
use rcas::{Poly, Rational, parse_expr};

fn poly(input: &str) -> Poly {
    let expr = parse_expr(input).expect("parse polynomial");
    Poly::from_expr(&expr, "x").expect("build polynomial")
}

#[test]
fn polynomial_division_exact() {
    let dividend = poly("x^3 - 1");
    let divisor = poly("x - 1");
    let (quotient, remainder) = dividend.div_rem(&divisor);
    assert!(remainder.is_zero());
    assert_eq!(quotient, poly("x^2 + x + 1"));
}

#[test]
fn polynomial_division_remainder() {
    let dividend = poly("x^3 + x + 1");
    let divisor = poly("x^2 + 1");
    let (quotient, remainder) = dividend.div_rem(&divisor);
    assert_eq!(quotient, poly("x"));
    assert_eq!(remainder, poly("1"));
}

#[test]
fn polynomial_division_non_exact() {
    let dividend = poly("x^2 + 1");
    let divisor = poly("x + 1");
    assert!(dividend.div_exact(&divisor).is_none());
}

#[test]
fn polynomial_gcd_is_monic() {
    let a = poly("x^2 - 1");
    let b = poly("x^2 - x");
    let gcd = Poly::gcd(&a, &b);
    assert_eq!(gcd, poly("x - 1"));
}

#[test]
fn polynomial_gcd_ignores_content() {
    let a = poly("2*x^2 + 2*x");
    let b = poly("4*x");
    let gcd = Poly::gcd(&a, &b);
    assert_eq!(gcd, poly("x"));
}

#[test]
fn polynomial_content_and_primitive_part() {
    let polynomial = poly("2/3*x^2 + 4/3*x + 2/3");
    let (content, primitive) = polynomial.content_and_primitive_part();
    assert_eq!(content, Rational::new(2.into(), 3.into()));
    assert_eq!(primitive, poly("x^2 + 2*x + 1"));
    assert_eq!(primitive.scale(&content), polynomial);
}

#[test]
fn polynomial_content_sign_normalizes_leading_coeff() {
    let polynomial = poly("-2*x^2 - 4*x");
    let (content, primitive) = polynomial.content_and_primitive_part();
    assert_eq!(content, Rational::from_integer((-2).into()));
    assert_eq!(primitive, poly("x^2 + 2*x"));
    assert_eq!(primitive.scale(&content), polynomial);
}

#[test]
fn polynomial_content_zero_is_zero() {
    let polynomial = poly("0");
    let (content, primitive) = polynomial.content_and_primitive_part();
    assert!(content.is_zero());
    assert!(primitive.is_zero());
}
