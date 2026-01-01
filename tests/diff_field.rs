use rcas::diff_field::{FieldElement, Tower};
use rcas::{differentiate, parse_expr, simplify_fully};

#[test]
fn field_roundtrip_with_generators() {
    let mut tower = Tower::new("x");
    tower.push_exp(parse_expr("x").expect("parse exp arg")).expect("push exp");
    tower.push_log(parse_expr("x").expect("parse log arg")).expect("push log");

    let expr = parse_expr("(x^2 + 1) * exp(x) + log(x)").expect("parse expr");
    let elem = FieldElement::try_from_expr(&expr, &tower).expect("convert to field element");
    let roundtrip = tower.expand_symbols(&elem.to_expr());
    assert_eq!(simplify_fully(roundtrip), simplify_fully(expr));
}

#[test]
fn field_derivative_matches_calculus() {
    let mut tower = Tower::new("x");
    tower.push_exp(parse_expr("x").expect("parse exp arg")).expect("push exp");

    let expr = parse_expr("(x^2 + 1) * exp(x)").expect("parse expr");
    let elem = FieldElement::try_from_expr(&expr, &tower).expect("convert to field element");
    let deriv = elem.derivative().expect("differentiate element");
    let deriv_expr = tower.expand_symbols(&deriv.to_expr());
    let expected = simplify_fully(differentiate("x", &expr));
    assert_eq!(simplify_fully(deriv_expr), expected);
}

#[test]
fn field_constant_checks() {
    let mut tower = Tower::new("x");
    tower.push_exp(parse_expr("x").expect("parse exp arg")).expect("push exp");

    let const_expr = parse_expr("y + 2").expect("parse const expr");
    let const_elem = FieldElement::try_from_expr(&const_expr, &tower).expect("convert const");
    assert!(const_elem.is_constant().expect("constant check"));

    let nonconst_expr = parse_expr("exp(x) + y").expect("parse nonconst expr");
    let nonconst_elem = FieldElement::try_from_expr(&nonconst_expr, &tower).expect("convert nonconst");
    assert!(!nonconst_elem.is_constant().expect("constant check"));
}

#[test]
fn conversion_rejects_unsupported() {
    let tower = Tower::new("x");
    let expr = parse_expr("sin(x)").expect("parse sin");
    assert!(FieldElement::try_from_expr(&expr, &tower).is_err());

    let mut tower = Tower::new("x");
    tower.push_exp(parse_expr("x").expect("parse exp arg")).expect("push exp");
    let expr = parse_expr("log(x)").expect("parse log");
    assert!(FieldElement::try_from_expr(&expr, &tower).is_err());

    let expr = parse_expr("x^(1/2)").expect("parse fractional power");
    let tower = Tower::new("x");
    assert!(FieldElement::try_from_expr(&expr, &tower).is_err());
}

#[test]
fn field_ops_basic() {
    let tower = Tower::new("x");
    let x_expr = parse_expr("x").expect("parse x");
    let inv_expr = parse_expr("1/x").expect("parse inv");
    let x_elem = FieldElement::try_from_expr(&x_expr, &tower).expect("convert x");
    let inv_elem = FieldElement::try_from_expr(&inv_expr, &tower).expect("convert inv");
    let prod = x_elem.mul(&inv_elem).expect("multiply");
    assert_eq!(simplify_fully(prod.to_expr()), simplify_fully(parse_expr("1").unwrap()));

    let f_expr = parse_expr("x/(x+1)").expect("parse f");
    let g_expr = parse_expr("1/(x+1)").expect("parse g");
    let f_elem = FieldElement::try_from_expr(&f_expr, &tower).expect("convert f");
    let g_elem = FieldElement::try_from_expr(&g_expr, &tower).expect("convert g");
    let sum = f_elem.add(&g_elem).expect("add");
    assert_eq!(simplify_fully(sum.to_expr()), simplify_fully(parse_expr("1").unwrap()));
}
