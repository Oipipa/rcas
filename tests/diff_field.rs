use num_traits::ToPrimitive;
use rcas::diff_field::{FieldElement, Tower};
use rcas::{differentiate, parse_expr, simplify_fully, sub};

fn eval_expr_f64(expr: &rcas::Expr, var: &str, x: f64) -> f64 {
    match expr {
        rcas::Expr::Constant(c) => c.to_f64().expect("constant to f64"),
        rcas::Expr::Variable(v) => {
            if v == var {
                x
            } else {
                0.0
            }
        }
        rcas::Expr::Add(a, b) => eval_expr_f64(a, var, x) + eval_expr_f64(b, var, x),
        rcas::Expr::Sub(a, b) => eval_expr_f64(a, var, x) - eval_expr_f64(b, var, x),
        rcas::Expr::Mul(a, b) => eval_expr_f64(a, var, x) * eval_expr_f64(b, var, x),
        rcas::Expr::Div(a, b) => eval_expr_f64(a, var, x) / eval_expr_f64(b, var, x),
        rcas::Expr::Neg(inner) => -eval_expr_f64(inner, var, x),
        rcas::Expr::Pow(base, exp) => {
            let base_val = eval_expr_f64(base, var, x);
            let exponent = match &**exp {
                rcas::Expr::Constant(c) => c.to_f64().expect("exp to f64"),
                _ => panic!("non-constant exponent in eval"),
            };
            base_val.powf(exponent)
        }
        other => panic!("unsupported eval in diff field test: {other:?}"),
    }
}

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
    let delta = simplify_fully(sub(deriv_expr, expected));
    for sample in [0.1, 0.5, 1.2] {
        let value = eval_expr_f64(&delta, "x", sample).abs();
        assert!(value < 1e-6, "algebraic derivative mismatch at {sample}: {value}");
    }
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

#[test]
fn field_algebraic_extension_roundtrip_and_derivative() {
    let mut tower = Tower::new("x");
    tower
        .push_algebraic_root(parse_expr("x^2 + 1").expect("parse base"), 2)
        .expect("push algebraic");

    let expr = parse_expr("(x^2 + 1)^(1/2)").expect("parse algebraic expr");
    let elem = FieldElement::try_from_expr(&expr, &tower).expect("convert to field element");
    let roundtrip = tower.expand_symbols(&elem.to_expr());
    assert_eq!(simplify_fully(roundtrip), simplify_fully(expr.clone()));

    let squared = elem.mul(&elem).expect("multiply");
    let squared_expr = tower.expand_symbols(&squared.to_expr());
    assert_eq!(
        simplify_fully(squared_expr),
        simplify_fully(parse_expr("x^2 + 1").unwrap())
    );

    let deriv = elem.derivative().expect("differentiate element");
    let deriv_expr = tower.expand_symbols(&deriv.to_expr());
    let expected = simplify_fully(differentiate("x", &expr));
    let delta = simplify_fully(sub(deriv_expr, expected));
    for sample in [0.1, 0.5, 1.2] {
        let value = eval_expr_f64(&delta, "x", sample).abs();
        assert!(value < 1e-6, "algebraic derivative mismatch at {sample}: {value}");
    }
}

#[test]
fn field_accepts_parameterized_exp_and_log() {
    let mut tower = Tower::new("x");
    tower
        .push_exp(parse_expr("y*x").expect("parse exp arg"))
        .expect("push exp");
    let expr = parse_expr("y*exp(y*x)").expect("parse expr");
    let elem = FieldElement::try_from_expr(&expr, &tower).expect("convert exp expr");
    let roundtrip = tower.expand_symbols(&elem.to_expr());
    assert_eq!(simplify_fully(roundtrip), simplify_fully(expr));

    let mut tower = Tower::new("x");
    tower
        .push_log(parse_expr("x + y").expect("parse log arg"))
        .expect("push log");
    let expr = parse_expr("log(x + y)").expect("parse log expr");
    let elem = FieldElement::try_from_expr(&expr, &tower).expect("convert log expr");
    let roundtrip = tower.expand_symbols(&elem.to_expr());
    assert_eq!(simplify_fully(roundtrip), simplify_fully(expr));
}

#[test]
fn field_accepts_parameterized_algebraic_extensions() {
    let mut tower = Tower::new("x");
    tower
        .push_algebraic_root(parse_expr("x^2 + y").expect("parse base"), 2)
        .expect("push algebraic");

    let expr = parse_expr("(x^2 + y)^(1/2)").expect("parse algebraic expr");
    let elem = FieldElement::try_from_expr(&expr, &tower).expect("convert algebraic expr");
    let roundtrip = tower.expand_symbols(&elem.to_expr());
    assert_eq!(simplify_fully(roundtrip), simplify_fully(expr));
}
