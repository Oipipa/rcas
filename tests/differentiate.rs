use rcas::{differentiate, parse_expr, simplify_fully};

fn assert_diff_eq(var: &str, input: &str, expected: &str) {
    let expr = parse_expr(input).expect("parse input");
    let got = simplify_fully(differentiate(var, &expr));
    let expected_expr = simplify_fully(parse_expr(expected).expect("parse expected"));
    assert_eq!(got, expected_expr, "d/d{var} {input}");
}

#[test]
fn basic_vars_and_constants() {
    assert_diff_eq("x", "x", "1");
    assert_diff_eq("x", "y", "0");
    assert_diff_eq("x", "5", "0");
}

#[test]
fn polynomials_and_products() {
    assert_diff_eq("x", "x^3", "3*x^2");
    assert_diff_eq("x", "x*y", "y");
    assert_diff_eq("x", "2*x^2+3*x", "4*x+3");
}

#[test]
fn trig_and_exponentials() {
    assert_diff_eq("x", "sin(x)", "cos(x)");
    assert_diff_eq("x", "cos(x)", "-sin(x)");
    assert_diff_eq("x", "exp(x^2)", "2*x*exp(x^2)");
}

#[test]
fn extended_trig_and_hyperbolic() {
    assert_diff_eq("x", "sec(x)", "sec(x)*tan(x)");
    assert_diff_eq("x", "csc(x)", "-csc(x)*cot(x)");
    assert_diff_eq("x", "cot(x)", "-(csc(x)^2)");
    assert_diff_eq("x", "asec(x)", "1/(abs(x)*(x^2 - 1)^(1/2))");
    assert_diff_eq("x", "acsc(x)", "-1/(abs(x)*(x^2 - 1)^(1/2))");
    assert_diff_eq("x", "acot(x)", "-1/(1 + x^2)");
    assert_diff_eq("x", "sinh(x)", "cosh(x)");
    assert_diff_eq("x", "cosh(x)", "sinh(x)");
    assert_diff_eq("x", "tanh(x)", "1/cosh(x)^2");
    assert_diff_eq("x", "asinh(x)", "1/(x^2 + 1)^(1/2)");
    assert_diff_eq("x", "acosh(x)", "1/(x^2 - 1)^(1/2)");
    assert_diff_eq("x", "atanh(x)", "1/(1 - x^2)");
}

#[test]
fn nontrivial_hyperbolic_chain_rules() {
    assert_diff_eq("x", "x*atanh(x/y)", "atanh(x/y) + x*((y/y^2)/(1 - (x/y)^2))");
    assert_diff_eq("x", "sinh(2*x + 1)", "2*cosh(2*x + 1)");
    assert_diff_eq("x", "asinh(x^2)", "2*x/((x^2)^2 + 1)^(1/2)");
}

#[test]
fn general_power_rule() {
    assert_diff_eq("x", "x^x", "x^x*(log(x)+1)");
    assert_diff_eq("x", "log(x)", "1/x");
}
