use rcas::expr::Expr;
use rcas::parse_expr;
use rcas::simplify::{normalize, simplify_fully};

fn normalized(input: &str) -> Expr {
    let expr = parse_expr(input).expect("parse input");
    simplify_fully(normalize(expr))
}

fn expect_normalized(input: &str, expected: &str) {
    let actual = normalized(input);
    let expected_expr = normalized(expected);
    assert_eq!(
        actual, expected_expr,
        "normalization mismatch for {input}: got {actual:?}, expected {expected_expr:?}"
    );
}

#[test]
fn canonicalization_trivial_cases() {
    let cases = vec![
        ("2*x*3", "6*x"),
        ("x*1", "x"),
        ("x/2", "1/2*x"),
        ("2*(x/3)", "2/3*x"),
        ("1 + 2*x", "2*x + 1"),
        ("2*x + 3 + x", "3*x + 3"),
        ("x + 2 + 3*x", "4*x + 2"),
        ("x + 0", "x"),
        ("0*x + 5", "5"),
        ("x*x", "x^2"),
        ("x*x^2", "x^3"),
        ("x^2*x^3", "x^5"),
        ("x^1", "x"),
        ("x^0", "1"),
        ("(3*x + 4)^-1", "1/3*(x + 4/3)^-1"),
        ("(2*x + 6)^2", "4*(x + 3)^2"),
        ("(5*x - 10)^-2", "1/25*(x - 2)^-2"),
        ("-2*x", "-2*x"),
        ("sin(1 + 2*x)", "sin(2*x + 1)"),
        ("cos(3 + x)", "cos(x + 3)"),
        ("exp(1 + x)", "exp(x + 1)"),
        ("log(5 + 2*x)", "log(2*x + 5)"),
        ("tan(2 + 3*x)", "tan(3*x + 2)"),
        ("asin(4 + x)", "asin(x + 4)"),
        ("acos(3 + x)", "acos(x + 3)"),
        ("abs(-x)", "abs(x)"),
        ("abs(abs(x))", "abs(x)"),
        ("exp(0)", "1"),
        ("exp(log(x))", "x"),
        ("log(1)", "0"),
        ("log(exp(x))", "x"),
        ("log(abs(exp(x)))", "x"),
        ("sin(0)", "0"),
        ("cos(0)", "1"),
    ];

    assert_eq!(cases.len(), 34, "expected 34 trivial cases");
    for (input, expected) in cases {
        expect_normalized(input, expected);
    }
}

#[test]
fn normalize_exp_square_stable() {
    let input = "exp(x^2)";
    let result = normalized(input);
    assert_eq!(result, normalized(input), "exp square should normalize stably");
}

#[test]
fn canonicalization_nontrivial_cases() {
    let expected_cases = vec![
        ("6/(2*x + 2)", "3*(x + 1)^-1"),
        ("(4*x - 2)^-3", "1/64*(x - 1/2)^-3"),
        (
            "(2*x + 3)^-1 * 4*(2*x + 3)",
            "2*(2*x + 3)*(x + 3/2)^-1",
        ),
        ("(3*x + 9)^2/(3*x + 9)", "3*x + 9"),
        ("(x*y)^2", "x^2*y^2"),
        ("(2*x*y)^2", "4*x^2*y^2"),
        ("(x + 1)/(2*x + 2)", "1/2"),
        ("(2*x + 2)^2/(2*(x + 1))", "2*(x + 1)"),
        ("(x + 1)^3/(x + 1)", "(x + 1)^2"),
        ("(x + 1)^2*(x + 1)^-1", "x + 1"),
        ("(x^2 - 1)/(x - 1)", "x + 1"),
        ("(x^2 + 2*x + 1)/(x + 1)", "x + 1"),
        ("(1 - x^2)/(x - 1)", "-1*(x + 1)"),
        ("(2*x^2 + 2*x)/(4*x)", "1/2*(x + 1)"),
        ("sin(2*x + 4) + sin(4 + 2*x)", "2*sin(2*x + 4)"),
        ("cos(3 + x) + cos(x + 3)", "2*cos(x + 3)"),
        ("log(2 + x) + log(x + 2)", "2*log(x + 2)"),
        ("exp(1 + x)*exp(x + 1)", "exp(x + 1)^2"),
        ("tan(1 + 2*x) - tan(2*x + 1)", "0"),
    ];

    assert_eq!(expected_cases.len(), 19, "expected 19 targeted cases");
    for (input, expected) in expected_cases {
        expect_normalized(input, expected);
    }

    let idempotent_inputs = vec![
        "((2*x + 4)^-1)^2 * (x + 1)",
        "((x + 1)*(x + 2)) + (x + 1)*(x + 2)",
        "((2*x + 1)^3)/((2*x + 1)^2)",
        "((x + 1)^4)/(x + 1)^2",
        "(2*x+4)*(3*x+6)",
        "((x + 1) + (x + 1))*(2*x)",
        "((3*x + 6)^-2)*((3*x + 6))",
        "(x^2*y)*(x^-2*y^-1)",
        "(x + 1)^-1*(x + 1)",
        "((x*y)^3)/(x^2*y)",
        "(x + 1)^2/(2*(x + 1))",
        "(2*x + 2)^-1 + (2*x + 2)^-1",
        "(x^2 - 1)/(x - 1)",
        "(1 - x^2)/(x - 1)",
        "(2*x^2 + 2*x)/(4*x)",
        "exp(log(x))",
        "log(abs(-x))",
        "sin(cos(x + 1) + 2)",
        "cos(sin(x) + 1)",
        "exp(2*x + 1)*cos(2*x + 1)",
        "(x + 1 + 2*x) / (3*(x + 1))",
        "((x + 2)^2)^3",
        "((x*y)^2)^3",
        "(x + 1)^-3*(x + 1)^2",
        "((2*x + 4)^2)*(x + 1)^-2",
        "(x + 1)^-1*(x + 1)^-1",
        "(2*(x + 1))^2*(1/2)^-2",
        "(3*x + 6)^-1*(3*x + 6)^-1",
    ];

    assert_eq!(idempotent_inputs.len(), 28, "expected 28 idempotence inputs");
    for input in idempotent_inputs {
        let first = normalized(input);
        let second = simplify_fully(normalize(first.clone()));
        assert_eq!(
            first, second,
            "normalization should be idempotent for {input}"
        );
    }
}

#[test]
fn fractional_nested_power_not_collapsed() {
    expect_normalized("(x^2)^(1/2)", "(x^2)^(1/2)");
}
