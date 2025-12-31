use num_traits::{One, ToPrimitive, Zero};
use rcas::{
    AttemptStatus, Expr, IntegrandKind, IntegrationResult, NonElementaryKind, Rational, ReasonCode,
    Strategy, differentiate, integrate, parse_expr, simplify_fully, sub,
};

fn simplify_parse(input: &str) -> rcas::Expr {
    simplify_fully(parse_expr(input).expect("parse input"))
}

fn assert_polynomial_integral(input: &str, expected: &str) {
    let expr = simplify_parse(input);
    let expected_expr = simplify_parse(expected);
    match integrate("x", &expr) {
        IntegrationResult::Integrated { result, report } => {
            assert_eq!(
                report.kind,
                IntegrandKind::Polynomial,
                "integrand kind for {input}"
            );
            assert_eq!(
                simplify_fully(result),
                expected_expr,
                "integral of {input} should match expected form"
            );
        }
        other => panic!("expected integration for {input}, got {other:?}"),
    }
}

fn eval_polynomial(expr: &Expr, var: &str, x: &Rational, other: &Rational) -> Rational {
    match expr {
        Expr::Constant(c) => c.clone(),
        Expr::Variable(v) => {
            if v == var {
                x.clone()
            } else {
                other.clone()
            }
        }
        Expr::Add(a, b) => eval_polynomial(a, var, x, other) + eval_polynomial(b, var, x, other),
        Expr::Sub(a, b) => eval_polynomial(a, var, x, other) - eval_polynomial(b, var, x, other),
        Expr::Mul(a, b) => eval_polynomial(a, var, x, other) * eval_polynomial(b, var, x, other),
        Expr::Div(a, b) => eval_polynomial(a, var, x, other) / eval_polynomial(b, var, x, other),
        Expr::Neg(inner) => -eval_polynomial(inner, var, x, other),
        Expr::Pow(base, exp) => {
            let base_val = eval_polynomial(base, var, x, other);
            let exponent = match &**exp {
                Expr::Constant(k) => k.clone(),
                _ => panic!("non-constant exponent in polynomial evaluation"),
            };
            assert!(
                exponent.is_integer(),
                "non-integer exponent encountered in polynomial evaluation"
            );
            let mut n = exponent
                .to_integer()
                .to_i64()
                .expect("integer exponent should fit in i64");
            if n == 0 {
                return Rational::one();
            }
            let mut acc = Rational::one();
            let factor = base_val;
            if n < 0 {
                n = -n;
                for _ in 0..n {
                    acc *= factor.clone();
                }
                Rational::one() / acc
            } else {
                for _ in 0..n {
                    acc *= factor.clone();
                }
                acc
            }
        }
        _ => panic!("unexpected expression form in polynomial evaluation: {expr:?}"),
    }
}

fn assert_polynomial_roundtrip(input: &str) {
    let expr = simplify_parse(input);
    match integrate("x", &expr) {
        IntegrationResult::Integrated { result, report } => {
            assert_eq!(
                report.kind,
                IntegrandKind::Polynomial,
                "integrand kind for {input}"
            );
            let derivative = simplify_fully(differentiate("x", &result));
            let target = simplify_fully(expr);
            let delta = simplify_fully(sub(derivative.clone(), target.clone()));
            let samples = [-2, -1, 0, 1, 2, 3];
            let other_val = Rational::from_integer(2.into());
            for s in samples {
                let value = Rational::from_integer(s.into());
                let eval = eval_polynomial(&delta, "x", &value, &other_val);
                assert!(
                    eval.is_zero(),
                    "differentiate(integrate({input})) should return the original; \
                     difference evaluates to {eval} at x={s}"
                );
            }
        }
        other => panic!("expected integration for {input}, got {other:?}"),
    }
}

#[test]
fn integrates_polynomial_and_rational() {
    let poly = parse_expr("x^3").expect("parse poly");
    let res = integrate("x", &poly);
    match res {
        IntegrationResult::Integrated { result, report } => {
            assert_eq!(
                simplify_fully(result),
                simplify_parse("1/4 * x^4"),
                "integral of x^3"
            );
            assert_eq!(report.kind, IntegrandKind::Polynomial);
        }
        other => panic!("expected integration, got {other:?}"),
    }

    let rational = parse_expr("(2*x+3)/(x+1)").expect("parse rational");
    let res = integrate("x", &rational);
    match res {
        IntegrationResult::Integrated { result, report } => {
            assert_eq!(
                simplify_fully(result),
                simplify_parse("2*x + log(x+1)"),
                "integral of (2*x+3)/(x+1)"
            );
            assert_eq!(report.kind, IntegrandKind::Rational { linear: true });
            assert!(
                report
                    .attempts
                    .iter()
                    .any(|a| a.strategy == Strategy::Direct && a.status == AttemptStatus::Succeeded),
                "direct strategy should succeed"
            );
        }
        other => panic!("expected integration, got {other:?}"),
    }
}

#[test]
fn integrates_affine_trig_exp_log_and_one_over_x() {
    let sin_affine = parse_expr("sin(2*x + 3)").expect("parse sin affine");
    let sin_res = integrate("x", &sin_affine);
    match sin_res {
        IntegrationResult::Integrated { result, .. } => assert_eq!(
            simplify_fully(result),
            simplify_parse("-1/2 * cos(2*x + 3)"),
            "sin(kx+b) should integrate with linear coefficient"
        ),
        other => panic!("expected sin affine integration, got {other:?}"),
    }

    let exp_affine = parse_expr("exp(2*x + 1)").expect("parse exp affine");
    let exp_res = integrate("x", &exp_affine);
    match exp_res {
        IntegrationResult::Integrated { result, .. } => assert_eq!(
            simplify_fully(result),
            simplify_parse("1/2 * exp(2*x + 1)"),
            "exp(kx+b) should integrate with linear coefficient"
        ),
        other => panic!("expected exp affine integration, got {other:?}"),
    }

    let log_linear = parse_expr("log(2*x + 3)").expect("parse log linear");
    let log_res = integrate("x", &log_linear);
    match log_res {
        IntegrationResult::Integrated { result, .. } => assert_eq!(
            simplify_fully(result),
            simplify_parse("((2*x + 3)*log(2*x + 3) - (2*x + 3)) / 2"),
            "log(kx+b) should use linear-change-of-variables formula"
        ),
        other => panic!("expected log linear integration, got {other:?}"),
    }

    let inv_x = parse_expr("x^-1").expect("parse x^-1");
    let inv_res = integrate("x", &inv_x);
    match inv_res {
        IntegrationResult::Integrated { result, .. } => assert_eq!(
            simplify_fully(result),
            simplify_parse("log(x)"),
            "x^-1 should integrate to log(x)"
        ),
        other => panic!("expected x^-1 integration, got {other:?}"),
    }
}

#[test]
fn substitution_and_parts_heuristics() {
    let sub_expr = parse_expr("2*x*exp(x^2)").expect("parse substitution case");
    let res = integrate("x", &sub_expr);
    match res {
        IntegrationResult::Integrated { result, report } => {
            assert_eq!(
                simplify_fully(result),
                simplify_parse("exp(x^2)"),
                "u-substitution result"
            );
            assert!(
                report
                    .attempts
                    .iter()
                    .any(|a| a.strategy == Strategy::Substitution
                        && a.status == AttemptStatus::Succeeded),
                "substitution heuristic should succeed"
            );
        }
        other => panic!("expected substitution integration, got {other:?}"),
    }

    let parts_expr = parse_expr("x*sin(x)").expect("parse parts case");
    let res = integrate("x", &parts_expr);
    match res {
        IntegrationResult::Integrated { result, report } => {
            assert_eq!(
                simplify_fully(result),
                simplify_parse("sin(x) - x*cos(x)"),
                "integration by parts result"
            );
            assert!(
                report
                    .attempts
                    .iter()
                    .any(|a| a.strategy == Strategy::IntegrationByParts
                        && a.status == AttemptStatus::Succeeded),
                "integration by parts heuristic should succeed"
            );
        }
        other => panic!("expected parts integration, got {other:?}"),
    }
}

#[test]
fn partial_fraction_linear_denominators() {
    let cases = vec![
        ("x/(x^2 - 1)", "1/2*log(x - 1) + 1/2*log(x + 1)"),
        ("1/((x-1)*(x-2))", "log(x - 2) - log(x - 1)"),
        ("1/(x-1)^2", "-1*(x - 1)^-1"),
        ("(2*x + 3)/(x + 1)^2", "2*log(x + 1) - (x + 1)^-1"),
        ("x^2/(x-1)", "1/2*x^2 + x + log(x - 1)"),
    ];

    for (input, expected) in cases {
        let expr = parse_expr(input).expect("parse rational");
        let res = integrate("x", &expr);
        match res {
            IntegrationResult::Integrated { result, report } => {
                assert_eq!(
                    simplify_fully(result),
                    simplify_parse(expected),
                    "partial fraction integral for {input}"
                );
                assert!(
                    matches!(report.kind, IntegrandKind::Rational { .. }),
                    "kind should be rational for {input}"
                );
            }
            other => panic!("expected integration for {input}, got {other:?}"),
        }
    }
}

#[test]
fn flags_non_elementary_inputs() {
    let exp_square = parse_expr("exp(x^2)").expect("parse exp square");
    let res = integrate("x", &exp_square);
    match res {
        IntegrationResult::NotIntegrable(report) => {
            assert_eq!(
                report.reason,
                Some(ReasonCode::NonElementary(
                    NonElementaryKind::ExpOfPolynomial
                ))
            );
        }
        other => panic!("expected non-elementary classification, got {other:?}"),
    }

    let trig_over_arg = parse_expr("sin(x)/x").expect("parse trig over arg");
    let res = integrate("x", &trig_over_arg);
    match res {
        IntegrationResult::NotIntegrable(report) => {
            assert_eq!(
                report.reason,
                Some(ReasonCode::NonElementary(
                    NonElementaryKind::TrigOverArgument
                ))
            );
        }
        other => panic!("expected trig/x non-elementary flag, got {other:?}"),
    }

    let res_other_var = integrate("y", &exp_square);
    match res_other_var {
        IntegrationResult::Integrated { result, .. } => {
            assert_eq!(
                simplify_fully(result),
                simplify_parse("y*exp(x^2)"),
                "treat exp(x^2) as constant when integrating wrt y"
            );
        }
        other => panic!("expected constant-wrt-other-var integration, got {other:?}"),
    }
}

#[test]
fn integrates_constants_wrt_other_var() {
    let expr = parse_expr("x*sin(x)").expect("parse constant wrt y");
    let res = integrate("y", &expr);
    match res {
        IntegrationResult::Integrated { result, .. } => {
            assert_eq!(
                simplify_fully(result),
                simplify_parse("x*sin(x)*y"),
                "treat x*sin(x) as constant when integrating wrt y"
            );
        }
        other => panic!("expected integration treating expression as constant, got {other:?}"),
    }
}

#[test]
fn polynomial_trivial_suite() {
    let cases = vec![
        ("x", "1/2*x^2"),
        ("x^2", "1/3*x^3"),
        ("x^3", "1/4*x^4"),
        ("x^4", "1/5*x^5"),
        ("x^5", "1/6*x^6"),
        ("3*x", "3/2*x^2"),
        ("5*x^2", "5/3*x^3"),
        ("7*x^3", "7/4*x^4"),
        ("x/2", "1/4*x^2"),
        ("1/2 * x^3", "1/8*x^4"),
        ("-2*x^2", "-2/3*x^3"),
        ("-5", "-5*x"),
        ("0", "0"),
        ("2 + 3*x", "2*x + 3/2*x^2"),
        ("x + x", "x^2"),
        ("4*x^2 + 6*x + 8", "4/3*x^3 + 3*x^2 + 8*x"),
        ("x^0", "x"),
        ("x^1 + 1", "1/2*x^2 + x"),
        ("10*x^3 - 5*x + 1", "5/2*x^4 - 5/2*x^2 + x"),
        ("2*(x^2 + 1)", "2/3*x^3 + 2*x"),
        ("(x+1)^2", "1/3*x^3 + x^2 + x"),
        ("(3*x)^2", "3*x^3"),
        ("x + 2*x^2 + 3*x^3", "1/2*x^2 + 2/3*x^3 + 3/4*x^4"),
        ("5*x^4 + 4*x^2 + 3", "x^5 + 4/3*x^3 + 3*x"),
        ("12*x^2 - 8*x + 4", "4*x^3 - 4*x^2 + 4*x"),
    ];

    assert_eq!(cases.len(), 25, "expected 25 trivial cases");
    for (input, expected) in cases {
        assert_polynomial_integral(input, expected);
    }
}

#[test]
fn polynomial_nontrivial_suite() {
    let expected_forms = vec![
        ("x^-1", "log(x)"),
        ("(3*x + 4)^-1", "1/3*log(3*x + 4)"),
        ("(5*x - 7)^-2", "-1/5*(5*x - 7)^-1"),
        ("2*(3*x + 1)^-1", "2/3*log(3*x + 1)"),
        ("(2*x + 3)^(1/2)", "1/3*(2*x + 3)^(3/2)"),
        ("(4*x - 1)^(-1/2)", "1/2*(4*x - 1)^(1/2)"),
    ];

    assert_eq!(expected_forms.len(), 6, "expected form cases");
    for (input, expected) in expected_forms {
        assert_polynomial_integral(input, expected);
    }

    let roundtrip_cases = vec![
        "(2*x-3)^5",
        "(x+1)*(x-2)^3",
        "(x-1)*(x-2)*(x-3)",
        "(2*x+5)*(3*x-1)",
        "(x+1)^4",
        "2*(x+1)^3",
        "x*(x+1)^2",
        "y*x^2",
        "(y+1)*x^3",
        "(2*y-3)*x^2",
        "(a+b)*x",
        "(x+1)*(x+2)*(x+3)",
        "(x^2 + 2*x + 1)*(x+1)",
        "3*(2*x-1)^2*(x+4)",
        "(x-1)^2*(x+2)^2",
        "x^3*(x-1)*(x+2)",
        "((x+1)*(x+2))^2",
        "(x+1)^2*(x+2)^2*(x+3)",
        "(2*x-1)*(x+2)*(x-3)*(x+4)",
    ];

    assert_eq!(roundtrip_cases.len(), 19, "expected roundtrip cases");
    for input in roundtrip_cases {
        assert_polynomial_roundtrip(input);
    }
}
