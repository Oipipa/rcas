use num_traits::{One, ToPrimitive, Zero};
use rcas::{
    AttemptStatus, Expr, IntegrandKind, IntegrationResult, NonElementaryKind, Rational, ReasonCode,
    Strategy, differentiate, integrate, parse_expr, simplify_fully, sub,
};

fn simplify_parse(input: &str) -> rcas::Expr {
    simplify_fully(parse_expr(input).expect("parse input"))
}

fn contains_var(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Variable(v) => v == var,
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Pow(a, b) => contains_var(a, var) || contains_var(b, var),
        Expr::Neg(inner)
        | Expr::Sin(inner)
        | Expr::Cos(inner)
        | Expr::Tan(inner)
        | Expr::Atan(inner)
        | Expr::Asin(inner)
        | Expr::Acos(inner)
        | Expr::Exp(inner)
        | Expr::Log(inner)
        | Expr::Abs(inner) => contains_var(inner, var),
        Expr::Constant(_) => false,
    }
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

fn assert_rational_integral(input: &str, expected: &str) {
    let expr = simplify_parse(input);
    let expected_expr = simplify_parse(expected);
    match integrate("x", &expr) {
        IntegrationResult::Integrated { result, report } => {
            assert!(
                matches!(report.kind, IntegrandKind::Rational { .. }),
                "integrand kind for {input}: {:?}",
                report.kind
            );
            assert_eq!(
                simplify_fully(result),
                expected_expr,
                "integral of {input} should match expected form"
            );
        }
        other => panic!("expected rational integration for {input}, got {other:?}"),
    }
}

fn eval_expr_f64(expr: &Expr, var: &str, x: f64) -> f64 {
    eval_expr_f64_with_default(expr, var, x, 0.0).expect("evaluate expression")
}

fn eval_expr_f64_with_default(
    expr: &Expr,
    var: &str,
    x: f64,
    default_other: f64,
) -> Option<f64> {
    match expr {
        Expr::Constant(c) => c.to_f64(),
        Expr::Variable(v) => {
            if v == var {
                Some(x)
            } else {
                Some(default_other)
            }
        }
        Expr::Add(a, b) => {
            Some(eval_expr_f64_with_default(a, var, x, default_other)? + eval_expr_f64_with_default(b, var, x, default_other)?)
        }
        Expr::Sub(a, b) => {
            Some(eval_expr_f64_with_default(a, var, x, default_other)? - eval_expr_f64_with_default(b, var, x, default_other)?)
        }
        Expr::Mul(a, b) => {
            Some(eval_expr_f64_with_default(a, var, x, default_other)? * eval_expr_f64_with_default(b, var, x, default_other)?)
        }
        Expr::Div(a, b) => {
            Some(
                eval_expr_f64_with_default(a, var, x, default_other)?
                    / eval_expr_f64_with_default(b, var, x, default_other)?,
            )
        }
        Expr::Pow(base, exp) => {
            let base_val = eval_expr_f64_with_default(base, var, x, default_other)?;
            let exponent = match &**exp {
                Expr::Constant(c) => c.to_f64()?,
                _ => return None,
            };
            Some(base_val.powf(exponent))
        }
        Expr::Neg(inner) => eval_expr_f64_with_default(inner, var, x, default_other).map(|v| -v),
        Expr::Sin(inner) => eval_expr_f64_with_default(inner, var, x, default_other).map(f64::sin),
        Expr::Cos(inner) => eval_expr_f64_with_default(inner, var, x, default_other).map(f64::cos),
        Expr::Tan(inner) => eval_expr_f64_with_default(inner, var, x, default_other).map(f64::tan),
        Expr::Atan(inner) => eval_expr_f64_with_default(inner, var, x, default_other).map(f64::atan),
        Expr::Asin(inner) => eval_expr_f64_with_default(inner, var, x, default_other).map(f64::asin),
        Expr::Acos(inner) => eval_expr_f64_with_default(inner, var, x, default_other).map(f64::acos),
        Expr::Exp(inner) => eval_expr_f64_with_default(inner, var, x, default_other).map(f64::exp),
        Expr::Log(inner) => {
            Some(
                eval_expr_f64_with_default(inner, var, x, default_other)?
                    .abs()
                    .ln(),
            )
        }
        Expr::Abs(inner) => eval_expr_f64_with_default(inner, var, x, default_other).map(f64::abs),
    }
}

fn assert_integral_expected(input: &str, expected: &str) {
    let expr = parse_expr(input).expect("parse expected integral input");
    let expected_expr = simplify_parse(expected);
    match integrate("x", &expr) {
        IntegrationResult::Integrated { result, .. } => {
            assert_eq!(
                simplify_fully(result),
                expected_expr,
                "integral of {input}"
            );
        }
        other => panic!("expected integration for {input}, got {other:?}"),
    }
}

fn assert_numeric_roundtrip(input: &str, samples: &[f64]) {
    let expr = parse_expr(input).expect("parse roundtrip input");
    match integrate("x", &expr) {
        IntegrationResult::Integrated { result, .. } => {
            let derivative = simplify_fully(differentiate("x", &result));
            let target = simplify_fully(expr);
            for &sample in samples {
                let lhs = eval_expr_f64(&derivative, "x", sample);
                let rhs = eval_expr_f64(&target, "x", sample);
                let delta = (lhs - rhs).abs();
                assert!(
                    delta < 1e-6,
                    "roundtrip failure for {input} at x={sample}: {delta}"
                );
            }
        }
        other => panic!("expected integration for {input}, got {other:?}"),
    }
}

fn assert_integral_with_var(var: &str, input: &str, expected: &str) {
    let expr = parse_expr(input).expect("parse expected integral input");
    let expected_expr = simplify_parse(expected);
    match integrate(var, &expr) {
        IntegrationResult::Integrated { result, .. } => {
            let simplified_result = simplify_fully(result);
            if simplified_result != expected_expr {
                let delta = simplify_fully(sub(simplified_result.clone(), expected_expr.clone()));
                let samples = [-1.5, -0.75, 0.5, 1.25, 2.0];
                let default_other = 1.3;
                let mut baseline: Option<f64> = None;
                for s in samples {
                    let val =
                        eval_expr_f64_with_default(&delta, var, s, default_other).unwrap();
                    if let Some(b) = baseline {
                        if (val - b).abs() > 1e-6 {
                            assert!(
                                val.abs() < 1e-6,
                                "integral mismatch for {input} wrt {var}: delta={delta:?} at {s}"
                            );
                        }
                    } else {
                        baseline = Some(val);
                    }
                }
            }
        }
        other => panic!("expected integration for {input} wrt {var}, got {other:?}"),
    }
}

fn assert_parts_expected(input: &str, expected: &str) {
    let expr = parse_expr(input).expect("parse parts input");
    let expected_expr = simplify_parse(expected);
    match integrate("x", &expr) {
        IntegrationResult::Integrated { result, report } => {
            assert_eq!(
                simplify_fully(result),
                expected_expr,
                "integration by parts result for {input}"
            );
            assert!(
                report
                    .attempts
                    .iter()
                    .any(|a| a.strategy == Strategy::IntegrationByParts
                        && a.status == AttemptStatus::Succeeded),
                "parts strategy should be marked succeeded for {input}"
            );
        }
        other => panic!("expected integration for {input}, got {other:?}"),
    }
}

fn assert_parts_roundtrip(input: &str, samples: &[f64]) {
    let expr = parse_expr(input).expect("parse parts input");
    match integrate("x", &expr) {
        IntegrationResult::Integrated { result, report } => {
            assert!(
                report
                    .attempts
                    .iter()
                    .any(|a| a.strategy == Strategy::IntegrationByParts
                        && a.status == AttemptStatus::Succeeded),
                "parts strategy should succeed for {input}"
            );
            let derivative = simplify_fully(differentiate("x", &result));
            let target = simplify_fully(expr);
            for &sample in samples {
                let lhs = eval_expr_f64(&derivative, "x", sample);
                let rhs = eval_expr_f64(&target, "x", sample);
                let delta = (lhs - rhs).abs();
                assert!(
                    delta < 1e-6,
                    "roundtrip failure for {input} at x={sample}: {delta}"
                );
            }
        }
        other => panic!("expected integration for {input}, got {other:?}"),
    }
}

fn assert_rational_roundtrip(input: &str, samples: &[f64]) {
    let expr = simplify_parse(input);
    match integrate("x", &expr) {
        IntegrationResult::Integrated { result, report } => {
            assert!(
                matches!(report.kind, IntegrandKind::Rational { .. }),
                "integrand kind for {input}"
            );
            let derivative = simplify_fully(differentiate("x", &result));
            let target = simplify_fully(expr);
            for &sample in samples {
                let lhs = eval_expr_f64(&derivative, "x", sample);
                let rhs = eval_expr_f64(&target, "x", sample);
                let delta = (lhs - rhs).abs();
                assert!(
                    delta < 1e-8,
                    "roundtrip diff for {input} at x={sample} -> {delta}"
                );
            }
        }
        other => panic!("expected rational integration for {input}, got {other:?}"),
    }
}

fn assert_substitution_integral(input: &str, expected: &str) {
    let expr = parse_expr(input).expect("parse substitution input");
    let expected_expr = simplify_parse(expected);
    match integrate("x", &expr) {
        IntegrationResult::Integrated { result, report } => {
            let simplified_result = simplify_fully(result);
            if simplified_result != expected_expr {
                let delta = simplify_fully(sub(simplified_result.clone(), expected_expr.clone()));
                if contains_var(&delta, "x") {
                    let samples = [-2.0, -1.0, 0.0, 1.0, 2.0];
                    let mut baseline: Option<f64> = None;
                    for s in samples {
                        let dv = eval_expr_f64(&delta, "x", s);
                        if let Some(b) = baseline {
                            if (dv - b).abs() > 1e-6 {
                                panic!(
                                    "substitution integral mismatch for {input}: got {simplified_result}, expected {expected_expr}"
                                );
                            }
                        } else {
                            baseline = Some(dv);
                        }
                    }
                }
            }
            let sub_success = report.attempts.iter().any(|a| {
                a.strategy == Strategy::Substitution && a.status == AttemptStatus::Succeeded
            });
            if !sub_success {
                assert!(
                    report
                        .attempts
                        .iter()
                        .any(|a| a.strategy == Strategy::Direct
                            && a.status == AttemptStatus::Succeeded),
                    "expected either substitution or direct success recorded for {input}"
                );
            }
        }
        other => panic!("expected substitution integration for {input}, got {other:?}"),
    }
}

fn assert_non_elementary(input: &str, expected: NonElementaryKind) {
    let expr = parse_expr(input).expect("parse non-elementary input");
    let expected_kind = expected.clone();
    let expected_reason = ReasonCode::NonElementary(expected);
    match integrate("x", &expr) {
        IntegrationResult::NotIntegrable(report) => {
            assert_eq!(
                report.kind,
                IntegrandKind::NonElementary(expected_kind),
                "non-elementary kind for {input}"
            );
            assert_eq!(
                report.reason,
                Some(expected_reason),
                "non-elementary reason for {input}"
            );
            assert!(
                report.attempts.iter().any(|a| a.strategy == Strategy::RischLite),
                "risch-lite should be recorded for {input}"
            );
            assert!(
                report.attempts.iter().any(|a| a.strategy == Strategy::MeijerG),
                "meijer-g should be recorded for {input}"
            );
        }
        other => panic!("expected non-elementary classification for {input}, got {other:?}"),
    }
}

fn assert_risch_lite_integral(input: &str, expected: &str) {
    let expr = parse_expr(input).expect("parse risch-lite input");
    let expected_expr = simplify_parse(expected);
    match integrate("x", &expr) {
        IntegrationResult::Integrated { result, report } => {
            assert_eq!(
                simplify_fully(result),
                expected_expr,
                "risch-lite integral for {input}"
            );
            let attempt = report
                .attempts
                .iter()
                .find(|a| a.strategy == Strategy::RischLite)
                .expect("risch-lite attempt");
            assert_eq!(
                attempt.status,
                AttemptStatus::Succeeded,
                "risch-lite should succeed for {input}"
            );
            let note = attempt.note.as_deref().unwrap_or("");
            assert!(
                note.contains("determinate"),
                "risch-lite should report determinate for {input}"
            );
        }
        other => panic!("expected integration for {input}, got {other:?}"),
    }
}

fn assert_risch_lite_non_elementary(input: &str, expected: NonElementaryKind) {
    let expr = parse_expr(input).expect("parse non-elementary input");
    let expected_kind = expected.clone();
    let expected_reason = ReasonCode::NonElementary(expected.clone());
    match integrate("x", &expr) {
        IntegrationResult::NotIntegrable(report) => {
            assert_eq!(
                report.kind,
                IntegrandKind::NonElementary(expected_kind),
                "non-elementary kind for {input}"
            );
            assert_eq!(
                report.reason,
                Some(expected_reason),
                "non-elementary reason for {input}"
            );
            let attempt = report
                .attempts
                .iter()
                .find(|a| a.strategy == Strategy::RischLite)
                .expect("risch-lite attempt");
            assert!(
                matches!(
                    attempt.status,
                    AttemptStatus::Failed(ReasonCode::NonElementary(ref kind))
                        if kind == &expected
                ),
                "risch-lite should record non-elementary for {input}"
            );
            let note = attempt.note.as_deref().unwrap_or("");
            assert!(
                note.contains("determinate"),
                "risch-lite should report determinate for {input}"
            );
        }
        other => panic!("expected non-elementary classification for {input}, got {other:?}"),
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
                simplify_parse("2*x + log(abs(x+1))"),
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
            simplify_parse("((2*x + 3)*log(abs(2*x + 3)) - (2*x + 3)) / 2"),
            "log(kx+b) should use linear-change-of-variables formula"
        ),
        other => panic!("expected log linear integration, got {other:?}"),
    }

    let inv_x = parse_expr("x^-1").expect("parse x^-1");
    let inv_res = integrate("x", &inv_x);
    match inv_res {
        IntegrationResult::Integrated { result, .. } => assert_eq!(
            simplify_fully(result),
            simplify_parse("log(abs(x))"),
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
        (
            "x/(x^2 - 1)",
            "1/2*log(abs(x - 1)) + 1/2*log(abs(x + 1))",
        ),
        (
            "1/((x-1)*(x-2))",
            "log(abs(x - 2)) - log(abs(x - 1))",
        ),
        ("1/(x-1)^2", "-1*(x - 1)^-1"),
        ("(2*x + 3)/(x + 1)^2", "2*log(abs(x + 1)) - (x + 1)^-1"),
        ("x^2/(x-1)", "1/2*x^2 + x + log(abs(x - 1))"),
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
fn non_elementary_classification_trivial() {
    let cases = vec![
        ("exp(x^2)", NonElementaryKind::ExpOfPolynomial),
        ("exp(x^2 + 1)", NonElementaryKind::ExpOfPolynomial),
        ("exp(x^2 + x)", NonElementaryKind::ExpOfPolynomial),
        ("exp(3*x^2 + 2*x + 1)", NonElementaryKind::ExpOfPolynomial),
        ("exp((x+1)^2)", NonElementaryKind::ExpOfPolynomial),
        ("exp((x-1)^2)", NonElementaryKind::ExpOfPolynomial),
        ("exp((2*x+3)^2)", NonElementaryKind::ExpOfPolynomial),
        ("exp((x+2)*(x+1))", NonElementaryKind::ExpOfPolynomial),
        ("exp((x+1)^2 + x)", NonElementaryKind::ExpOfPolynomial),
        ("exp((x+1)^2 + 3)", NonElementaryKind::ExpOfPolynomial),
        ("exp(x^2 - 4*x + 4)", NonElementaryKind::ExpOfPolynomial),
        ("exp((x-2)*(x-2))", NonElementaryKind::ExpOfPolynomial),
        ("sin(x)/x", NonElementaryKind::TrigOverArgument),
        ("sin(2*x)/(2*x)", NonElementaryKind::TrigOverArgument),
        ("sin(x+1)/(x+1)", NonElementaryKind::TrigOverArgument),
        ("sin(3*x - 1)/(3*x - 1)", NonElementaryKind::TrigOverArgument),
        ("sin(-x)/x", NonElementaryKind::TrigOverArgument),
        ("sin(x)/(-x)", NonElementaryKind::TrigOverArgument),
        ("sin(5*x)/(5*x)", NonElementaryKind::TrigOverArgument),
        ("cos(x)/x", NonElementaryKind::TrigOverArgument),
        ("cos(2*x)/(2*x)", NonElementaryKind::TrigOverArgument),
        ("cos(x+1)/(x+1)", NonElementaryKind::TrigOverArgument),
        ("cos(3*x - 1)/(3*x - 1)", NonElementaryKind::TrigOverArgument),
        ("cos(-x)/x", NonElementaryKind::TrigOverArgument),
        ("cos(x)/(-x)", NonElementaryKind::TrigOverArgument),
    ];

    assert_eq!(cases.len(), 25, "expected 25 trivial non-elementary cases");
    for (input, expected) in cases {
        assert_non_elementary(input, expected);
    }
}

#[test]
fn non_elementary_classification_non_trivial() {
    let cases = vec![
        ("exp(x^3)", NonElementaryKind::ExpOfPolynomial),
        ("exp(x^3 + x)", NonElementaryKind::ExpOfPolynomial),
        ("exp(x^4 - 2*x^2)", NonElementaryKind::ExpOfPolynomial),
        ("exp((x+1)^3)", NonElementaryKind::ExpOfPolynomial),
        ("exp((2*x-1)^3)", NonElementaryKind::ExpOfPolynomial),
        ("2*exp(x^3)", NonElementaryKind::ExpOfPolynomial),
        ("y*exp(x^3)", NonElementaryKind::ExpOfPolynomial),
        ("x^x", NonElementaryKind::PowerSelf),
        ("2*x^x", NonElementaryKind::PowerSelf),
        ("-1*x^x", NonElementaryKind::PowerSelf),
        ("x^x/2", NonElementaryKind::PowerSelf),
        ("y*x^x", NonElementaryKind::PowerSelf),
        ("x^x*y", NonElementaryKind::PowerSelf),
        ("x^x*log(x)", NonElementaryKind::PowerSelfLog),
        ("log(x)*x^x", NonElementaryKind::PowerSelfLog),
        ("2*x^x*log(x)", NonElementaryKind::PowerSelfLog),
        ("x^x*log(x)/3", NonElementaryKind::PowerSelfLog),
        ("y*x^x*log(x)", NonElementaryKind::PowerSelfLog),
        ("x^x*log(x)*y", NonElementaryKind::PowerSelfLog),
        (
            "sin(x^2)/x^2",
            NonElementaryKind::TrigOverPolynomialArgument,
        ),
        (
            "cos(x^2)/x^2",
            NonElementaryKind::TrigOverPolynomialArgument,
        ),
        (
            "sin((x+1)^2)/(x+1)^2",
            NonElementaryKind::TrigOverPolynomialArgument,
        ),
        (
            "cos((x-2)^2)/(x-2)^2",
            NonElementaryKind::TrigOverPolynomialArgument,
        ),
        (
            "sin(2*x^2)/(2*x^2)",
            NonElementaryKind::TrigOverPolynomialArgument,
        ),
        (
            "cos(3*x^2)/(3*x^2)",
            NonElementaryKind::TrigOverPolynomialArgument,
        ),
    ];

    assert_eq!(cases.len(), 25, "expected 25 non-trivial non-elementary cases");
    for (input, expected) in cases {
        assert_non_elementary(input, expected);
    }
}

#[test]
fn non_elementary_detection_allows_substitution_cases() {
    let cases = vec![
        ("x", "2*x*exp(x^2)", "exp(x^2)"),
        ("x", "2*x*sin(x^2)", "-cos(x^2)"),
        ("x", "2*x*cos(x^2)", "sin(x^2)"),
    ];

    for (var, input, expected) in cases {
        assert_integral_with_var(var, input, expected);
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
fn substitution_preserves_constants_from_other_vars() {
    let expr = parse_expr("x*sin(y)").expect("parse cross-var substitution case");
    let res = integrate("y", &expr);
    match res {
        IntegrationResult::Integrated { result, report } => {
            assert_eq!(
                simplify_fully(result),
                simplify_parse("-x*cos(y)"),
                "constants independent of integration variable should be preserved"
            );
            assert!(
                report.attempts.iter().any(|a| {
                    (a.strategy == Strategy::Substitution || a.strategy == Strategy::Direct)
                        && a.status == AttemptStatus::Succeeded
                }),
                "substitution or direct strategy should succeed"
            );
        }
        other => panic!("expected integration for x*sin(y) wrt y, got {other:?}"),
    }
}

#[test]
fn odd_and_cross_variable_integrals() {
    let cases: Vec<(&str, &str, &str)> = vec![
        ("y", "sin(y/x)", "-x*cos(y/x)"),
        ("y", "y*sin(y/x)", "x^2*sin(y/x) - x*y*cos(y/x)"),
        ("y", "cos(y/x)/x", "sin(y/x)"),
        ("y", "exp((y + 1)/x)", "x*exp((y + 1)/x)"),
        ("y", "tan(y/x)/x", "-log(abs(cos(y/x)))"),
        (
            "y",
            "(2*y + 3)/(y^2 + 3*y + 5)",
            "log(abs(y^2 + 3*y + 5))",
        ),
        (
            "y",
            "(6*y - 4)/(3*y^2 - 4*y + 7)",
            "log(abs(3*y^2 - 4*y + 7))",
        ),
        ("y", "(2*y + 1)/(y^2 + y)", "log(abs(y^2 + y))"),
        ("y", "(4*y + 1)/(2*y^2 + y + 1)", "log(abs(2*y^2 + y + 1))"),
        (
            "y",
            "(2*y + 2)/(y^2 + 2*y + 1)",
            "log(abs(y^2 + 2*y + 1))",
        ),
        ("y", "exp(x)*sin(y)", "-exp(x)*cos(y)"),
        ("y", "(x + 1)*cos(y)", "(x + 1)*sin(y)"),
        ("x", "sin(x/y)", "-y*cos(x/y)"),
        ("x", "cos(x/y)/y", "sin(x/y)"),
        ("x", "exp((2*x + 1)/y)", "1/2*y*exp((2*x + 1)/y)"),
        (
            "x",
            "tan((3*x - 1)/y)",
            "-1/3*y*log(abs(cos((3*x - 1)/y)))",
        ),
        (
            "x",
            "(4*x + 5)/(2*x^2 + 5*x + 7)",
            "log(abs(2*x^2 + 5*x + 7))",
        ),
        (
            "x",
            "(2*x - 3)/(x^2 - 3*x + 4)",
            "log(abs(x^2 - 3*x + 4))",
        ),
        (
            "x",
            "(6*x + 4)/(3*x^2 + 4*x + 1)",
            "log(abs(3*x^2 + 4*x + 1))",
        ),
        ("x", "(x + 1)/(1/2*x^2 + x)", "log(abs(1/2*x^2 + x))"),
        ("y", "(3*y^2 + 2)*exp(y^3 + 2*y)", "exp(y^3 + 2*y)"),
        ("y", "(3*y^2 + 2)*sin(y^3 + 2*y)", "-cos(y^3 + 2*y)"),
        ("y", "(3*y^2 + 2)*cos(y^3 + 2*y)", "sin(y^3 + 2*y)"),
        (
            "y",
            "(3*y^2 + 2)*log(y^3 + 2*y)",
            "((y^3 + 2*y)*log(abs(y^3 + 2*y)) - (y^3 + 2*y))",
        ),
        ("y", "(3*y^2 + 2)*(y^3 + 2*y)^2", "1/3*(y^3 + 2*y)^3"),
        ("y", "(3*y^2 + 2)*(y^3 + 2*y)^-2", "-1*(y^3 + 2*y)^-1"),
        ("x", "(2*x + 1)*exp(x^2 + x)", "exp(x^2 + x)"),
        ("x", "(2*x + 1)*sin(x^2 + x)", "-cos(x^2 + x)"),
        ("x", "(2*x + 1)/(x^2 + x)", "log(abs(x^2 + x))"),
        ("x", "(2*x + 1)*(x^2 + x)^3", "1/4*(x^2 + x)^4"),
        ("y", "y^2 + 2*x*y + x^2", "1/3*y^3 + x*y^2 + x^2*y"),
        ("x", "x^2 + 3*y*x + 2*y^2", "1/3*x^3 + 3/2*y*x^2 + 2*y^2*x"),
        ("y", "(y + x)^-1", "log(abs(y + x))"),
        ("x", "(x + y)^-2", "-1*(x + y)^-1"),
        ("y", "sin(2*y + x)", "-1/2*cos(2*y + x)"),
        ("y", "cos(3*y - x)", "1/3*sin(3*y - x)"),
        ("x", "exp(5*x - 2*y)", "1/5*exp(5*x - 2*y)"),
        ("x", "sin(4*x + y)", "-1/4*cos(4*x + y)"),
        ("x", "cos(4*x + y)", "1/4*sin(4*x + y)"),
        ("x", "tan(2*x - y)", "-1/2*log(abs(cos(2*x - y)))"),
        ("y", "tan(3*y + x)", "-1/3*log(abs(cos(3*y + x)))"),
    ];

    assert_eq!(cases.len(), 41, "expected 41 odd cases");
    for (var, input, expected) in cases {
        assert_integral_with_var(var, input, expected);
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
        ("x^-1", "log(abs(x))"),
        ("(3*x + 4)^-1", "1/3*log(abs(3*x + 4))"),
        ("(5*x - 7)^-2", "-1/5*(5*x - 7)^-1"),
        ("2*(3*x + 1)^-1", "2/3*log(abs(3*x + 1))"),
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

#[test]
fn rational_trivial_suite() {
    let cases = vec![
        ("1/(x + 1)", "log(abs(x + 1))"),
        ("3/(2*x + 1)", "3/2*log(abs(x + 1/2))"),
        ("(x + 2)/(x + 1)", "x + log(abs(x + 1))"),
        ("(2*x + 3)/(x + 1)", "2*x + log(abs(x + 1))"),
        ("(x - 1)/x", "x - log(abs(x))"),
        ("5/(x - 2)", "5*log(abs(x - 2))"),
        ("-4/(3*x - 1)", "-4/3*log(abs(x - 1/3))"),
        ("1/(x - 1)^2", "-1*(x - 1)^-1"),
        (
            "(2*x + 1)/(x - 3)^2",
            "2*log(abs(x - 3)) - (7)*(x - 3)^-1",
        ),
        ("(x^2 + 1)/x", "1/2*x^2 + log(abs(x))"),
        ("(x^2 + 2*x)/x", "1/2*x^2 + 2*x"),
        (
            "(3*x^2 + 5*x + 2)/(x + 2)",
            "3/2*x^2 - x + 4*log(abs(x + 2))",
        ),
        (
            "x/(x^2 - 4)",
            "1/2*log(abs(x - 2)) + 1/2*log(abs(x + 2))",
        ),
        (
            "1/((x + 1)*(x + 2))",
            "log(abs(x + 1)) - log(abs(x + 2))",
        ),
        ("2/(x^2 - 1)", "log(abs(x - 1)) - log(abs(x + 1))"),
        ("(x + 1)/(x*(x + 1))", "log(abs(x))"),
        ("5/(x^2 + 2*x + 1)", "-5*(x + 1)^-1"),
        ("(4*x + 6)/(2*x + 3)", "2*x"),
        ("(2*x + 1)/(2*x + 3)", "x - log(abs(x + 3/2))"),
        ("(-3*x + 5)/(x - 4)", "-3*x - 7*log(abs(x - 4))"),
        ("(x^3 + x)/(x^2 + 1)", "1/2*x^2"),
        ("(x^2 + 4*x + 4)/(x + 2)", "1/2*x^2 + 2*x"),
        (
            "(2*x^2 + 3*x + 4)/(x + 1)",
            "x^2 + x + 3*log(abs(x + 1))",
        ),
        ("(x + 4)/(x - 1)", "x + 5*log(abs(x - 1))"),
        ("7/(5*x - 2)", "7/5*log(abs(x - 2/5))"),
    ];

    assert_eq!(cases.len(), 25, "expected 25 trivial rational cases");
    for (input, expected) in cases {
        assert_rational_integral(input, expected);
    }
}

#[test]
fn rational_nontrivial_suite() {
    let expected_cases = vec![
        (
            "1/(x^2 + 1)",
            "2/(4)^(1/2)*arctan((2*x)/(4)^(1/2))",
        ),
        (
            "1/(x^2 + x + 1)",
            "2/(3)^(1/2)*arctan((2*x + 1)/(3)^(1/2))",
        ),
        (
            "(2*x + 5)/(x^2 + 4*x + 5)",
            "log(abs(x^2 + 4*x + 5)) + 2/(4)^(1/2)*arctan((2*x + 4)/(4)^(1/2))",
        ),
        (
            "(3*x + 1)/(x^2 + 2)",
            "3/2*log(abs(x^2 + 2)) + 2/(8)^(1/2)*arctan((2*x)/(8)^(1/2))",
        ),
        (
            "(x + 1)/(x^2 + 4)",
            "1/2*log(abs(x^2 + 4)) + 2/(16)^(1/2)*arctan((2*x)/(16)^(1/2))",
        ),
        ("x/(x^2 + 1)^2", "-1/2*(x^2 + 1)^-1"),
        (
            "1/(x^2 + 1)^2",
            "1/(4)^(1/2)*arctan((2*x)/(4)^(1/2)) + 2*x/(4*x^2 + 4)",
        ),
        (
            "1/((x + 1)*(x^2 + 1))",
            "1/2*log(abs(x + 1)) - 1/4*log(abs(x^2 + 1)) + 1/(4)^(1/2)*arctan((2*x)/(4)^(1/2))",
        ),
        (
            "(x - 1)/(x^2 + x + 1)",
            "1/2*log(abs(x^2 + x + 1)) - 3/(3)^(1/2)*arctan((2*x + 1)/(3)^(1/2))",
        ),
        (
            "x/(x^2 + 2*x + 2)",
            "1/2*log(abs(x^2 + 2*x + 2)) - 2/(4)^(1/2)*arctan((2*x + 2)/(4)^(1/2))",
        ),
        (
            "(x + 3)/(x^2 + 6*x + 13)",
            "1/2*log(abs(x^2 + 6*x + 13))",
        ),
        (
            "(2*x + 3)/(x^2 + 4)",
            "log(abs(x^2 + 4)) + 6/(16)^(1/2)*arctan((2*x)/(16)^(1/2))",
        ),
    ];

    let roundtrip_cases: Vec<(&str, Vec<f64>)> = vec![
        ("(3*x^2 + 5*x + 7)/(x^2 + 1)", vec![-1.1, -0.3, 0.8, 1.5]),
        ("(x^3 + 2*x)/(x^2 + 1)", vec![-1.3, -0.4, 0.9, 1.7]),
        ("(x^2 + 2*x + 2)/((x + 1)^2)", vec![0.5, 1.5, 2.5]),
        ("(x^2 + 1)/(x + 1)^3", vec![0.5, 1.0, 2.0]),
        ("(x + 2)/((x - 1)*(x^2 + 4))", vec![1.5, 2.5, 3.5]),
        (
            "(2*x + 3)/((x - 2)^2*(x^2 + 1))",
            vec![2.5, 3.0, 4.0],
        ),
        ("(x^4 + 1)/(x^2 + 1)", vec![-1.2, -0.6, 0.6, 1.2]),
        ("(x^2)/(x^2 + 4)", vec![-2.5, -1.0, 1.0, 2.5]),
        ("(3*x + 1)/((x + 2)^2)", vec![-1.0, 0.5, 2.0]),
        (
            "(2*x^2 + 4*x + 5)/((x + 1)*(x^2 + 1))",
            vec![0.5, 1.5, 2.5],
        ),
        (
            "(x^2 + 3*x + 5)/(x*(x^2 + 1))",
            vec![0.5, 1.5, 2.5],
        ),
        ("(x^2 + 4)/(x^2 - 4)", vec![2.5, 3.5, 5.0]),
        ("(x^2 + 5*x + 6)/(x^2 + 1)", vec![-2.0, -1.0, 1.0, 2.0]),
    ];

    assert_eq!(
        expected_cases.len() + roundtrip_cases.len(),
        25,
        "expected 25 non-trivial rational cases"
    );

    for (input, expected) in expected_cases {
        assert_rational_integral(input, expected);
    }

    for (input, samples) in roundtrip_cases {
        assert_rational_roundtrip(input, &samples);
    }
}

#[test]
fn risch_lite_trivial_suite() {
    let cases = vec![
        (
            "1/(1+exp(x))",
            "log(abs(exp(x))) - log(abs(exp(x) + 1))",
        ),
        (
            "1/(2+exp(x))",
            "1/2*log(abs(exp(x))) - 1/2*log(abs(exp(x) + 2))",
        ),
        (
            "1/(3+exp(x))",
            "1/3*log(abs(exp(x))) - 1/3*log(abs(exp(x) + 3))",
        ),
        (
            "(exp(x)+1)/(exp(x)+2)",
            "1/2*log(abs(exp(x))) + 1/2*log(abs(exp(x) + 2))",
        ),
        (
            "(exp(x)+2)/(exp(x)+1)",
            "2*log(abs(exp(x))) - log(abs(exp(x) + 1))",
        ),
        (
            "exp(x)^2/(1+exp(x))",
            "exp(x) - log(abs(exp(x) + 1))",
        ),
        (
            "exp(x)^3/(1+exp(x))",
            "1/2*exp(x)^2 - exp(x) + log(abs(exp(x) + 1))",
        ),
        (
            "1/(1+exp(2*x))",
            "1/2*log(abs(exp(2*x))) - 1/2*log(abs(exp(2*x) + 1))",
        ),
        (
            "1/(2+exp(2*x))",
            "1/4*log(abs(exp(2*x))) - 1/4*log(abs(exp(2*x) + 2))",
        ),
        (
            "(exp(2*x)+1)/(exp(2*x)+2)",
            "1/4*log(abs(exp(2*x))) + 1/4*log(abs(exp(2*x) + 2))",
        ),
        (
            "1/(x*(1+exp(log(x))))",
            "log(abs(exp(log(x)))) - log(abs(exp(log(x)) + 1))",
        ),
        (
            "exp(log(x))^2/(x*(1+exp(log(x))))",
            "exp(log(x)) - log(abs(exp(log(x)) + 1))",
        ),
        ("(log(x) + 1)/x", "1/2*log(x)^2 + log(x)"),
        ("(2*log(x) + 3)/x", "log(x)^2 + 3*log(x)"),
        (
            "(log(x)^2 + log(x))/x",
            "1/3*log(x)^3 + 1/2*log(x)^2",
        ),
        (
            "(log(x)^2 + 2*log(x) + 1)/x",
            "1/3*log(x)^3 + log(x)^2 + log(x)",
        ),
        (
            "(log(x)^3 + log(x))/x",
            "1/4*log(x)^4 + 1/2*log(x)^2",
        ),
        (
            "((log(x) + 1)*(log(x) + 2))/x",
            "1/3*log(x)^3 + 3/2*log(x)^2 + 2*log(x)",
        ),
        (
            "((log(x) - 1)*(log(x) + 2))/x",
            "1/3*log(x)^3 + 1/2*log(x)^2 - 2*log(x)",
        ),
        (
            "(log(x)^2 + 5)/x",
            "1/3*log(x)^3 + 5*log(x)",
        ),
        (
            "(3*log(x)^2 - 2*log(x) + 4)/x",
            "log(x)^3 - log(x)^2 + 4*log(x)",
        ),
        (
            "(log(x)^4 + log(x)^2)/x",
            "1/5*log(x)^5 + 1/3*log(x)^3",
        ),
        (
            "2*(log(2*x+1) + 1)/(2*x+1)",
            "1/2*log(2*x + 1)^2 + log(2*x + 1)",
        ),
        (
            "3*(log(3*x-2) + 2)/(3*x-2)",
            "1/2*log(3*x - 2)^2 + 2*log(3*x - 2)",
        ),
        (
            "(log(4*x+1)^2 + log(4*x+1) + 1) * 4/(4*x+1)",
            "1/3*log(4*x + 1)^3 + 1/2*log(4*x + 1)^2 + log(4*x + 1)",
        ),
    ];

    assert_eq!(cases.len(), 25, "expected 25 trivial risch-lite cases");
    for (input, expected) in cases {
        assert_risch_lite_integral(input, expected);
    }
}

#[test]
fn risch_lite_non_elementary_suite() {
    let cases = vec![
        ("exp(x^2)", NonElementaryKind::ExpOfPolynomial),
        ("exp(x^2 + 2*x + 1)", NonElementaryKind::ExpOfPolynomial),
        ("exp(2*x^3 + 1)", NonElementaryKind::ExpOfPolynomial),
        ("exp((x+1)^2)", NonElementaryKind::ExpOfPolynomial),
        ("exp((2*x-3)^2)", NonElementaryKind::ExpOfPolynomial),
        ("exp(x^4 - x^2)", NonElementaryKind::ExpOfPolynomial),
        ("exp((x-1)*(x+2))", NonElementaryKind::ExpOfPolynomial),
        ("2*exp(x^3)", NonElementaryKind::ExpOfPolynomial),
        ("y*exp(x^2)", NonElementaryKind::ExpOfPolynomial),
        ("exp(3*x^5 + 2*x)", NonElementaryKind::ExpOfPolynomial),
        ("sin(x)/x", NonElementaryKind::TrigOverArgument),
        ("cos(x)/x", NonElementaryKind::TrigOverArgument),
        ("sin(2*x)/(2*x)", NonElementaryKind::TrigOverArgument),
        ("cos(3*x-1)/(3*x-1)", NonElementaryKind::TrigOverArgument),
        (
            "sin(x^2)/x^2",
            NonElementaryKind::TrigOverPolynomialArgument,
        ),
        (
            "cos(x^2)/x^2",
            NonElementaryKind::TrigOverPolynomialArgument,
        ),
        (
            "sin((x+1)^2)/(x+1)^2",
            NonElementaryKind::TrigOverPolynomialArgument,
        ),
        (
            "cos((2*x-1)^2)/(2*x-1)^2",
            NonElementaryKind::TrigOverPolynomialArgument,
        ),
        ("x^x", NonElementaryKind::PowerSelf),
        ("2*x^x", NonElementaryKind::PowerSelf),
        ("x^x/3", NonElementaryKind::PowerSelf),
        ("y*x^x", NonElementaryKind::PowerSelf),
        ("x^x*log(x)", NonElementaryKind::PowerSelfLog),
        ("2*x^x*log(x)", NonElementaryKind::PowerSelfLog),
        ("x^x*log(x)/3", NonElementaryKind::PowerSelfLog),
    ];

    assert_eq!(cases.len(), 25, "expected 25 non-trivial risch-lite cases");
    for (input, expected) in cases {
        assert_risch_lite_non_elementary(input, expected);
    }
}

#[test]
fn substitution_trivial_suite() {
    let cases = vec![
        ("2*x*exp(x^2)", "exp(x^2)"),
        ("4*x*sin(x^2)", "-2*cos(x^2)"),
        ("6*x*cos(x^2)", "3*sin(x^2)"),
        ("3*x*(x^2 + 1)^-1", "3/2*log(abs(x^2 + 1))"),
        ("5*x*(x^2 + 1)^-2", "-5/2*(x^2 + 1)^-1"),
        ("7*x*(x^2 + 1)^(1/2)", "7/3*(x^2 + 1)^(3/2)"),
        ("9*x*(x^2 + 1)^(-3/2)", "-9*(x^2 + 1)^-1/2"),
        (
            "2*x*log(x^2 + 1)",
            "(x^2 + 1)*log(abs(x^2 + 1)) - (x^2 + 1)",
        ),
        ("4*x*exp(x^2 + 1)", "2*exp(x^2 + 1)"),
        ("6*x*tan(x^2)", "-3*log(abs(cos(x^2)))"),
        ("3*(2*x + 1)*exp(x^2 + x)", "3*exp(x^2 + x)"),
        ("5*(2*x + 1)*sin(x^2 + x)", "-5*cos(x^2 + x)"),
        ("7*(2*x + 1)*cos(x^2 + x)", "7*sin(x^2 + x)"),
        ("2*(2*x + 1)*tan(x^2 + x)", "-2*log(abs(cos(x^2 + x)))"),
        (
            "4*(2*x + 1)*log(x^2 + x + 1)",
            "4*((x^2 + x + 1)*log(abs(x^2 + x + 1)) - (x^2 + x + 1))",
        ),
        (
            "6*(2*x + 3)*(x^2 + 3*x)^2*exp((x^2 + 3*x)^3)",
            "2*exp((x^2 + 3*x)^3)",
        ),
        (
            "10*x*(x^2 + 1)*exp((x^2 + 1)^2)",
            "5/2*exp((x^2 + 1)^2)",
        ),
        (
            "6*x*(x^2 + 1)*cos((x^2 + 1)^2)",
            "3/2*sin((x^2 + 1)^2)",
        ),
        (
            "8*x*(x^2 + 1)*sin((x^2 + 1)^2)",
            "-2*cos((x^2 + 1)^2)",
        ),
        (
            "8*(x^2 + 2)*(2*x)*exp((x^2 + 2)^2)",
            "4*exp((x^2 + 2)^2)",
        ),
        (
            "10*(x^2 + 2)*(2*x)*cos((x^2 + 2)^2)",
            "5*sin((x^2 + 2)^2)",
        ),
        (
            "6*(x^2 + 2)*(2*x)*sin((x^2 + 2)^2)",
            "-3*cos((x^2 + 2)^2)",
        ),
        ("9*x*(x^2 + 4)^-2", "-9/2*(x^2 + 4)^-1"),
        ("7*x*(x^2 + 4)^(-3/2)", "-7*(x^2 + 4)^-1/2"),
        ("11*x*(x^2 + 5)^(1/3)", "33/8*(x^2 + 5)^(4/3)"),
    ];

    assert_eq!(cases.len(), 25, "expected 25 trivial substitution cases");
    for (input, expected) in cases {
        assert_substitution_integral(input, expected);
    }
}

#[test]
fn parts_trivial_suite() {
    let cases = vec![
        ("x*sin(x)", "sin(x) - x*cos(x)"),
        ("x*cos(x)", "x*sin(x) + cos(x)"),
        ("x*exp(x)", "x*exp(x) - exp(x)"),
        ("x^2*exp(x)", "exp(x)*(x^2 - 2*x + 2)"),
        ("x^2*exp(2*x)", "exp(2*x)*(1/2*x^2 - 1/2*x + 1/4)"),
        ("x^2*sin(x)", "-1*x^2*cos(x) + 2*x*sin(x) + 2*cos(x)"),
        ("x^2*cos(x)", "x^2*sin(x) + 2*x*cos(x) - 2*sin(x)"),
        ("x*log(x)", "1/2*x^2*log(abs(x)) - 1/4*x^2"),
        ("x^2*log(x)", "1/3*x^3*log(abs(x)) - 1/9*x^3"),
        ("2*x*sin(x)", "2*sin(x) - 2*x*cos(x)"),
        ("3*x*cos(x)", "3*x*sin(x) + 3*cos(x)"),
        ("4*x*exp(3*x)", "exp(3*x)*((4/3)*x - 4/9)"),
        ("x*sin(2*x)", "-1/2*x*cos(2*x) + 1/4*sin(2*x)"),
        ("x*cos(3*x)", "1/3*x*sin(3*x) + 1/9*cos(3*x)"),
        ("x^3*exp(x)", "exp(x)*(x^3 - 3*x^2 + 6*x - 6)"),
        (
            "x^3*sin(x)",
            "-1*x^3*cos(x) + 3*x^2*sin(x) + 6*x*cos(x) - 6*sin(x)",
        ),
        (
            "x^3*cos(x)",
            "x^3*sin(x) + 3*x^2*cos(x) - 6*x*sin(x) - 6*cos(x)",
        ),
        ("x*exp(x + 1)", "exp(x + 1)*(x - 1)"),
        ("x*exp(2*x + 1)", "exp(2*x + 1)*(1/2*x - 1/4)"),
        ("(2*x + 1)*exp(x)", "exp(x)*(2*x - 1)"),
    ];

    assert_eq!(cases.len(), 20, "expected 20 trivial parts cases");
    for (input, expected) in cases {
        assert_parts_expected(input, expected);
    }
}

#[test]
fn parts_nontrivial_suite() {
    let cases: Vec<(&str, Vec<f64>)> = vec![
        ("(x^4 + 2*x)*exp(x)", vec![-1.0, 0.0, 1.0, 2.0]),
        ("(x^3 - x)*exp(2*x)", vec![-1.0, 0.5, 1.0]),
        ("(x^2 + 3*x + 2)*sin(x)", vec![-1.0, 0.0, 1.0]),
        ("(x^2 - 2)*cos(2*x)", vec![-1.0, 0.0, 1.5]),
        ("(3*x^2 + 2*x + 1)*exp(3*x)", vec![-0.5, 0.0, 0.5]),
        ("x^4*exp(1/2*x)", vec![-1.0, 0.0, 1.0]),
        ("x^3*cos(x + 1)", vec![-1.0, 0.5, 1.0]),
        ("x^3*sin(2*x + 1)", vec![-0.5, 0.0, 0.5]),
        ("(x^2 + 1)*exp(2*x + 3)", vec![-1.0, 0.0, 1.0]),
        ("(x^2 + 2*x)*exp(x)", vec![-1.0, 0.0, 1.0]),
        ("(x^2 + 1)*sin(x)", vec![-1.0, 0.0, 1.0]),
        ("(x^2 + 1)*cos(x)", vec![-1.0, 0.0, 1.0]),
        ("(x^3 + x)*log(x)", vec![0.5, 1.0, 2.0]),
        ("(x^2 + 2*x + 1)*log(x + 2)", vec![-1.0, 0.0, 1.0]),
        ("(x^2 + 1)*sin(3*x)", vec![-1.0, 0.0, 1.0]),
        ("(x^2 + 1)*cos(3*x)", vec![-1.0, 0.0, 1.0]),
        ("(x^3 - 2*x^2 + x)*exp(x)", vec![-0.5, 0.0, 0.5]),
        ("(2*x + 1)*x^2*sin(x)", vec![-1.0, 0.0, 1.0]),
        ("(2*x + 3)*x^2*cos(x)", vec![-1.0, 0.0, 1.0]),
        ("(x^2 + x + 1)*exp(4*x)", vec![-0.5, 0.0, 0.5]),
        ("x^4*sin(x)", vec![-1.0, 0.0, 1.0]),
        ("x^4*cos(x)", vec![-1.0, 0.0, 1.0]),
        ("(x^3 + 2*x^2 + 1)*exp(2*x + 1)", vec![-0.5, 0.0, 0.5]),
        ("(x^2 + 1)*exp(x)", vec![-1.0, 0.0, 1.0]),
        ("(x^2 + x + 1)*sin(x + 1)", vec![-1.0, 0.0, 1.0]),
        ("(x^2 + x + 1)*cos(x + 1)", vec![-1.0, 0.0, 1.0]),
        ("(x^2 + 3*x + 2)*exp(x + 2)", vec![-1.0, 0.0, 1.0]),
        ("(x^3 + 1)*exp(3*x + 1)", vec![-1.0, 0.0, 1.0]),
        ("(x^2 + x)*(x + 1)*exp(x)", vec![-0.5, 0.0, 0.5]),
        ("(x^2 + 2*x + 3)*log(x + 3)", vec![-2.0, -1.0, 0.5]),
    ];

    assert_eq!(cases.len(), 30, "expected 30 non-trivial parts cases");
    for (input, samples) in cases {
        assert_parts_roundtrip(input, &samples);
    }
}

#[test]
fn substitution_nontrivial_suite() {
    let cases = vec![
        ("4*x*(x^2 + 1)*exp((x^2 + 1)^2)", "exp((x^2 + 1)^2)"),
        ("6*x*(x^2 + 3)^2*cos((x^2 + 3)^3)", "sin((x^2 + 3)^3)"),
        ("2*(3*x^2 + 2*x)*exp(x^3 + x^2)", "2*exp(x^3 + x^2)"),
        (
            "4*x*(x^2 + 2)^3*sin((x^2 + 2)^4)",
            "-1/2*cos((x^2 + 2)^4)",
        ),
        (
            "5*(2*x + 5)*(x^2 + 5*x + 1)^-3",
            "-5/2*(x^2 + 5*x + 1)^-2",
        ),
        (
            "3*(2*x + 2)*(x^2 + 2*x + 5)^-2",
            "-3*(x^2 + 2*x + 5)^-1",
        ),
        ("6*x/(x^2 + 1)^3", "-3/2*(x^2 + 1)^-2"),
        ("8*x*(x^2 + 1)^-3", "-2*(x^2 + 1)^-2"),
        (
            "6*x*(x^2 + 1)^2*exp((x^2 + 1)^3)",
            "exp((x^2 + 1)^3)",
        ),
        (
            "4*x*(x^2 + 1)^3*cos((x^2 + 1)^4)",
            "1/2*sin((x^2 + 1)^4)",
        ),
        (
            "4*(x^2 + x)*(2*x + 1)*cos((x^2 + x)^2)",
            "2*sin((x^2 + x)^2)",
        ),
        (
            "15*(x^2 + x + 1)^4*(2*x + 1)*exp((x^2 + x + 1)^5)",
            "3*exp((x^2 + x + 1)^5)",
        ),
        (
            "6*(3*x^2 + 2*x)/(x^3 + x^2 + 1)",
            "6*log(abs(x^3 + x^2 + 1))",
        ),
        (
            "8*(3*x^2 + 2*x)*(x^3 + x^2 + 1)^2",
            "8/3*(x^3 + x^2 + 1)^3",
        ),
        (
            "4*(3*x^2 + 2*x)*cos(x^3 + x^2 + 1)",
            "4*sin(x^3 + x^2 + 1)",
        ),
        (
            "7*(3*x^2 + 2*x)*sin(x^3 + x^2 + 1)",
            "-7*cos(x^3 + x^2 + 1)",
        ),
        (
            "5*(3*x^2 + 2*x)*tan(x^3 + x^2 + 1)",
            "-5*log(abs(cos(x^3 + x^2 + 1)))",
        ),
        (
            "9*(3*x^2 + 2*x)*exp(x^3 + x^2 + 1)",
            "9*exp(x^3 + x^2 + 1)",
        ),
        (
            "3*(6*x^2 + 4*x + 1)*exp(2*x^3 + 2*x^2 + x)",
            "3*exp(2*x^3 + 2*x^2 + x)",
        ),
        (
            "2*(4*x^3 + 6*x^2 + 2*x)*cos(x^4 + 2*x^3 + x^2)",
            "2*sin(x^4 + 2*x^3 + x^2)",
        ),
        (
            "(4*x^3 + 6*x^2 + 2*x)/(x^4 + 2*x^3 + x^2)",
            "log(abs(x^4 + 2*x^3 + x^2))",
        ),
        (
            "5*(4*x^3 + 6*x^2 + 2*x)/(x^4 + 2*x^3 + x^2)",
            "5*log(abs(x^4 + 2*x^3 + x^2))",
        ),
        (
            "6*(4*x^3 + 6*x^2 + 2*x)*(x^4 + 2*x^3 + x^2)^-2",
            "-6*(x^4 + 2*x^3 + x^2)^-1",
        ),
        (
            "4*(4*x^3 + 6*x^2 + 2*x)*(x^4 + 2*x^3 + x^2)^3",
            "(x^4 + 2*x^3 + x^2)^4",
        ),
        (
            "4*(2*x + 1)*(x^2 + x + 1)^2*exp((x^2 + x + 1)^3)",
            "4/3*exp((x^2 + x + 1)^3)",
        ),
    ];

    assert_eq!(cases.len(), 25, "expected 25 non-trivial substitution cases");
    for (input, expected) in cases {
        assert_substitution_integral(input, expected);
    }
}

#[test]
fn trig_exp_log_trivial_suite() {
    let cases = vec![
        ("sin(x)^2", "1/2*x - 1/2*sin(x)*cos(x)"),
        ("cos(x)^2", "1/2*x + 1/2*sin(x)*cos(x)"),
        ("sin(x)*cos(x)", "-1/2*cos(x)^2"),
        ("sin(2*x)^2", "1/2*x - 1/4*sin(2*x)*cos(2*x)"),
        ("cos(3*x)^2", "1/2*x + 1/6*sin(3*x)*cos(3*x)"),
        ("sin(x)^3", "-1*cos(x) + 1/3*cos(x)^3"),
        ("cos(x)^3", "sin(x) - 1/3*sin(x)^3"),
        ("sin(x)^2*cos(x)", "1/3*sin(x)^3"),
        ("sin(x)*cos(x)^2", "-1/3*cos(x)^3"),
        ("sin(x)^2*cos(x)^2", "1/8*x - 1/32*sin(4*x)"),
        ("tan(x)", "-1*log(abs(cos(x)))"),
        ("exp(2*x)", "1/2*exp(2*x)"),
        ("exp(3*x)", "1/3*exp(3*x)"),
        ("exp(-x)", "-1*exp(-x)"),
        ("exp(2*x + 1)", "1/2*exp(2*x + 1)"),
        ("exp(x)*cos(2*x)", "exp(x)*(cos(2*x) + 2*sin(2*x))/5"),
        ("exp(3*x)*sin(x)", "exp(3*x)*(3*sin(x) - cos(x))/10"),
        (
            "exp(-2*x)*cos(3*x)",
            "exp(-2*x)*(-2*cos(3*x) + 3*sin(3*x))/13",
        ),
        ("exp(2*x)*cos(2*x)", "exp(2*x)*(cos(2*x) + sin(2*x))/4"),
        ("exp(x)*sin(3*x)", "exp(x)*(sin(3*x) - 3*cos(3*x))/10"),
        ("arcsin(x)", "x*arcsin(x) + (1 - x^2)^(1/2)"),
        ("arccos(x)", "x*arccos(x) - (1 - x^2)^(1/2)"),
        ("arctan(x)", "x*arctan(x) - 1/2*log(abs(x^2 + 1))"),
        (
            "arcsin(2*x + 1)",
            "1/2*((2*x + 1)*arcsin(2*x + 1) + (1 - (2*x + 1)^2)^(1/2))",
        ),
        ("cos(2*x)*sin(2*x)", "-1/4*cos(2*x)^2"),
    ];

    assert_eq!(cases.len(), 25, "expected 25 trivial trig/exp/log cases");
    for (input, expected) in cases {
        assert_integral_expected(input, expected);
    }
}

#[test]
fn trig_exp_log_nontrivial_suite() {
    let cases: Vec<(&str, Vec<f64>)> = vec![
        ("sin(x)^4", vec![-1.0, -0.5, 0.0, 0.5, 1.0]),
        ("cos(x)^4", vec![-1.0, -0.5, 0.0, 0.5, 1.0]),
        ("sin(x)^5", vec![-1.0, -0.5, 0.5]),
        ("cos(x)^5", vec![-1.0, -0.5, 0.5]),
        ("sin(x)^3*cos(x)^2", vec![-1.0, -0.5, 0.5, 1.0]),
        ("sin(x)^2*cos(x)^3", vec![-1.0, -0.5, 0.5, 1.0]),
        ("sin(2*x)^3*cos(2*x)", vec![-0.5, 0.0, 0.5]),
        ("sin(3*x)*cos(3*x)^3", vec![-0.5, 0.0, 0.5]),
        ("sin(2*x)^5", vec![-0.5, 0.0, 0.5]),
        ("cos(2*x)^5", vec![-0.5, 0.0, 0.5]),
        ("exp(2*x + 1)*sin(2*x)", vec![-0.5, 0.0, 0.5]),
        ("exp(2*x + 1)*cos(3*x)", vec![-0.5, 0.0, 0.5]),
        ("exp(-x)*sin(2*x + 1)", vec![-0.5, 0.0, 0.5]),
        ("exp(-x)*cos(2*x + 1)", vec![-0.5, 0.0, 0.5]),
        ("exp(3/2*x)*sin(1/2*x + 1)", vec![-0.5, 0.0, 0.5]),
        ("exp(1/2*x)*cos(1/2*x)", vec![-0.5, 0.0, 0.5]),
        ("exp(3*x - 1)*sin(4*x)", vec![-0.5, 0.0, 0.5]),
        ("exp(3*x - 1)*cos(4*x)", vec![-0.5, 0.0, 0.5]),
        ("arcsin(1/2*x + 1/5)", vec![-0.4, 0.0, 0.4]),
        ("arccos(1/2*x - 1/10)", vec![-1.0, 0.0, 1.0]),
        ("arctan(3*x - 1)", vec![-0.5, 0.0, 0.5]),
        ("sin(x)^6", vec![-0.5, 0.0, 0.5]),
        ("cos(x)^6", vec![-0.5, 0.0, 0.5]),
        ("sin(2*x)^4", vec![-0.5, 0.0, 0.5]),
        ("cos(2*x)^4", vec![-0.5, 0.0, 0.5]),
    ];

    assert_eq!(cases.len(), 25, "expected 25 non-trivial trig/exp/log cases");
    for (input, samples) in cases {
        assert_numeric_roundtrip(input, &samples);
    }
}
