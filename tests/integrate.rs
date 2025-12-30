use rcas::{
    AttemptStatus, IntegrandKind, IntegrationResult, NonElementaryKind, ReasonCode, Strategy,
    integrate, parse_expr, simplify_fully,
};

fn simplify_parse(input: &str) -> rcas::Expr {
    simplify_fully(parse_expr(input).expect("parse input"))
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
