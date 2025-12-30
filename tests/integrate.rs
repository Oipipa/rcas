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
}
