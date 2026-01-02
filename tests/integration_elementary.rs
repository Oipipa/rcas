use num_traits::{ToPrimitive, Zero};
use rcas::{
    Expr, IntegrandKind, IntegrationResult, NonElementaryKind, ReasonCode, differentiate, integrate,
    parse_expr, simplify_fully, sub,
};

const DEFAULT_SAMPLES: [f64; 10] = [-2.7, -1.9, -1.1, -0.4, 0.6, 1.2, 1.8, 2.5, 3.3, 4.1];
const MIN_NUMERIC_SAMPLES: usize = 3;
const NUMERIC_TOLERANCE: f64 = 1e-6;

#[derive(Clone, Debug)]
struct Case {
    integrand: String,
    label: &'static str,
    force_numeric: bool,
}

impl Case {
    fn new(label: &'static str, integrand: String, force_numeric: bool) -> Self {
        Self {
            integrand,
            label,
            force_numeric,
        }
    }
}

#[derive(Clone, Debug)]
struct NonElemCase {
    integrand: &'static str,
    kind: NonElementaryKind,
}

#[test]
fn integration_elementary_roundtrip() {
    let cases = build_elementary_cases();
    assert!(
        cases.len() >= 500,
        "expected 500+ elementary cases, got {}",
        cases.len()
    );

    for (idx, case) in cases.iter().enumerate() {
        let expr = parse_expr(&case.integrand)
            .unwrap_or_else(|_| panic!("parse failure for case {idx}: {}", case.integrand));
        match integrate("x", &expr) {
            IntegrationResult::Integrated { result, .. } => {
                verify_roundtrip(&expr, &result, case, idx);
            }
            other => panic!(
                "expected integration for case {idx} [{}]: {} but got {other:?}",
                case.label, case.integrand
            ),
        }
    }
}

#[test]
fn integration_non_elementary_cases() {
    let cases = vec![
        NonElemCase {
            integrand: "exp(x^2)",
            kind: NonElementaryKind::ExpOfPolynomial,
        },
        NonElemCase {
            integrand: "exp(x^3+x)",
            kind: NonElementaryKind::ExpOfPolynomial,
        },
        NonElemCase {
            integrand: "exp(x^2+x+1)",
            kind: NonElementaryKind::ExpOfPolynomial,
        },
        NonElemCase {
            integrand: "sin(x)/x",
            kind: NonElementaryKind::TrigOverArgument,
        },
        NonElemCase {
            integrand: "cos(x)/x",
            kind: NonElementaryKind::TrigOverArgument,
        },
        NonElemCase {
            integrand: "tan(x)/x",
            kind: NonElementaryKind::TrigOverArgument,
        },
        NonElemCase {
            integrand: "sin(x^2)/x^2",
            kind: NonElementaryKind::TrigOverPolynomialArgument,
        },
        NonElemCase {
            integrand: "cos(x^2)/x^2",
            kind: NonElementaryKind::TrigOverPolynomialArgument,
        },
        NonElemCase {
            integrand: "tan(x^2)/x^2",
            kind: NonElementaryKind::TrigOverPolynomialArgument,
        },
        NonElemCase {
            integrand: "x^x",
            kind: NonElementaryKind::PowerSelf,
        },
        NonElemCase {
            integrand: "x^x*log(x)",
            kind: NonElementaryKind::PowerSelfLog,
        },
        NonElemCase {
            integrand: "(x^2+1)^(1/3)",
            kind: NonElementaryKind::SpecialFunctionNeeded,
        },
        NonElemCase {
            integrand: "(x^3+1)^(1/2)",
            kind: NonElementaryKind::SpecialFunctionNeeded,
        },
        NonElemCase {
            integrand: "(x^4+1)^(1/2)",
            kind: NonElementaryKind::SpecialFunctionNeeded,
        },
    ];

    for (idx, case) in cases.iter().enumerate() {
        let expr = parse_expr(case.integrand)
            .unwrap_or_else(|_| panic!("parse failure for non-elementary case {idx}"));
        match integrate("x", &expr) {
            IntegrationResult::NotIntegrable(report) => {
                let expected = case.kind.clone();
                assert_eq!(
                    report.reason,
                    Some(ReasonCode::NonElementary(expected.clone())),
                    "unexpected reason for non-elementary case {idx}: {}",
                    case.integrand
                );
                assert_eq!(
                    report.kind,
                    IntegrandKind::NonElementary(expected),
                    "unexpected kind for non-elementary case {idx}: {}",
                    case.integrand
                );
            }
            other => panic!(
                "expected NotIntegrable for non-elementary case {idx}: {} but got {other:?}",
                case.integrand
            ),
        }
    }
}

fn build_elementary_cases() -> Vec<Case> {
    let mut cases = Vec::new();
    add_polynomial_cases(&mut cases);
    add_linear_power_cases(&mut cases);
    add_rational_cases(&mut cases);
    add_exponential_cases(&mut cases);
    add_log_cases(&mut cases);
    add_trig_cases(&mut cases);
    add_inverse_trig_cases(&mut cases);
    add_mixed_product_cases(&mut cases);
    add_parameter_cases(&mut cases);
    cases
}

fn add_polynomial_cases(cases: &mut Vec<Case>) {
    let max_degree = 8;
    for seed in 0..=10 {
        for degree in 0..=max_degree {
            let mut coeffs = Vec::new();
            for exp in 0..=degree {
                let sign = if (exp + seed) % 2 == 0 { 1 } else { -1 };
                let coeff = sign * (exp + 1 + seed) as i64;
                coeffs.push(coeff);
            }
            let expr = poly_string(&coeffs);
            cases.push(Case::new("polynomial", expr, false));
        }
    }
}

fn add_linear_power_cases(cases: &mut Vec<Case>) {
    let a_vals = [1, 2, -3];
    let b_vals = [0, 1, -2];
    let exponents = ["-3", "-2", "-1", "-1/2", "1/2", "3/2", "2", "3"];
    for &a in &a_vals {
        for &b in &b_vals {
            let base = linear_expr(a, b);
            for exp in exponents {
                let expr = format!("({base})^({exp})");
                cases.push(Case::new("linear-power", expr, false));
            }
        }
    }
}

fn add_rational_cases(cases: &mut Vec<Case>) {
    let numerators = vec![
        "1".to_string(),
        "x".to_string(),
        "x^2".to_string(),
        "x^3".to_string(),
        "x+1".to_string(),
        "2*x-1".to_string(),
        "x^2+2*x+1".to_string(),
        "3*x^2-2*x+5".to_string(),
        "x^3-2*x".to_string(),
        "2*x^3+3*x^2+1".to_string(),
    ];
    let denominators = vec![
        "x+1",
        "x-2",
        "2*x+1",
        "3*x-4",
        "x-3",
        "x^2+1",
        "x^2+4",
        "x^2+2*x+2",
        "2*x^2+3*x+5",
        "x^2-2*x+5",
        "(x+1)^2",
        "(x-2)^3",
        "(x^2+1)^2",
    ];
    for num in &numerators {
        for denom in &denominators {
            let expr = format!("({num})/({denom})");
            cases.push(Case::new("rational", expr, true));
        }
    }
}

fn add_exponential_cases(cases: &mut Vec<Case>) {
    let k_vals = [-3, -1, 1, 2, 4];
    let c_vals = [-2, 0, 1];
    for &k in &k_vals {
        for &c in &c_vals {
            let arg = linear_expr(k, c);
            cases.push(Case::new("exponential", format!("exp({arg})"), true));
        }
    }

    let a_vals = [-2, -1, 1, 2];
    let b_vals = [1, 2, 3];
    let shifts = [0, 1];
    for &a in &a_vals {
        for &b in &b_vals {
            for &shift in &shifts {
                let exp_arg = linear_expr(a, shift);
                let trig_arg = linear_expr(b, 0);
                cases.push(Case::new(
                    "exp-trig",
                    format!("exp({exp_arg})*sin({trig_arg})"),
                    true,
                ));
                cases.push(Case::new(
                    "exp-trig",
                    format!("exp({exp_arg})*cos({trig_arg})"),
                    true,
                ));
            }
        }
    }

    let substitution_cases = [
        "2*x*exp(x^2)",
        "(2*x+1)*exp(x^2+x)",
        "3*(2*x-1)*exp(x^2-x)",
        "(4*x+1)*exp(2*x^2+x)",
        "(6*x-2)*exp(3*x^2-2*x)",
        "5*(4*x+3)*exp(2*x^2+3*x)",
    ];
    for expr in substitution_cases {
        cases.push(Case::new("exp-substitution", expr.to_string(), true));
    }
}

fn add_log_cases(cases: &mut Vec<Case>) {
    let direct_logs = ["log(x)", "log(x+1)", "log(2*x+1)", "log(3*x-2)", "log(x-3)"];
    for expr in direct_logs {
        cases.push(Case::new("log", expr.to_string(), true));
    }
    cases.push(Case::new("log", "1/x".to_string(), true));

    let degrees = [1, 2, 3, 4];
    let k_vals = [1, 2];
    let c_vals = [1, -2];
    for &deg in &degrees {
        let poly = format!("x^{deg}");
        for &k in &k_vals {
            for &c in &c_vals {
                let arg = linear_expr(k, c);
                cases.push(Case::new(
                    "poly-log",
                    format!("{poly}*log({arg})"),
                    true,
                ));
            }
        }
    }
}

fn add_trig_cases(cases: &mut Vec<Case>) {
    let trig_funcs = ["sin", "cos", "tan", "sec", "csc", "cot"];
    let k_vals = [-3, -1, 1, 2];
    let shifts = [0, 1];
    for func in trig_funcs {
        for &k in &k_vals {
            for &shift in &shifts {
                let arg = linear_expr(k, shift);
                cases.push(Case::new("trig", format!("{func}({arg})"), true));
            }
        }
    }

    let hyperbolic_funcs = ["sinh", "cosh", "tanh"];
    let k_vals = [1, 2];
    let shifts = [0, 1];
    for func in hyperbolic_funcs {
        for &k in &k_vals {
            for &shift in &shifts {
                let arg = linear_expr(k, shift);
                cases.push(Case::new("hyperbolic", format!("{func}({arg})"), true));
            }
        }
    }

    let powers = [2, 3, 4, 5];
    let k_vals = [1, 2];
    for &power in &powers {
        for &k in &k_vals {
            let arg = linear_expr(k, 0);
            cases.push(Case::new(
                "trig-power",
                format!("sin({arg})^{power}"),
                true,
            ));
            cases.push(Case::new(
                "trig-power",
                format!("cos({arg})^{power}"),
                true,
            ));
        }
    }

    let power_pairs = [
        (1, 1),
        (1, 2),
        (1, 3),
        (3, 1),
        (3, 2),
        (2, 1),
        (2, 3),
        (5, 1),
        (1, 5),
        (2, 2),
    ];
    let k_vals = [1, 2];
    for &(sin_exp, cos_exp) in &power_pairs {
        for &k in &k_vals {
            let arg = linear_expr(k, 0);
            cases.push(Case::new(
                "trig-product",
                format!("sin({arg})^{sin_exp}*cos({arg})^{cos_exp}"),
                true,
            ));
        }
    }

    let k_vals = [1, 2];
    for &k in &k_vals {
        let arg = linear_expr(k, 0);
        cases.push(Case::new(
            "trig-power",
            format!("sec({arg})^2"),
            true,
        ));
        cases.push(Case::new(
            "trig-power",
            format!("csc({arg})^2"),
            true,
        ));
    }
}

fn add_inverse_trig_cases(cases: &mut Vec<Case>) {
    let bounded_args = ["x/5", "x/6"];
    let unbounded_args = ["x", "2*x+1"];
    let large_args = ["x+5", "x+6"];

    for arg in &bounded_args {
        cases.push(Case::new(
            "inverse-trig",
            format!("asin({arg})"),
            true,
        ));
        cases.push(Case::new(
            "inverse-trig",
            format!("acos({arg})"),
            true,
        ));
        cases.push(Case::new(
            "inverse-hyperbolic",
            format!("atanh({arg})"),
            true,
        ));
    }

    for arg in &unbounded_args {
        cases.push(Case::new(
            "inverse-trig",
            format!("atan({arg})"),
            true,
        ));
        cases.push(Case::new(
            "inverse-trig",
            format!("acot({arg})"),
            true,
        ));
        cases.push(Case::new(
            "inverse-hyperbolic",
            format!("asinh({arg})"),
            true,
        ));
    }

    for arg in &large_args {
        cases.push(Case::new(
            "inverse-trig",
            format!("asec({arg})"),
            true,
        ));
        cases.push(Case::new(
            "inverse-trig",
            format!("acsc({arg})"),
            true,
        ));
        cases.push(Case::new(
            "inverse-hyperbolic",
            format!("acosh({arg})"),
            true,
        ));
    }
}

fn add_mixed_product_cases(cases: &mut Vec<Case>) {
    let degrees = [1, 2, 3, 4];
    let k_vals = [1, 2];
    for &deg in &degrees {
        let poly = format!("x^{deg}");
        for &k in &k_vals {
            let arg = linear_expr(k, 0);
            cases.push(Case::new(
                "poly-exp",
                format!("{poly}*exp({arg})"),
                true,
            ));
            cases.push(Case::new(
                "poly-trig",
                format!("{poly}*sin({arg})"),
                true,
            ));
            cases.push(Case::new(
                "poly-trig",
                format!("{poly}*cos({arg})"),
                true,
            ));
            cases.push(Case::new(
                "poly-hyperbolic",
                format!("{poly}*sinh({arg})"),
                true,
            ));
            cases.push(Case::new(
                "poly-hyperbolic",
                format!("{poly}*cosh({arg})"),
                true,
            ));
            let log_arg = linear_expr(k, 1);
            cases.push(Case::new(
                "poly-log",
                format!("{poly}*log({log_arg})"),
                true,
            ));
        }
    }
}

fn add_parameter_cases(cases: &mut Vec<Case>) {
    let exprs = [
        "a*x",
        "a*x^2",
        "a*x^3",
        "a*x^4",
        "a*x+b",
        "a*x-b",
        "a*x+c",
        "a*x+d",
        "a*x^2+b*x+c",
        "a*x^3+b*x^2+c*x+d",
        "(a*x+b)^2",
        "(a*x+b)^3",
        "(a*x+b)^(-1)",
        "(a*x+b)^(1/2)",
        "(a*x+b)^(3/2)",
        "exp(a*x+b)",
        "exp(a*x-b)",
        "sin(a*x+b)",
        "cos(a*x+b)",
        "tan(a*x+b)",
        "sinh(a*x+b)",
        "cosh(a*x+b)",
        "log(a*x+b)",
        "x*exp(a*x)",
        "x*sin(a*x)",
        "x*cos(a*x)",
        "exp(a*x)*sin(b*x)",
        "exp(a*x)*cos(b*x)",
        "sin(a*x)*cos(a*x)",
        "x^2*exp(b*x)",
        "x^2*sin(b*x)",
        "x^2*cos(b*x)",
        "x^3*exp(b*x)",
        "x^3*sin(b*x)",
        "x^3*cos(b*x)",
    ];
    for expr in exprs {
        cases.push(Case::new("parameterized", expr.to_string(), true));
    }
}

fn verify_roundtrip(expr: &Expr, result: &Expr, case: &Case, idx: usize) {
    let derivative = simplify_fully(differentiate("x", result));
    let target = simplify_fully(expr.clone());
    let delta = simplify_fully(sub(derivative.clone(), target.clone()));
    if is_zero_expr(&delta) && !case.force_numeric {
        return;
    }
    numeric_check(&delta, case, idx);
}

fn numeric_check(delta: &Expr, case: &Case, idx: usize) {
    let mut max_delta: f64 = 0.0;
    let mut samples = 0;
    for &sample in &DEFAULT_SAMPLES {
        if let Some(value) = eval_expr_f64(delta, "x", sample) {
            samples += 1;
            max_delta = max_delta.max(value.abs());
        }
    }
    assert!(
        samples >= MIN_NUMERIC_SAMPLES,
        "insufficient numeric samples for case {idx} [{}]: {}",
        case.label,
        case.integrand
    );
    assert!(
        max_delta < NUMERIC_TOLERANCE,
        "roundtrip failure for case {idx} [{}]: {}, max delta {max_delta}",
        case.label,
        case.integrand
    );
}

fn is_zero_expr(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(c) if c.is_zero())
}

fn eval_expr_f64(expr: &Expr, var: &str, x: f64) -> Option<f64> {
    let value = eval_expr_f64_with_env(expr, var, x)?;
    if value.is_finite() {
        Some(value)
    } else {
        None
    }
}

fn eval_expr_f64_with_env(expr: &Expr, var: &str, x: f64) -> Option<f64> {
    let value = match expr {
        Expr::Constant(c) => c.to_f64(),
        Expr::Variable(v) => {
            if v == var {
                Some(x)
            } else {
                Some(param_value(v))
            }
        }
        Expr::Add(a, b) => Some(eval_expr_f64_with_env(a, var, x)? + eval_expr_f64_with_env(b, var, x)?),
        Expr::Sub(a, b) => Some(eval_expr_f64_with_env(a, var, x)? - eval_expr_f64_with_env(b, var, x)?),
        Expr::Mul(a, b) => Some(eval_expr_f64_with_env(a, var, x)? * eval_expr_f64_with_env(b, var, x)?),
        Expr::Div(a, b) => Some(eval_expr_f64_with_env(a, var, x)? / eval_expr_f64_with_env(b, var, x)?),
        Expr::Pow(base, exp) => {
            let base_val = eval_expr_f64_with_env(base, var, x)?;
            let exponent = match &**exp {
                Expr::Constant(c) => c.to_f64()?,
                _ => return None,
            };
            Some(base_val.powf(exponent))
        }
        Expr::Neg(inner) => eval_expr_f64_with_env(inner, var, x).map(|v| -v),
        Expr::Sin(inner) => eval_expr_f64_with_env(inner, var, x).map(f64::sin),
        Expr::Cos(inner) => eval_expr_f64_with_env(inner, var, x).map(f64::cos),
        Expr::Tan(inner) => eval_expr_f64_with_env(inner, var, x).map(f64::tan),
        Expr::Sec(inner) => eval_expr_f64_with_env(inner, var, x).map(|v| 1.0 / v.cos()),
        Expr::Csc(inner) => eval_expr_f64_with_env(inner, var, x).map(|v| 1.0 / v.sin()),
        Expr::Cot(inner) => eval_expr_f64_with_env(inner, var, x).map(|v| v.cos() / v.sin()),
        Expr::Atan(inner) => eval_expr_f64_with_env(inner, var, x).map(f64::atan),
        Expr::Asin(inner) => eval_expr_f64_with_env(inner, var, x).map(f64::asin),
        Expr::Acos(inner) => eval_expr_f64_with_env(inner, var, x).map(f64::acos),
        Expr::Asec(inner) => eval_expr_f64_with_env(inner, var, x).map(|v| (1.0 / v).acos()),
        Expr::Acsc(inner) => eval_expr_f64_with_env(inner, var, x).map(|v| (1.0 / v).asin()),
        Expr::Acot(inner) => eval_expr_f64_with_env(inner, var, x).map(|v| (1.0 / v).atan()),
        Expr::Sinh(inner) => eval_expr_f64_with_env(inner, var, x).map(f64::sinh),
        Expr::Cosh(inner) => eval_expr_f64_with_env(inner, var, x).map(f64::cosh),
        Expr::Tanh(inner) => eval_expr_f64_with_env(inner, var, x).map(f64::tanh),
        Expr::Asinh(inner) => eval_expr_f64_with_env(inner, var, x).map(f64::asinh),
        Expr::Acosh(inner) => eval_expr_f64_with_env(inner, var, x).map(f64::acosh),
        Expr::Atanh(inner) => eval_expr_f64_with_env(inner, var, x).map(f64::atanh),
        Expr::Exp(inner) => eval_expr_f64_with_env(inner, var, x).map(f64::exp),
        Expr::Log(inner) => {
            Some(eval_expr_f64_with_env(inner, var, x)?.abs().ln())
        }
        Expr::Abs(inner) => eval_expr_f64_with_env(inner, var, x).map(f64::abs),
    };
    value
}

fn param_value(name: &str) -> f64 {
    match name {
        "a" => 1.7,
        "b" => -0.6,
        "c" => 0.9,
        "d" => 2.4,
        "p" => -1.3,
        "q" => 0.5,
        "r" => 3.2,
        _ => 1.1,
    }
}

fn poly_string(coeffs: &[i64]) -> String {
    let mut terms = Vec::new();
    for (exp, &coeff) in coeffs.iter().enumerate() {
        if coeff == 0 {
            continue;
        }
        let abs_coeff = coeff.abs();
        let term = match exp {
            0 => format!("{abs_coeff}"),
            1 => format!("{abs_coeff}*x"),
            _ => format!("{abs_coeff}*x^{exp}"),
        };
        if terms.is_empty() {
            if coeff < 0 {
                terms.push(format!("-{term}"));
            } else {
                terms.push(term);
            }
        } else if coeff < 0 {
            terms.push(format!("-{term}"));
        } else {
            terms.push(format!("+{term}"));
        }
    }
    if terms.is_empty() {
        "0".to_string()
    } else {
        terms.join("")
    }
}

fn linear_expr(a: i64, b: i64) -> String {
    if b == 0 {
        format!("{a}*x")
    } else if b > 0 {
        format!("{a}*x+{b}")
    } else {
        format!("{a}*x{b}")
    }
}
