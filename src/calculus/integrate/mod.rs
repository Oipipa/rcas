mod common;
mod exponential;
mod logarithmic;
mod polynomial;
mod rational;
mod trig;

use crate::calculus::differentiate;
use crate::expr::{Expr, Rational};
use crate::simplify::{simplify, simplify_fully};
use num_traits::{One, ToPrimitive, Zero};

pub(crate) use common::{coeff_of_var, linear_parts};
pub use exponential::is_exp;
pub use logarithmic::is_log;
pub use polynomial::is_polynomial;
pub use rational::is_rational;
pub use trig::is_trig;

const TRANSFORM_SIZE_LIMIT: usize = 96;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntegrandKind {
    Polynomial,
    Rational { linear: bool },
    Trig,
    Exponential,
    Logarithmic,
    Product(Box<IntegrandKind>, Box<IntegrandKind>),
    Sum,
    NonElementary(NonElementaryKind),
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NonElementaryKind {
    ExpOfPolynomial,
    TrigOverArgument,
    SpecialFunctionNeeded,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReasonCode {
    NonRational,
    NonPolynomialTrig,
    NonElementary(NonElementaryKind),
    UnknownStructure,
    SizeLimit(usize),
    StrategyNotAvailable(&'static str),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Strategy {
    Direct,
    Substitution,
    IntegrationByParts,
    PartialFractions,
    RischLite,
    MeijerG,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttemptStatus {
    Succeeded,
    NotApplicable,
    Failed(ReasonCode),
    HitLimit { size: usize, limit: usize },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegrationAttempt {
    pub strategy: Strategy,
    pub status: AttemptStatus,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegrandReport {
    pub kind: IntegrandKind,
    pub reason: Option<ReasonCode>,
    pub attempts: Vec<IntegrationAttempt>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntegrationResult {
    Integrated {
        result: Expr,
        report: IntegrandReport,
    },
    NotIntegrable(IntegrandReport),
}

pub fn integrate(var: &str, expr: &Expr) -> IntegrationResult {
    let mut attempts = Vec::new();
    let mut kind = classify_integrand(expr);

    // If the chosen variable does not occur, treat the expression as a constant.
    if !contains_var(expr, var) {
        let result = simplify(Expr::Mul(
            expr.clone().boxed(),
            Expr::Variable(var.to_string()).boxed(),
        ));
        attempts.push(IntegrationAttempt {
            strategy: Strategy::Direct,
            status: AttemptStatus::Succeeded,
        });
        return IntegrationResult::Integrated {
            result,
            report: IntegrandReport {
                kind,
                reason: None,
                attempts,
            },
        };
    }

    if let Some(non_elem) = detect_non_elementary(expr) {
        kind = IntegrandKind::NonElementary(non_elem.clone());
        let report = IntegrandReport {
            kind,
            reason: Some(ReasonCode::NonElementary(non_elem)),
            attempts,
        };
        return IntegrationResult::NotIntegrable(report);
    }

    if let Some(result) = integrate_direct(expr, var) {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::Direct,
            status: AttemptStatus::Succeeded,
        });
        return IntegrationResult::Integrated {
            result: simplify(result),
            report: IntegrandReport {
                kind,
                reason: None,
                attempts,
            },
        };
    }

    attempts.push(IntegrationAttempt {
        strategy: Strategy::Direct,
        status: AttemptStatus::Failed(default_reason(&kind)),
    });

    let size = expr_size(expr);

    // Substitution heuristics (u-sub, f'/f).
    if size > TRANSFORM_SIZE_LIMIT {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::Substitution,
            status: AttemptStatus::HitLimit {
                size,
                limit: TRANSFORM_SIZE_LIMIT,
            },
        });
    } else if let Some(result) = integrate_by_substitution(expr, var) {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::Substitution,
            status: AttemptStatus::Succeeded,
        });
        return IntegrationResult::Integrated {
            result: simplify(result),
            report: IntegrandReport {
                kind,
                reason: None,
                attempts,
            },
        };
    } else {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::Substitution,
            status: AttemptStatus::NotApplicable,
        });
    }

    // Integration by parts for polynomial * trig/exp/log forms.
    if size > TRANSFORM_SIZE_LIMIT {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::IntegrationByParts,
            status: AttemptStatus::HitLimit {
                size,
                limit: TRANSFORM_SIZE_LIMIT,
            },
        });
    } else if let Some(result) = integration_by_parts(expr, var) {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::IntegrationByParts,
            status: AttemptStatus::Succeeded,
        });
        return IntegrationResult::Integrated {
            result: simplify(result),
            report: IntegrandReport {
                kind,
                reason: None,
                attempts,
            },
        };
    } else {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::IntegrationByParts,
            status: AttemptStatus::NotApplicable,
        });
    }

    // Partial fractions (only if rational).
    if size > TRANSFORM_SIZE_LIMIT {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::PartialFractions,
            status: AttemptStatus::HitLimit {
                size,
                limit: TRANSFORM_SIZE_LIMIT,
            },
        });
    } else if let Some(result) = integrate_partial_fractions(expr, var) {
        attempts.push(IntegrationAttempt {
            strategy: Strategy::PartialFractions,
            status: AttemptStatus::Succeeded,
        });
        return IntegrationResult::Integrated {
            result: simplify(result),
            report: IntegrandReport {
                kind,
                reason: None,
                attempts,
            },
        };
    } else {
        let status = if is_rational_like(expr) {
            AttemptStatus::Failed(ReasonCode::NonRational)
        } else {
            AttemptStatus::NotApplicable
        };
        attempts.push(IntegrationAttempt {
            strategy: Strategy::PartialFractions,
            status,
        });
    }

    // Future hooks.
    attempts.push(IntegrationAttempt {
        strategy: Strategy::RischLite,
        status: AttemptStatus::Failed(ReasonCode::StrategyNotAvailable("risch-lite")),
    });
    attempts.push(IntegrationAttempt {
        strategy: Strategy::MeijerG,
        status: AttemptStatus::Failed(ReasonCode::StrategyNotAvailable("meijer-g expansion")),
    });

    let reason = Some(default_reason(&kind));
    IntegrationResult::NotIntegrable(IntegrandReport {
        kind,
        reason,
        attempts,
    })
}

fn integrate_direct(expr: &Expr, var: &str) -> Option<Expr> {
    if !contains_var(expr, var) {
        let with_var = Expr::Mul(
            expr.clone().boxed(),
            Expr::Variable(var.to_string()).boxed(),
        );
        return Some(with_var);
    }
    match expr {
        Expr::Add(a, b) => Some(Expr::Add(
            integrate_direct(a, var)?.boxed(),
            integrate_direct(b, var)?.boxed(),
        )),
        Expr::Sub(a, b) => Some(Expr::Sub(
            integrate_direct(a, var)?.boxed(),
            integrate_direct(b, var)?.boxed(),
        )),
        Expr::Neg(inner) => integrate_direct(inner, var).map(|r| Expr::Neg(r.boxed())),
        Expr::Mul(a, b) => match (&**a, &**b) {
            (Expr::Constant(c), other) | (other, Expr::Constant(c)) => integrate_direct(other, var)
                .map(|r| Expr::Mul(Expr::Constant(c.clone()).boxed(), r.boxed())),
            _ => None,
        },
        _ => polynomial::integrate(expr, var)
            .or_else(|| rational::integrate(expr, var))
            .or_else(|| trig::integrate(expr, var))
            .or_else(|| exponential::integrate(expr, var))
            .or_else(|| logarithmic::integrate(expr, var)),
    }
}

fn integrate_by_substitution(expr: &Expr, var: &str) -> Option<Expr> {
    if let Expr::Mul(a, b) = expr {
        if let Some(result) = substitution_pair(a, b, var) {
            return Some(result);
        }
        if let Some(result) = substitution_pair(b, a, var) {
            return Some(result);
        }
    }

    if let Expr::Div(num, den) = expr {
        let den_deriv = simplify_fully(differentiate(var, den));
        let num_simplified = simplify_fully((**num).clone());
        if den_deriv == num_simplified {
            return Some(Expr::Log(den.clone()));
        }
        if let Some(k) = constant_multiple(&num_simplified, &den_deriv) {
            return Some(Expr::Mul(
                Expr::Constant(k).boxed(),
                Expr::Log(den.clone()).boxed(),
            ));
        }
        if let Some(k) = constant_multiple(&den_deriv, &num_simplified) {
            return Some(Expr::Mul(
                Expr::Constant(Rational::one() / k).boxed(),
                Expr::Log(den.clone()).boxed(),
            ));
        }
    }

    None
}

fn substitution_pair(candidate_derivative: &Expr, outer: &Expr, var: &str) -> Option<Expr> {
    let inner = match outer {
        Expr::Sin(arg) | Expr::Cos(arg) | Expr::Tan(arg) | Expr::Exp(arg) | Expr::Log(arg) => {
            Some(&**arg)
        }
        Expr::Pow(base, _) => Some(&**base),
        _ => None,
    }?;

    let inner_derivative = simplify_fully(differentiate(var, inner));
    let candidate = simplify_fully(candidate_derivative.clone());

    if candidate == inner_derivative {
        return integrate_with_respect_to_inner(outer, inner);
    }

    if let Some(k) = constant_multiple(&candidate, &inner_derivative) {
        return integrate_with_respect_to_inner(outer, inner)
            .map(|expr| Expr::Mul(Expr::Constant(k).boxed(), expr.boxed()));
    }

    None
}

fn integrate_with_respect_to_inner(outer: &Expr, inner: &Expr) -> Option<Expr> {
    match outer {
        Expr::Exp(_) => Some(Expr::Exp(inner.clone().boxed())),
        Expr::Sin(_) => Some(Expr::Neg(Expr::Cos(inner.clone().boxed()).boxed())),
        Expr::Cos(_) => Some(Expr::Sin(inner.clone().boxed())),
        Expr::Tan(_) => Some(Expr::Neg(
            Expr::Log(Expr::Cos(inner.clone().boxed()).boxed()).boxed(),
        )),
        Expr::Log(_) => Some(Expr::Sub(
            Expr::Mul(
                inner.clone().boxed(),
                Expr::Log(inner.clone().boxed()).boxed(),
            )
            .boxed(),
            inner.clone().boxed(),
        )),
        Expr::Pow(_, exp) => {
            if let Expr::Constant(n) = &**exp {
                if n != &-Rational::from_integer(1.into()) {
                    let new_exp = n + Rational::one();
                    return Some(Expr::Div(
                        Expr::Pow(
                            inner.clone().boxed(),
                            Expr::Constant(new_exp.clone()).boxed(),
                        )
                        .boxed(),
                        Expr::Constant(new_exp).boxed(),
                    ));
                }
            }
            None
        }
        _ => None,
    }
}

fn constant_multiple(expr: &Expr, target: &Expr) -> Option<Rational> {
    match expr {
        e if e == target => Some(Rational::one()),
        Expr::Constant(c) => match target {
            Expr::Constant(t) if !t.is_zero() => Some(c / t),
            _ => None,
        },
        Expr::Mul(a, b) => match (&**a, &**b) {
            (Expr::Constant(c), other) if other == target => Some(c.clone()),
            (other, Expr::Constant(c)) if other == target => Some(c.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn integration_by_parts(expr: &Expr, var: &str) -> Option<Expr> {
    if let Expr::Mul(a, b) = expr {
        if polynomial::is_polynomial(a) {
            return integrate_parts(a, b, var);
        }
        if polynomial::is_polynomial(b) {
            return integrate_parts(b, a, var);
        }
    }
    None
}

fn integrate_parts(u: &Expr, dv: &Expr, var: &str) -> Option<Expr> {
    let v = integrate_direct(dv, var)?;
    let du = differentiate(var, u);
    let vdu = Expr::Mul(v.clone().boxed(), du.boxed());
    let int_vdu = integrate_direct(&vdu, var)?;
    Some(simplify(Expr::Sub(
        Expr::Mul(u.clone().boxed(), v.boxed()).boxed(),
        int_vdu.boxed(),
    )))
}

fn integrate_partial_fractions(expr: &Expr, _var: &str) -> Option<Expr> {
    if !is_rational_like(expr) {
        return None;
    }
    rational::integrate(expr, _var)
}

fn classify_integrand(expr: &Expr) -> IntegrandKind {
    if let Some(non_elem) = detect_non_elementary(expr) {
        return IntegrandKind::NonElementary(non_elem);
    }
    if polynomial::is_polynomial(expr) {
        return IntegrandKind::Polynomial;
    }
    if rational::is_rational(expr) {
        return IntegrandKind::Rational { linear: true };
    }
    if is_rational_like(expr) {
        return IntegrandKind::Rational { linear: false };
    }
    if trig::is_trig(expr) {
        return IntegrandKind::Trig;
    }
    if exponential::is_exp(expr) {
        return IntegrandKind::Exponential;
    }
    if logarithmic::is_log(expr) {
        return IntegrandKind::Logarithmic;
    }
    match expr {
        Expr::Mul(a, b) => IntegrandKind::Product(
            Box::new(classify_integrand(a)),
            Box::new(classify_integrand(b)),
        ),
        Expr::Add(_, _) | Expr::Sub(_, _) => IntegrandKind::Sum,
        _ => IntegrandKind::Unknown,
    }
}

fn detect_non_elementary(expr: &Expr) -> Option<NonElementaryKind> {
    match expr {
        Expr::Exp(arg) => {
            if let Some(deg) = polynomial_degree(arg) {
                if deg > 1 {
                    return Some(NonElementaryKind::ExpOfPolynomial);
                }
            }
        }
        Expr::Div(num, den) => {
            if matches!(&**num, Expr::Sin(_)) || matches!(&**num, Expr::Cos(_)) {
                if is_linear_match(num, den) {
                    return Some(NonElementaryKind::TrigOverArgument);
                }
            }
        }
        _ => {}
    }
    None
}

fn is_linear_match(num: &Expr, den: &Expr) -> bool {
    let inner = match num {
        Expr::Sin(arg) | Expr::Cos(arg) => arg,
        _ => return false,
    };
    match (&**inner, den) {
        (Expr::Variable(v1), Expr::Variable(v2)) => v1 == v2,
        (Expr::Variable(v1), Expr::Mul(a, b)) => match (&**a, &**b) {
            (Expr::Constant(_), Expr::Variable(v2)) | (Expr::Variable(v2), Expr::Constant(_)) => {
                v1 == v2
            }
            _ => false,
        },
        _ => false,
    }
}

fn polynomial_degree(expr: &Expr) -> Option<usize> {
    match expr {
        Expr::Constant(_) => Some(0),
        Expr::Variable(_) => Some(1),
        Expr::Add(a, b) | Expr::Sub(a, b) => {
            let da = polynomial_degree(a)?;
            let db = polynomial_degree(b)?;
            Some(da.max(db))
        }
        Expr::Mul(a, b) => {
            let da = polynomial_degree(a)?;
            let db = polynomial_degree(b)?;
            Some(da + db)
        }
        Expr::Pow(base, exp) => match (&**base, &**exp) {
            (Expr::Variable(_), Expr::Constant(k)) if k.is_integer() && k >= &Rational::zero() => {
                k.to_integer().to_usize()
            }
            (Expr::Constant(_), Expr::Constant(_)) => Some(0),
            _ => None,
        },
        Expr::Neg(inner) => polynomial_degree(inner),
        _ => None,
    }
}

fn is_rational_like(expr: &Expr) -> bool {
    match expr {
        Expr::Div(num, den) => polynomial::is_polynomial(num) && polynomial::is_polynomial(den),
        _ => false,
    }
}

fn expr_size(expr: &Expr) -> usize {
    1 + match expr {
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) | Expr::Pow(a, b) => {
            expr_size(a) + expr_size(b)
        }
        Expr::Neg(inner)
        | Expr::Sin(inner)
        | Expr::Cos(inner)
        | Expr::Tan(inner)
        | Expr::Exp(inner)
        | Expr::Log(inner) => expr_size(inner),
        Expr::Variable(_) | Expr::Constant(_) => 0,
    }
}

fn default_reason(kind: &IntegrandKind) -> ReasonCode {
    match kind {
        IntegrandKind::Rational { .. } => ReasonCode::NonRational,
        IntegrandKind::Trig => ReasonCode::NonPolynomialTrig,
        IntegrandKind::NonElementary(ne) => ReasonCode::NonElementary(ne.clone()),
        _ => ReasonCode::UnknownStructure,
    }
}

fn contains_var(expr: &Expr, var: &str) -> bool {
    match expr {
        Expr::Variable(v) => v == var,
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) | Expr::Pow(a, b) => {
            contains_var(a, var) || contains_var(b, var)
        }
        Expr::Neg(inner)
        | Expr::Sin(inner)
        | Expr::Cos(inner)
        | Expr::Tan(inner)
        | Expr::Exp(inner)
        | Expr::Log(inner) => contains_var(inner, var),
        Expr::Constant(_) => false,
    }
}
