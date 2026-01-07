use crate::core::expr::Expr;

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
    TrigOverPolynomialArgument,
    PowerSelf,
    PowerSelfLog,
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
    Risch,
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
    pub note: Option<String>,
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
