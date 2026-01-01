//! Expression tree definitions and helpers.

use std::fmt;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

pub type Rational = BigRational;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Expr {
    Variable(String),
    Constant(Rational),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Pow(Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),
    Sin(Box<Expr>),
    Cos(Box<Expr>),
    Tan(Box<Expr>),
    Sec(Box<Expr>),
    Csc(Box<Expr>),
    Cot(Box<Expr>),
    Atan(Box<Expr>),
    Asin(Box<Expr>),
    Acos(Box<Expr>),
    Asec(Box<Expr>),
    Acsc(Box<Expr>),
    Acot(Box<Expr>),
    Sinh(Box<Expr>),
    Cosh(Box<Expr>),
    Tanh(Box<Expr>),
    Asinh(Box<Expr>),
    Acosh(Box<Expr>),
    Atanh(Box<Expr>),
    Exp(Box<Expr>),
    Log(Box<Expr>),
    Abs(Box<Expr>),
}

impl Expr {
    pub fn var(name: impl Into<String>) -> Self {
        Expr::Variable(name.into())
    }

    pub fn constant(num: impl Into<BigInt>, den: impl Into<BigInt>) -> Self {
        Expr::Constant(Rational::new(num.into(), den.into()))
    }

    pub fn integer(value: impl Into<BigInt>) -> Self {
        Expr::Constant(Rational::from_integer(value.into()))
    }

    pub fn rational(value: Rational) -> Self {
        Expr::Constant(value)
    }

    pub fn negate(self) -> Self {
        match self {
            Expr::Constant(r) => Expr::Constant(-r),
            Expr::Neg(inner) => *inner,
            other => Expr::Neg(Box::new(other)),
        }
    }

    pub fn is_zero(&self) -> bool {
        matches!(self, Expr::Constant(r) if r.is_zero())
    }

    pub fn is_one(&self) -> bool {
        matches!(self, Expr::Constant(r) if r.is_one())
    }

    pub fn as_variable(&self) -> Option<&str> {
        if let Expr::Variable(name) = self {
            Some(name)
        } else {
            None
        }
    }

    pub fn boxed(self) -> Box<Self> {
        Box::new(self)
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", crate::format::pretty(self))
    }
}

pub fn zero() -> Expr {
    Expr::Constant(Rational::zero())
}

pub fn one() -> Expr {
    Expr::Constant(Rational::one())
}

pub fn rational(num: i64, den: i64) -> Rational {
    Rational::new(num.into(), den.into())
}

pub fn pow(base: Expr, exp: Expr) -> Expr {
    Expr::Pow(base.boxed(), exp.boxed())
}

pub fn add(a: Expr, b: Expr) -> Expr {
    Expr::Add(a.boxed(), b.boxed())
}

pub fn sub(a: Expr, b: Expr) -> Expr {
    Expr::Sub(a.boxed(), b.boxed())
}

pub fn mul(a: Expr, b: Expr) -> Expr {
    Expr::Mul(a.boxed(), b.boxed())
}

pub fn div(a: Expr, b: Expr) -> Expr {
    Expr::Div(a.boxed(), b.boxed())
}

pub fn neg(a: Expr) -> Expr {
    Expr::Neg(a.boxed())
}
