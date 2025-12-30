use crate::expr::{Expr, Rational};

pub fn is_log(expr: &Expr) -> bool {
    match expr {
        Expr::Div(a, b) => matches!(
            (&**a, &**b),
            (Expr::Constant(r), Expr::Variable(_))
                if *r == Rational::from_integer(1.into())
        ),
        Expr::Log(_) => true,
        _ => false,
    }
}

pub fn integrate(expr: &Expr, var: &str) -> Option<Expr> {
    match expr {
        Expr::Div(a, b) => match (&**a, &**b) {
            (Expr::Constant(r), Expr::Variable(v))
                if *r == Rational::from_integer(1.into()) && v == var =>
            {
                Some(Expr::Log(Expr::Variable(v.clone()).boxed()))
            }
            _ => None,
        },
        Expr::Log(u) => Some(Expr::Sub(
            Expr::Mul(u.clone(), Expr::Log(u.clone()).boxed()).boxed(),
            u.clone(),
        )),
        _ => None,
    }
}
