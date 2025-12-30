use crate::expr::{Expr, Rational};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

pub fn is_polynomial(expr: &Expr) -> bool {
    match expr {
        Expr::Constant(_) => true,
        Expr::Variable(_) => true,
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) => is_polynomial(a) && is_polynomial(b),
        Expr::Pow(base, exp) => {
            if let Expr::Constant(r) = &**exp {
                r.is_integer() && r >= &BigRational::zero() && is_polynomial(base)
            } else {
                false
            }
        }
        _ => false,
    }
}

pub fn integrate(expr: &Expr, var: &str) -> Option<Expr> {
    let var_expr = Expr::Variable(var.to_string());
    match expr {
        Expr::Constant(c) => Some(Expr::Mul(
            Expr::Constant(c.clone()).boxed(),
            var_expr.clone().boxed(),
        )),
        Expr::Variable(v) => {
            if v == var {
                Some(Expr::Div(
                    Expr::Pow(
                        var_expr.clone().boxed(),
                        Expr::Constant(Rational::from_integer(2.into())).boxed(),
                    )
                    .boxed(),
                    Expr::Constant(Rational::from_integer(2.into())).boxed(),
                ))
            } else {
                Some(Expr::Mul(
                    Expr::Variable(v.clone()).boxed(),
                    var_expr.clone().boxed(),
                ))
            }
        }
        Expr::Add(a, b) => Some(Expr::Add(
            integrate(a, var)?.boxed(),
            integrate(b, var)?.boxed(),
        )),
        Expr::Sub(a, b) => Some(Expr::Sub(
            integrate(a, var)?.boxed(),
            integrate(b, var)?.boxed(),
        )),
        Expr::Mul(a, b) => match (&**a, &**b) {
            (Expr::Constant(c), e) | (e, Expr::Constant(c)) => integrate(e, var)
                .map(|int| Expr::Mul(Expr::Constant(c.clone()).boxed(), int.boxed())),
            _ => None,
        },
        Expr::Pow(base, exp) => {
            if let (Expr::Variable(name), Expr::Constant(n)) = (&**base, &**exp) {
                if name == var && n.is_integer() {
                    let k: BigInt = n.to_integer() + 1;
                    return Some(Expr::Div(
                        Expr::Pow(
                            var_expr.clone().boxed(),
                            Expr::Constant(Rational::from_integer(k.clone())).boxed(),
                        )
                        .boxed(),
                        Expr::Constant(Rational::from_integer(k)).boxed(),
                    ));
                }
            }
            None
        }
        _ => None,
    }
}
