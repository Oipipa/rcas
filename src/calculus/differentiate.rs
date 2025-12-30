use crate::expr::{Expr, Rational, one};
use crate::simplify::{simplify, simplify_add, simplify_sub};
use num_traits::{One, Zero};

pub fn differentiate(var: &str, expr: &Expr) -> Expr {
    Differentiator { var }.derive(expr)
}

struct Differentiator<'a> {
    var: &'a str,
}

impl<'a> Differentiator<'a> {
    fn derive(&self, expr: &Expr) -> Expr {
        match expr {
            Expr::Variable(name) if name == self.var => Expr::Constant(Rational::one()),
            Expr::Variable(_) => Expr::Constant(Rational::zero()),
            Expr::Constant(_) => Expr::Constant(Rational::zero()),

            Expr::Add(a, b) => simplify_add(self.derive(a), self.derive(b)),
            Expr::Sub(a, b) => simplify_sub(self.derive(a), self.derive(b)),
            Expr::Mul(a, b) => self.product_rule(a, b),
            Expr::Div(a, b) => self.quotient_rule(a, b),
            Expr::Pow(a, b) => self.power_rule(a, b),
            Expr::Neg(a) => simplify(Expr::Neg(self.derive(a).boxed())),

            Expr::Sin(a) => self.chain_rule(a, |inner| Expr::Cos(inner.boxed())),
            Expr::Cos(a) => simplify(Expr::Neg(
                self.chain_rule(a, |inner| Expr::Sin(inner.boxed())).boxed(),
            )),
            Expr::Tan(a) => {
                let da = self.strip_one(self.derive(a));
                let sec2 = Expr::Div(
                    Expr::Constant(Rational::one()).boxed(),
                    Expr::Pow(
                        Expr::Cos(a.clone()).boxed(),
                        Expr::Constant(Rational::from_integer(2.into())).boxed(),
                    )
                    .boxed(),
                );
                simplify(Expr::Mul(da.boxed(), sec2.boxed()))
            }

            Expr::Exp(a) => simplify(Expr::Mul(
                self.derive(a).boxed(),
                Expr::Exp(a.clone()).boxed(),
            )),
            Expr::Log(a) => simplify(Expr::Div(self.derive(a).boxed(), a.clone().boxed())),
        }
    }

    fn product_rule(&self, a: &Expr, b: &Expr) -> Expr {
        let da = self.derive(a);
        let db = self.derive(b);
        simplify(Expr::Add(
            self.strip_one(Expr::Mul(da.boxed(), b.clone().boxed()))
                .boxed(),
            self.strip_one(Expr::Mul(a.clone().boxed(), db.boxed()))
                .boxed(),
        ))
    }

    fn quotient_rule(&self, a: &Expr, b: &Expr) -> Expr {
        simplify(Expr::Div(
            Expr::Sub(
                Expr::Mul(self.derive(a).boxed(), b.clone().boxed()).boxed(),
                Expr::Mul(a.clone().boxed(), self.derive(b).boxed()).boxed(),
            )
            .boxed(),
            Expr::Pow(
                b.clone().boxed(),
                Expr::Constant(Rational::from_integer(2.into())).boxed(),
            )
            .boxed(),
        ))
    }

    fn power_rule(&self, base: &Expr, exp: &Expr) -> Expr {
        match exp {
            Expr::Constant(n) => {
                let db = self.derive(base);
                simplify(Expr::Mul(
                    Expr::Mul(
                        Expr::Constant(n.clone()).boxed(),
                        Expr::Pow(
                            base.clone().boxed(),
                            Expr::Constant(n - Rational::one()).boxed(),
                        )
                        .boxed(),
                    )
                    .boxed(),
                    db.boxed(),
                ))
            }
            _ => {
                let f = Expr::Pow(base.clone().boxed(), exp.clone().boxed());
                let da = self.derive(base);
                let db = self.derive(exp);
                simplify(Expr::Mul(
                    f.boxed(),
                    Expr::Add(
                        Expr::Mul(db.boxed(), Expr::Log(base.clone().boxed()).boxed()).boxed(),
                        Expr::Div(
                            Expr::Mul(exp.clone().boxed(), da.boxed()).boxed(),
                            base.clone().boxed(),
                        )
                        .boxed(),
                    )
                    .boxed(),
                ))
            }
        }
    }

    fn chain_rule<F>(&self, arg: &Expr, outer: F) -> Expr
    where
        F: Fn(Expr) -> Expr,
    {
        let da = self.strip_one(self.derive(arg));
        simplify(Expr::Mul(da.boxed(), outer(arg.clone()).boxed()))
    }

    fn flatten_mul(&self, expr: &Expr) -> Vec<Expr> {
        match expr {
            Expr::Mul(a, b) => {
                let mut out = self.flatten_mul(a);
                out.extend(self.flatten_mul(b));
                out
            }
            other => vec![other.clone()],
        }
    }

    fn strip_one(&self, expr: Expr) -> Expr {
        if !self.contains_one(&expr) {
            return expr;
        }
        let factors = self.flatten_mul(&expr);
        let filtered: Vec<Expr> = factors
            .into_iter()
            .filter(|e| !matches!(e, Expr::Constant(c) if c.is_one()))
            .collect();
        match filtered.len() {
            0 => one(),
            1 => filtered.into_iter().next().unwrap(),
            _ => filtered
                .into_iter()
                .reduce(|a, b| Expr::Mul(a.boxed(), b.boxed()))
                .unwrap(),
        }
    }

    fn contains_one(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Mul(a, b) => self.contains_one(a) || self.contains_one(b),
            Expr::Constant(c) => c.is_one(),
            _ => false,
        }
    }
}
