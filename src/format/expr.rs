use crate::expr::Expr;
use num_rational::BigRational;

pub fn pretty(expr: &Expr) -> String {
    fn pp(ctx: u8, expr: &Expr) -> String {
        match expr {
            Expr::Variable(v) => v.clone(),
            Expr::Constant(r) => show_rational(r),

            Expr::Add(a, b) => {
                let s_a = pp(1, a);
                let (neg_b, b_inner) = split_neg(b);
                let s_b = pp(2, &b_inner);
                let body = format!("{s_a}{}{}", if neg_b { "-" } else { "+" }, s_b);
                bracket(ctx, 1, body)
            }

            Expr::Sub(a, b) => {
                let s_a = pp(1, a);
                let (neg_b, b_inner) = split_neg(b);
                let s_b = pp(2, &b_inner);
                let body = format!("{s_a}{}{}", if neg_b { "+" } else { "-" }, s_b);
                bracket(ctx, 1, body)
            }

            Expr::Mul(a, b) => {
                let (na, a_inner) = split_neg(a);
                let (nb, b_inner) = split_neg(b);
                let body = format!("{}*{}", pp(2, &a_inner), pp(2, &b_inner));
                if na ^ nb {
                    bracket(ctx, 2, format!("-({body})"))
                } else {
                    bracket(ctx, 2, body)
                }
            }

            Expr::Div(a, b) => {
                let (na, a_inner) = split_neg(a);
                let (nb, b_inner) = split_neg(b);
                let body = format!("{} / {}", pp(2, &a_inner), pp(3, &b_inner));
                if na ^ nb {
                    bracket(ctx, 2, format!("-({body})"))
                } else {
                    bracket(ctx, 2, body)
                }
            }

            Expr::Pow(a, b) => bracket(ctx, 3, format!("{}^{}", pp(4, a), pp(3, b))),

            Expr::Neg(a) => {
                let (is_neg, inner) = split_neg(a);
                if is_neg {
                    pp(4, &inner)
                } else {
                    format!("-{}", pp(4, &inner))
                }
            }

            Expr::Sin(a) => format!("sin({})", pp(0, a)),
            Expr::Cos(a) => format!("cos({})", pp(0, a)),
            Expr::Tan(a) => format!("tan({})", pp(0, a)),
            Expr::Atan(a) => format!("arctan({})", pp(0, a)),
            Expr::Asin(a) => format!("arcsin({})", pp(0, a)),
            Expr::Acos(a) => format!("arccos({})", pp(0, a)),
            Expr::Exp(a) => format!("exp({})", pp(0, a)),
            Expr::Log(a) => format!("log({})", pp(0, a)),
            Expr::Abs(a) => format!("abs({})", pp(0, a)),
        }
    }

    pp(0, expr)
}

fn split_neg(expr: &Expr) -> (bool, Expr) {
    match expr {
        Expr::Neg(inner) => (true, *inner.clone()),
        Expr::Constant(r) if r < &BigRational::from_integer(0.into()) => (true, Expr::Constant(-r)),
        other => (false, other.clone()),
    }
}

fn bracket(ctx: u8, prec: u8, body: String) -> String {
    if prec < ctx {
        format!("({body})")
    } else {
        body
    }
}

fn show_rational(r: &BigRational) -> String {
    let n = r.numer().clone();
    let d = r.denom().clone();
    if d == 1.into() {
        format!("{n}")
    } else if n < 0.into() {
        format!("-{}/{}", -n, d)
    } else {
        format!("{}/{}", n, d)
    }
}
