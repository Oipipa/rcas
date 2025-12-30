use crate::expr::Expr;

/// Substitute variable `var` with `replacement` throughout `expr`.
pub fn substitute(expr: &Expr, var: &str, replacement: &Expr) -> Expr {
    match expr {
        Expr::Variable(name) if name == var => replacement.clone(),
        Expr::Add(a, b) => Expr::Add(
            substitute(a, var, replacement).boxed(),
            substitute(b, var, replacement).boxed(),
        ),
        Expr::Sub(a, b) => Expr::Sub(
            substitute(a, var, replacement).boxed(),
            substitute(b, var, replacement).boxed(),
        ),
        Expr::Mul(a, b) => Expr::Mul(
            substitute(a, var, replacement).boxed(),
            substitute(b, var, replacement).boxed(),
        ),
        Expr::Div(a, b) => Expr::Div(
            substitute(a, var, replacement).boxed(),
            substitute(b, var, replacement).boxed(),
        ),
        Expr::Pow(a, b) => Expr::Pow(
            substitute(a, var, replacement).boxed(),
            substitute(b, var, replacement).boxed(),
        ),
        Expr::Neg(a) => Expr::Neg(substitute(a, var, replacement).boxed()),
        Expr::Sin(a) => Expr::Sin(substitute(a, var, replacement).boxed()),
        Expr::Cos(a) => Expr::Cos(substitute(a, var, replacement).boxed()),
        Expr::Tan(a) => Expr::Tan(substitute(a, var, replacement).boxed()),
        Expr::Exp(a) => Expr::Exp(substitute(a, var, replacement).boxed()),
        Expr::Log(a) => Expr::Log(substitute(a, var, replacement).boxed()),
        _ => expr.clone(),
    }
}
