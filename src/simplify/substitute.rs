use crate::core::expr::Expr;

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
        Expr::Sec(a) => Expr::Sec(substitute(a, var, replacement).boxed()),
        Expr::Csc(a) => Expr::Csc(substitute(a, var, replacement).boxed()),
        Expr::Cot(a) => Expr::Cot(substitute(a, var, replacement).boxed()),
        Expr::Atan(a) => Expr::Atan(substitute(a, var, replacement).boxed()),
        Expr::Asin(a) => Expr::Asin(substitute(a, var, replacement).boxed()),
        Expr::Acos(a) => Expr::Acos(substitute(a, var, replacement).boxed()),
        Expr::Asec(a) => Expr::Asec(substitute(a, var, replacement).boxed()),
        Expr::Acsc(a) => Expr::Acsc(substitute(a, var, replacement).boxed()),
        Expr::Acot(a) => Expr::Acot(substitute(a, var, replacement).boxed()),
        Expr::Sinh(a) => Expr::Sinh(substitute(a, var, replacement).boxed()),
        Expr::Cosh(a) => Expr::Cosh(substitute(a, var, replacement).boxed()),
        Expr::Tanh(a) => Expr::Tanh(substitute(a, var, replacement).boxed()),
        Expr::Asinh(a) => Expr::Asinh(substitute(a, var, replacement).boxed()),
        Expr::Acosh(a) => Expr::Acosh(substitute(a, var, replacement).boxed()),
        Expr::Atanh(a) => Expr::Atanh(substitute(a, var, replacement).boxed()),
        Expr::Exp(a) => Expr::Exp(substitute(a, var, replacement).boxed()),
        Expr::Log(a) => Expr::Log(substitute(a, var, replacement).boxed()),
        Expr::Abs(a) => Expr::Abs(substitute(a, var, replacement).boxed()),
        _ => expr.clone(),
    }
}
