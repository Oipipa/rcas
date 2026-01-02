use crate::core::error::{CasError, Result};
use crate::core::expr::{Expr, Rational};
use nom::IResult;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::{alpha1, alphanumeric0, char, digit1, multispace0};
use nom::combinator::{all_consuming, map, opt, recognize};
use nom::error::VerboseError;
use nom::multi::fold_many0;
use nom::sequence::{delimited, pair, preceded, separated_pair};
use num_bigint::BigInt;
use num_traits::Num;

pub fn parse_expr(input: &str) -> Result<Expr> {
    match all_consuming(ws(parse_add_sub))(input) {
        Ok((_, expr)) => Ok(expr),
        Err(e) => Err(CasError::Parse(format!("{e:?}"))),
    }
}

fn parse_add_sub(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    let (rest, init) = parse_mul_div(input)?;
    fold_many0(
        pair(ws(alt((char('+'), char('-')))), parse_mul_div),
        move || init.clone(),
        |acc, (op, rhs)| match op {
            '+' => Expr::Add(acc.boxed(), rhs.boxed()),
            '-' => Expr::Sub(acc.boxed(), rhs.boxed()),
            _ => unreachable!(),
        },
    )(rest)
}

fn parse_mul_div(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    let (rest, init) = parse_pow(input)?;
    fold_many0(
        pair(ws(alt((char('*'), char('/')))), parse_pow),
        move || init.clone(),
        |acc, (op, rhs)| match op {
            '*' => Expr::Mul(acc.boxed(), rhs.boxed()),
            '/' => Expr::Div(acc.boxed(), rhs.boxed()),
            _ => unreachable!(),
        },
    )(rest)
}

fn parse_pow(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    let (rest, base) = parse_unary(input)?;
    if let Ok((next, exp)) = preceded(ws(char('^')), parse_pow)(rest) {
        Ok((next, Expr::Pow(base.boxed(), exp.boxed())))
    } else {
        Ok((rest, base))
    }
}

fn parse_unary(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    if let Ok((rest, expr)) = preceded(ws(char('-')), parse_unary)(input) {
        Ok((rest, Expr::Neg(expr.boxed())))
    } else {
        parse_primary(input)
    }
}

fn parse_primary(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    alt((
        parse_parens,
        parse_fraction,
        parse_function,
        parse_number,
        parse_identifier,
    ))(input)
}

fn parse_parens(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    delimited(ws(char('(')), parse_add_sub, ws(char(')')))(input)
}

fn parse_fraction(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    map(
        separated_pair(parse_int, ws(char('/')), parse_int),
        |(n, d)| Expr::Constant(Rational::new(n, d)),
    )(input)
}

fn parse_number(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    map(parse_int, |n| Expr::Constant(Rational::from_integer(n)))(input)
}

fn parse_identifier(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    map(ws(recognize(pair(alpha1, alphanumeric0))), |s: &str| {
        Expr::Variable(s.to_string())
    })(input)
}

fn parse_function(input: &str) -> IResult<&str, Expr, VerboseError<&str>> {
    let (rest, (name, arg)) = pair(
        parse_function_name,
        alt((
            delimited(ws(char('(')), parse_add_sub, ws(char(')'))),
            parse_primary,
        )),
    )(input)?;

    let expr = match name {
        "sin" => Expr::Sin(arg.boxed()),
        "cos" => Expr::Cos(arg.boxed()),
        "tan" => Expr::Tan(arg.boxed()),
        "sec" => Expr::Sec(arg.boxed()),
        "csc" => Expr::Csc(arg.boxed()),
        "cot" => Expr::Cot(arg.boxed()),
        "arctan" | "atan" => Expr::Atan(arg.boxed()),
        "arcsin" | "asin" => Expr::Asin(arg.boxed()),
        "arccos" | "acos" => Expr::Acos(arg.boxed()),
        "arcsec" | "asec" => Expr::Asec(arg.boxed()),
        "arccsc" | "acsc" => Expr::Acsc(arg.boxed()),
        "arccot" | "acot" => Expr::Acot(arg.boxed()),
        "sinh" => Expr::Sinh(arg.boxed()),
        "cosh" => Expr::Cosh(arg.boxed()),
        "tanh" => Expr::Tanh(arg.boxed()),
        "arcsinh" | "asinh" => Expr::Asinh(arg.boxed()),
        "arccosh" | "acosh" => Expr::Acosh(arg.boxed()),
        "arctanh" | "atanh" => Expr::Atanh(arg.boxed()),
        "exp" => Expr::Exp(arg.boxed()),
        "log" => Expr::Log(arg.boxed()),
        "abs" => Expr::Abs(arg.boxed()),
        _ => unreachable!(),
    };

    Ok((rest, expr))
}

fn parse_function_name(input: &str) -> IResult<&str, &str, VerboseError<&str>> {
    alt((
        alt((
            tag("arccosh"),
            tag("arcsinh"),
            tag("arctanh"),
            tag("arccos"),
            tag("arcsin"),
            tag("arctan"),
            tag("arcsec"),
            tag("arccsc"),
            tag("arccot"),
        )),
        alt((
            tag("acosh"),
            tag("asinh"),
            tag("atanh"),
            tag("acos"),
            tag("asin"),
            tag("atan"),
            tag("asec"),
            tag("acsc"),
            tag("acot"),
        )),
        alt((
            tag("cosh"),
            tag("sinh"),
            tag("tanh"),
            tag("cos"),
            tag("sin"),
            tag("tan"),
            tag("sec"),
            tag("csc"),
            tag("cot"),
        )),
        alt((tag("exp"), tag("log"), tag("abs"))),
    ))(input)
}

fn parse_int(input: &str) -> IResult<&str, BigInt, VerboseError<&str>> {
    map(ws(recognize(pair(opt(char('-')), digit1))), |s: &str| {
        BigInt::from_str_radix(s, 10).unwrap()
    })(input)
}

fn ws<'a, F, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O, VerboseError<&'a str>>
where
    F: FnMut(&'a str) -> IResult<&'a str, O, VerboseError<&'a str>>,
{
    delimited(multispace0, inner, multispace0)
}
