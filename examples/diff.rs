use rcas::{differentiate, parse_expr, pretty, simplify_fully};

fn main() {
    match parse_expr("1/2*x") {
        Ok(expr) => {
            let derivative = simplify_fully(differentiate("x", &expr));
            println!("{}", pretty(&derivative));
        }
        Err(err) => eprintln!("parse error: {err}"),
    }
}
