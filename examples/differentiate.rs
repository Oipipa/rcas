use rcas::prelude::diff;

fn main() {
    let expr = "sin(x)*exp(x)";
    let var = "x";

    match diff(expr, var) {
        Ok(result) => println!("d/d{var} {expr} = {result}"),
        Err(err) => eprintln!("parse error for {expr}: {err}"),
    }
}
