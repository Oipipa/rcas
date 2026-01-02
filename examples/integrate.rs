use rcas::prelude::inte;

fn main() {
    let expr = "(2*x-x^2)^1/2";
    let var = "x";

    match inte(expr, var) {
        Ok(result) => println!("integrate {expr} d{var} = {result}"),
        Err(err) => eprintln!("parse error for {expr}: {err}"),
    }
}
