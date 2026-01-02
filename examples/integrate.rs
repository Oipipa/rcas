use rcas::prelude::inte;

fn main() {
    let expr = "1/(1+sin(x/x))";
    let var = "x";

    match inte(expr, var) {
        Ok(result) => println!("integrate {expr} d{var} = {result}"),
        Err(err) => eprintln!("parse error for {expr}: {err}"),
    }
}
