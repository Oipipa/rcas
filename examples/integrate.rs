use rcas::prelude::inte;

fn main() {
    let expr = "1/(x^5+1)";
    let var = "x";

    match inte(expr, var) {
        Ok(result) => println!("integrate {expr} d{var} = {result}"),
        Err(err) => eprintln!("parse error for {expr}: {err}"),
    }
}
