use rcas::prelude::inte;

fn main() {
    let expr = "tan(log(x))^3/x";
    let var = "x";

    match inte(expr, var) {
        Ok(result) => println!("integrate {expr} d{var} = {result}"),
        Err(err) => eprintln!("parse error for {expr}: {err}"),
    }
}
