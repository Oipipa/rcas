use rcas::prelude::{norm, simp};

fn main() {
    let simplify_expr = "x*(x+1) - x*x";

    match simp(simplify_expr) {
        Ok(result) => println!("simplify {simplify_expr} => {result}"),
        Err(err) => eprintln!("parse error for {simplify_expr}: {err}"),
    }

    let normalize_expr = "(x^2)^(1/2)";
    match norm(normalize_expr) {
        Ok(result) => println!("normalize {normalize_expr} => {result}"),
        Err(err) => eprintln!("parse error for {normalize_expr}: {err}"),
    }
}
