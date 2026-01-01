use rcas::{integrate, parse_expr, pretty_integration_result};

fn main() {
    demo("non-elementary exp(x^2)", "exp(x^2)");
    demo("tricky by-parts x*sin(x)", "1/(x^2*(x^4+1)^3/4)");
}

fn demo(label: &str, input: &str) {
    println!("=== {label}: {input} ===");
    let expr = match parse_expr(input) {
        Ok(e) => e,
        Err(err) => {
            eprintln!("parse error for {input}: {err}");
            return;
        }
    };

    let result = integrate("x", &expr);
    for line in pretty_integration_result(&result) {
        println!("{line}");
    }
    println!();
}
