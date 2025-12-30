use rcas::{parse_expr, pretty_solve_result, solve_system};

fn parse(input: &str) -> rcas::Expr {
    parse_expr(input).unwrap_or_else(|e| panic!("Failed to parse {input}: {e}"))
}

fn main() {
    let vars = vec!["x", "y", "z", "w"];
    let equations = vec![
        (parse("x + y + z + w"), parse("10")),
        (parse("2*x + 3*y - z + 4*w"), parse("20")),
        (parse("-x + y + 5*z - 2*w"), parse("3")),
        (parse("3*x - y + 2*z + w"), parse("14")),
    ];

    let result = solve_system(vars.iter().copied().collect(), equations);
    for line in pretty_solve_result(&result) {
        println!("{line}");
    }
}
