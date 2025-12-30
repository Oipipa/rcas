use rcas::{parse_expr, pretty_solve_result, solve_system};

fn parse(input: &str) -> rcas::Expr {
    parse_expr(input).unwrap_or_else(|e| panic!("Failed to parse {input}: {e}"))
}

fn main() {
    let vars = vec!["x", "y"];
    let equations = vec![(parse("2*x+3*y"), parse("7")), (parse("x-4*y"), parse("1"))];

    let result = solve_system(vars.iter().copied().collect(), equations);
    for line in pretty_solve_result(&result) {
        println!("{line}");
    }
}
