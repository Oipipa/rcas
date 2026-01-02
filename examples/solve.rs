use rcas::prelude::solve_eqs;

fn main() {
    let vars = ["x", "y", "z"];
    let equations = ["2*x + 3*y + 8*z = 7", "x - 4*y + 6*z = 1", "3*x-y-z=8"];

    match solve_eqs(&vars, &equations) {
        Ok(lines) => println!("{}", lines.join("\n")),
        Err(err) => eprintln!("parse error: {err}"),
    }
}
