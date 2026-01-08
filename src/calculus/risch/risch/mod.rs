use crate::calculus::integrate::NonElementaryKind;
use crate::core::expr::Expr;
use crate::core::polynomial::Polynomial;
use crate::simplify::{normalize_for_risch, simplify_fully};

mod algebraic;
mod expr_poly;
mod integrate;
mod ode;
mod tower;
mod utils;

type ExprPoly = Polynomial<Expr>;

#[derive(Debug, Clone)]
pub enum RischOutcome {
    Integrated { result: Expr, note: String },
    NonElementary { kind: NonElementaryKind, note: String },
    Indeterminate { note: String },
}

enum RischStep {
    Integrated { result: Expr, note: String },
    NonElementary { note: String },
    Indeterminate { note: String },
}

pub fn analyze(expr: &Expr, var: &str) -> RischOutcome {
    let normalized = normalize_for_risch(expr.clone(), var);
    let simplified = simplify_fully(normalized);
    if let Some(outcome) = algebraic::analyze_algebraic(&simplified, var) {
        return outcome;
    }
    let tower = match tower::build_tower(&simplified, var) {
        Ok(tower) => tower,
        Err(note) => {
            return RischOutcome::Indeterminate {
                note: format!("tower: {note}"),
            };
        }
    };

    if tower.extensions().is_empty() {
        return RischOutcome::Indeterminate {
            note: "no transcendental generators".to_string(),
        };
    }
    let expr_sym = tower.replace_generators(&simplified);
    match integrate::integrate_in_tower(&expr_sym, var, &tower) {
        RischStep::Integrated { result, note } => {
            let restored = tower.expand_symbols(&result);
            RischOutcome::Integrated {
                result: simplify_fully(restored),
                note,
            }
        }
        RischStep::NonElementary { note } => RischOutcome::NonElementary {
            kind: NonElementaryKind::SpecialFunctionNeeded,
            note,
        },
        RischStep::Indeterminate { note } => RischOutcome::Indeterminate { note },
    }
}
