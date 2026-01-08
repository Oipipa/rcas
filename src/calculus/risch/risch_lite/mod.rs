use crate::calculus::integrate::{NonElementaryKind, detect_non_elementary, log_abs};
use crate::core::expr::Expr;
use crate::simplify::{normalize_for_risch, simplify};

mod integrate;
mod tower;
mod utils;

#[derive(Debug, Clone)]
pub enum RischLiteOutcome {
    Integrated { result: Expr, note: String },
    NonElementary { kind: NonElementaryKind, note: String },
    Indeterminate { note: String },
}

pub fn analyze(expr: &Expr, var: &str) -> RischLiteOutcome {
    let normalized = normalize_for_risch(expr.clone(), var);
    let tower = match tower::build_tower(&normalized, var) {
        Ok(tower) => tower,
        Err(note) => {
            if let Some(kind) = detect_non_elementary(&normalized, var) {
                return RischLiteOutcome::NonElementary {
                    kind,
                    note: format!("determinate non-elementary (tower: {note})"),
                };
            }
            return RischLiteOutcome::Indeterminate {
                note: format!("tower: {note}"),
            };
        }
    };

    if let Some((coeff, arg)) = integrate::log_derivative(&normalized, var) {
        let result = simplify(Expr::Mul(coeff.boxed(), log_abs(arg).boxed()));
        return RischLiteOutcome::Integrated {
            result,
            note: "logarithmic derivative (determinate)".to_string(),
        };
    }

    if let Some((result, note)) = integrate::integrate_in_tower(&normalized, var, &tower) {
        return RischLiteOutcome::Integrated {
            result,
            note: format!("{note} (determinate)"),
        };
    }

    if let Some(kind) = detect_non_elementary(expr, var) {
        return RischLiteOutcome::NonElementary {
            kind,
            note: "determinate non-elementary".to_string(),
        };
    }

    RischLiteOutcome::Indeterminate {
        note: "indeterminate".to_string(),
    }
}
