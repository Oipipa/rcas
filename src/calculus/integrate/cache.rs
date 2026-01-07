use std::cell::RefCell;
use std::collections::HashMap;
use std::thread_local;

use crate::core::expr::Expr;

use super::types::NonElementaryKind;

thread_local! {
    pub(super) static NON_ELEM_CACHE: RefCell<HashMap<(Expr, String), Option<NonElementaryKind>>> =
        RefCell::new(HashMap::new());
    pub(super) static POLY_CACHE: RefCell<HashMap<(Expr, String), Option<usize>>> =
        RefCell::new(HashMap::new());
    pub(super) static IS_POLY_CACHE: RefCell<HashMap<(Expr, String), bool>> =
        RefCell::new(HashMap::new());
}
