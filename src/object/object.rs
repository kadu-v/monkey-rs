use std::fmt::Display;

use crate::ast::{BlockStmt, Expr};
use crate::loc::Loc;
use crate::object::environment::Env;

#[derive(Debug, Clone)]
pub struct Object {
    pub kind: ObjectKind,
    pub loc: Loc,
}

impl Object {
    pub fn new(kind: ObjectKind, loc: Loc) -> Self {
        Self { kind, loc }
    }
}

impl PartialEq for Object {
    fn eq(&self, other: &Self) -> bool {
        self.kind.eq(&other.kind)
    }
}

impl Eq for Object {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObjectKind {
    Unit,
    Integer(isize),
    Boolean(bool),
    String(String),
    Return(Box<Object>),
    Function(Vec<Expr>, BlockStmt, Env),
    // Array(Vec<Object>),
    // Hash(...),
    // Builtin,
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            ObjectKind::Unit => write!(f, "()"),
            ObjectKind::Integer(i) => write!(f, "{}", i),
            ObjectKind::Boolean(b) => write!(f, "{}", b),
            ObjectKind::String(s) => write!(f, "{}", s),
            ObjectKind::Return(obj) => write!(f, "return {};", obj),
            ObjectKind::Function(_params, _body, _env) => write!(f, "function"),
        }
    }
}
