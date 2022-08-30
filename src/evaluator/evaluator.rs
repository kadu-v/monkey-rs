//-----------------------------------------------------------------------------
// Evaluator struct
//-----------------------------------------------------------------------------

use crate::ast::{Expr, ExprKind};
use crate::error::Result;
use crate::object::object::{Object, ObjectKind};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Eval {}

impl Eval {
    pub const fn new() -> Self {
        Self {}
    }

    // pub fn eval(&self, node: ) -> Result<Object> {}
}

//-----------------------------------------------------------------------------
// Evaluaable trait
//-----------------------------------------------------------------------------
pub trait Evaluable {
    fn eval(&mut self) -> Result<Object>;
}

//-----------------------------------------------------------------------------
// Expression
//-----------------------------------------------------------------------------

impl Evaluable for Expr {
    fn eval(&mut self) -> Result<Object> {
        match self.kind {
            ExprKind::LitInt(i) => Ok(Object::new(ObjectKind::Integer(i), self.loc)),
            ExprKind::LitBool(b) => Ok(Object::new(ObjectKind::Boolean(b), self.loc)),
            _ => unimplemented!("woops!!"),
        }
    }
}
