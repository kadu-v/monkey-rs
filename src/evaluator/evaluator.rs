//-----------------------------------------------------------------------------
// Evaluator struct
//-----------------------------------------------------------------------------

use crate::ast::{Expr, ExprKind, Op};
use crate::error::{EvalError, Result};
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
    fn eval(&self) -> Result<Object>;
}

//-----------------------------------------------------------------------------
// Expression
//-----------------------------------------------------------------------------

impl Evaluable for Expr {
    fn eval(&self) -> Result<Object> {
        match &self.kind {
            ExprKind::LitInt(i) => Ok(Object::new(ObjectKind::Integer(*i), self.loc)),
            ExprKind::LitString(s) => unimplemented!("The case of LisString in eval"),
            ExprKind::LitBool(b) => Ok(Object::new(ObjectKind::Boolean(*b), self.loc)),
            ExprKind::Infix(op, ref left, ref right) => {
                let left_obj = left.eval()?;
                let right_obj = right.eval()?;

                match (left_obj.kind, right_obj.kind) {
                    (ObjectKind::Integer(i), ObjectKind::Integer(j)) => match op {
                        &Op::Add => Ok(Object::new(
                            ObjectKind::Integer(i + j),
                            left_obj.loc + right_obj.loc,
                        )),
                        _ => Err(EvalError::new(left.loc, "invalid infix oprator").into()),
                    },
                    _ => Err(EvalError::new(left.loc, "expected a integer type").into()),
                }
            }
            _ => unimplemented!("woops!!"),
        }
    }
}
