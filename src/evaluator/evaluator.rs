//-----------------------------------------------------------------------------
// Evaluator struct
//-----------------------------------------------------------------------------

use std::iter::Product;

use crate::ast::{BlockStmt, Expr, ExprKind, Op, Program, Stmt, StmtKind};
use crate::error::{EvalError, Result};
use crate::object::{
    environment::Env,
    object::{Object, ObjectKind},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Eval {}

impl Eval {
    pub const fn new() -> Self {
        Self {}
    }

    // pub fn eval(&self, node: ) -> Result<Object> {}
}

//-----------------------------------------------------------------------------
// Evaluable trait
//-----------------------------------------------------------------------------
pub trait Evaluable {
    fn eval(&self, env: &mut Env) -> Result<Object>;
}

//-----------------------------------------------------------------------------
// Expression
//-----------------------------------------------------------------------------

impl Evaluable for Expr {
    fn eval(&self, env: &mut Env) -> Result<Object> {
        match &self.kind {
            ExprKind::LitInt(i) => Ok(Object::new(ObjectKind::Integer(*i), self.loc)),
            ExprKind::LitString(s) => unimplemented!("The case of LisString in eval"),
            ExprKind::LitBool(b) => Ok(Object::new(ObjectKind::Boolean(*b), self.loc)),
            ExprKind::Infix(op, ref left, ref right) => {
                let left_obj = left.eval(env)?;
                let right_obj = right.eval(env)?;

                match (left_obj.kind, right_obj.kind) {
                    (ObjectKind::Integer(i), ObjectKind::Integer(j)) => match op {
                        Op::Add => Ok(Object::new(
                            ObjectKind::Integer(i + j),
                            left_obj.loc + right_obj.loc,
                        )),
                        Op::Sub => unimplemented!(),
                        Op::Mul => unimplemented!(),
                        Op::Div => unimplemented!(),
                        Op::Eq => unimplemented!(),
                        Op::NotEq => unimplemented!(),
                        Op::Lt => unimplemented!(),
                        Op::Gt => unimplemented!(),
                        Op::Not => unimplemented!(),
                        _ => Err(EvalError::new(left.loc, "invalid infix oprator").into()),
                    },
                    _ => Err(EvalError::new(self.loc, "expected a integer type").into()),
                }
            }
            ExprKind::Prefix(op, ref expr) => {
                let obj = expr.eval(env)?;
                match (op, &obj.kind) {
                    (Op::Sub, &ObjectKind::Integer(i)) => {
                        Ok(Object::new(ObjectKind::Integer(-i), obj.loc))
                    }
                    (Op::Not, &ObjectKind::Boolean(b)) => {
                        Ok(Object::new(ObjectKind::Boolean(!b), obj.loc))
                    }
                    _ => Err(EvalError::new(self.loc, "invalid prefix operator").into()),
                }
            }
            ExprKind::Ident(ident) => {
                if let Some(obj) = env.get(ident) {
                    Ok(Object::new(obj.kind, obj.loc).into())
                } else {
                    Err(EvalError::new(self.loc, "use a undefined identifier").into())
                }
            }
            ExprKind::Call(func, params) => {
                unimplemented!("function call case")
            }
            _ => unimplemented!("woops!!"),
        }
    }
}

//-----------------------------------------------------------------------------
// Statement
//-----------------------------------------------------------------------------

impl Evaluable for Stmt {
    fn eval(&self, env: &mut Env) -> Result<Object> {
        match &self.kind {
            StmtKind::Let(ident, expr) => unimplemented!(),
            StmtKind::Return(expr) => unimplemented!(),
            StmtKind::ExprStmt(expr) => unimplemented!(),
            StmtKind::If(cond, expr0, expr1) => unimplemented!(),
        }
    }
}

//-----------------------------------------------------------------------------
// Block Statement
//-----------------------------------------------------------------------------

impl Evaluable for BlockStmt {
    fn eval(&self, env: &mut Env) -> Result<Object> {
        unimplemented!()
    }
}

//-----------------------------------------------------------------------------
// Program
//-----------------------------------------------------------------------------

impl Evaluable for Program {
    fn eval(&self, env: &mut Env) -> Result<Object> {
        unimplemented!()
    }
}
