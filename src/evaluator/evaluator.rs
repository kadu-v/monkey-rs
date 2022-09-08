//-----------------------------------------------------------------------------
// Evaluator struct
//-----------------------------------------------------------------------------

use std::f32::consts::E;

use crate::ast::{BlockStmt, Expr, ExprKind, Op, Program, Stmt, StmtKind};
use crate::error::{EvalError, Result};
use crate::loc::Loc;
use crate::object;
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

    pub fn eval_expressions(exprs: &Vec<Expr>, env: &mut Env) -> Result<Vec<Object>> {
        let mut objs = vec![];

        for expr in exprs.iter() {
            let evaluated = expr.eval(env)?;
            objs.push(evaluated);
        }
        Ok(objs)
    }

    pub fn apply_function(f: Object, args: Vec<Object>) -> Result<Object> {
        match f.kind {
            ObjectKind::Function(params, body, env) => {
                let mut extended_env = Self::extended_function_env(&params, env, &args, f.loc)?;
                body.eval(&mut extended_env)
            }
            _ => Err(EvalError::new(f.loc, "application should be a function object").into()),
        }
    }

    pub fn extended_function_env(
        params: &Vec<Expr>,
        env: Env,
        args: &Vec<Object>,
        loc: Loc,
    ) -> Result<Env> {
        let mut env = Env::new_enclosed_env(Box::new(env));

        for (i, param) in params.iter().enumerate() {
            match &param.kind {
                ExprKind::Ident(p) => {
                    env.set(p, args[i].clone());
                }
                _ => {
                    return Err(EvalError::new(loc, "parameters should be identifier").into());
                }
            }
        }
        Ok(env)
    }
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
            ExprKind::LitFunc(params, body) => Ok(Object::new(
                ObjectKind::Function(params.clone(), body.clone(), env.clone()),
                self.loc,
            )),
            ExprKind::Infix(op, ref left, ref right) => {
                let left_obj = left.eval(env)?;
                let right_obj = right.eval(env)?;

                match (left_obj.kind, right_obj.kind) {
                    (ObjectKind::Integer(i), ObjectKind::Integer(j)) => {
                        let kind = match op {
                            Op::Add => ObjectKind::Integer(i + j),
                            Op::Sub => ObjectKind::Integer(i - j),
                            Op::Mul => ObjectKind::Integer(i * j),
                            Op::Div => ObjectKind::Integer(i / j),
                            Op::Eq => ObjectKind::Boolean(i == j),
                            Op::NotEq => ObjectKind::Boolean(i != j),
                            Op::Lt => ObjectKind::Boolean(i < j),
                            Op::Gt => ObjectKind::Boolean(i > j),
                            _ => {
                                return Err(EvalError::new(left.loc, "invalid infix oprator").into())
                            }
                        };

                        Ok(Object::new(kind, left_obj.loc + right_obj.loc))
                    }
                    (ObjectKind::Boolean(b), ObjectKind::Boolean(c)) => {
                        let kind = match op {
                            Op::Eq => ObjectKind::Boolean(b == c),
                            Op::NotEq => ObjectKind::Boolean(b != c),
                            _ => {
                                return Err(EvalError::new(left.loc, "invalid infix oprator").into())
                            }
                        };

                        Ok(Object::new(kind, left_obj.loc + right_obj.loc))
                    }
                    #[allow(unreachable_patterns)]
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
                let f = func.eval(env)?;
                let args = Eval::eval_expressions(params, env)?;
                Eval::apply_function(f, args)
            }
            #[allow(unreachable_patterns)]
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
