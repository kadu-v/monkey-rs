//-----------------------------------------------------------------------------
// Evaluator struct
//-----------------------------------------------------------------------------

use crate::ast::{BlockStmt, Expr, ExprKind, Op, Program, Stmt, StmtKind};
use crate::error::{EvalError, Result};
use crate::loc::Loc;
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
                let evaluated = body.eval(&mut extended_env)?;
                Self::unwrap_return_value(evaluated)
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

    pub fn unwrap_return_value(obj: Object) -> Result<Object> {
        match obj.kind {
            ObjectKind::Return(obj) => Ok(*obj),
            _ => Ok(obj),
        }
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
            ExprKind::LitString(s) => Ok(Object::new(ObjectKind::String(s.clone()), self.loc)),
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
                    (left_obj, right_obj) => Err(EvalError::new(
                        self.loc,
                        format!(
                            "expected a integer type:\n left: {:?}\n right: {:?}",
                            left_obj, right_obj
                        ),
                    )
                    .into()),
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
                    match &obj.kind {
                        ObjectKind::Function(args, body, fenv) => {
                            let mut fenv = fenv.clone();
                            fenv.set(ident, obj.clone());
                            Ok(Object::new(
                                ObjectKind::Function(args.clone(), body.clone(), fenv),
                                self.loc,
                            ))
                        }
                        _ => Ok(Object::new(obj.kind, self.loc)),
                    }
                } else {
                    Err(
                        EvalError::new(self.loc, format!("use a undefined identifier: {}", ident))
                            .into(),
                    )
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
            StmtKind::Let(ident, expr) => {
                if let ExprKind::Ident(ident) = &ident.kind {
                    let obj = expr.eval(env)?;
                    env.set(ident, obj);
                    Ok(Object::new(ObjectKind::Unit, self.loc))
                } else {
                    Err(
                        EvalError::new(ident.loc, "should be an identifier at let statement")
                            .into(),
                    )
                }
            }
            StmtKind::Return(expr) => {
                let obj = expr.eval(env)?;
                Ok(Object::new(ObjectKind::Return(obj.into()), self.loc))
            }
            StmtKind::ExprStmt(expr) => expr.eval(env),
            StmtKind::If(cond, block0, block1) => {
                let cond_obj = cond.eval(env)?;
                match cond_obj.kind {
                    ObjectKind::Boolean(true) => block0.eval(env),
                    ObjectKind::Boolean(false) => {
                        let loc = self.loc;
                        if let Some(block1) = block1 {
                            return block1.eval(env);
                        }
                        Ok(Object::new(ObjectKind::Unit, loc))
                    }
                    _ => Err(EvalError::new(self.loc, "condition should be boolean").into()),
                }
            }
        }
    }
}

//-----------------------------------------------------------------------------
// Block Statement
//-----------------------------------------------------------------------------

impl Evaluable for BlockStmt {
    fn eval(&self, env: &mut Env) -> Result<Object> {
        let block = &self.block;
        if block.len() == 0 {
            return Err(EvalError::new(self.loc, "block statement shuould be a non empty").into());
        }

        let mut obj = block[0].eval(env)?;

        for (i, stmt) in block.iter().enumerate() {
            if i == 0 {
                continue;
            }

            obj = stmt.eval(env)?;
        }

        Ok(obj)
    }
}

//-----------------------------------------------------------------------------
// Program
//-----------------------------------------------------------------------------

impl Evaluable for Program {
    fn eval(&self, env: &mut Env) -> Result<Object> {
        let mut obj = Object::new(ObjectKind::Unit, self.loc);
        for stmt in self.stmts.iter() {
            obj = stmt.eval(env)?;
        }
        Ok(obj)
    }
}
