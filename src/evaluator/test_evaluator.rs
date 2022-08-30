use crate::lexer::lexer::Lexer;
use crate::object::object::{Object, ObjectKind};
use crate::parser::parser::Parser;
use crate::{
    ast::{BlockStmt, Expr, ExprKind, Op, Program, Stmt, StmtKind},
    loc::Loc,
};

use super::evaluator::Evaluable;

fn new_dummy_loc() -> Loc {
    Loc::new(0, 0, 0, 0)
}

fn new_object(kind: ObjectKind) -> Object {
    let loc = new_dummy_loc();
    Object::new(kind, loc)
}

fn parse_and_eval(input: &str) -> Object {
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let mut prg = p
        .parse_expression(1)
        .expect("can not parse a prefix expression");
    prg.eval().expect("cannot evaluate a false")
}

//-----------------------------------------------------------------------------
// Unit tests of Literals
//-----------------------------------------------------------------------------
#[test]
fn test_eval_false() {
    let actual = parse_and_eval("false");
    let expect = new_object(ObjectKind::Boolean(false));
    assert_eq!(actual, expect)
}

#[test]
fn test_eval_true() {
    let actual = parse_and_eval("true");
    let expect = new_object(ObjectKind::Boolean(true));
    assert_eq!(actual, expect)
}
