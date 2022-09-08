use crate::lexer::lexer::Lexer;
use crate::object::environment::Env;
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

fn new_ident(x: impl Into<String>) -> Expr {
    let kind = ExprKind::Ident(x.into());
    Expr::new(kind, new_dummy_loc())
}

fn new_int(x: isize) -> Expr {
    let kind = ExprKind::LitInt(x);
    Expr::new(kind, new_dummy_loc())
}

fn parse_and_eval(input: &str) -> Object {
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let prg = p
        .parse_expression(0)
        .expect("can not parse a prefix expression");
    let mut env = Env::new();
    let loc = new_dummy_loc();
    env.set("i", Object::new(ObjectKind::Integer(1), new_dummy_loc()));
    env.set("b", Object::new(ObjectKind::Boolean(true), new_dummy_loc()));
    env.set(
        "f",
        Object::new(
            ObjectKind::Function(
                vec![new_ident("x")],
                BlockStmt::new(
                    vec![Stmt::new(
                        StmtKind::Return(
                            Expr::new(
                                ExprKind::Infix(Op::Add, new_ident("x").into(), new_int(1).into()),
                                loc,
                            )
                            .into(),
                        ),
                        loc,
                    )],
                    loc,
                ),
                Env::new(),
            ),
            loc,
        ),
    );

    prg.eval(&mut env).expect("cannot evaluate a false")
}
//-----------------------------------------------------------------------------
// Unit tests of Literals
//-----------------------------------------------------------------------------
#[test]
fn test_eval_false() {
    let actual = parse_and_eval("false");
    let expect = new_object(ObjectKind::Boolean(false));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_true() {
    let actual = parse_and_eval("true");
    let expect = new_object(ObjectKind::Boolean(true));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_integer() {
    let actual = parse_and_eval("1");
    let expect = new_object(ObjectKind::Integer(1));
    assert_eq!(expect, actual)
}

//-----------------------------------------------------------------------------
// Unit tests of Expression
//-----------------------------------------------------------------------------

#[test]
fn test_eval_infix_add1() {
    let actual = parse_and_eval("1 + 1");
    let expect = new_object(ObjectKind::Integer(2));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_add2() {
    let actual = parse_and_eval("1 + 1 + 2");
    let expect = new_object(ObjectKind::Integer(4));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_sub1() {
    let actual = parse_and_eval("1 - 1");
    let expect = new_object(ObjectKind::Integer(0));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_sub2() {
    let actual = parse_and_eval("1 + 1 - 2");
    let expect = new_object(ObjectKind::Integer(0));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_mul1() {
    let actual = parse_and_eval("1 * 2");
    let expect = new_object(ObjectKind::Integer(2));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_mul2() {
    let actual = parse_and_eval("1 + 1 * 2");
    let expect = new_object(ObjectKind::Integer(3));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_div1() {
    let actual = parse_and_eval("1 / 2");
    let expect = new_object(ObjectKind::Integer(0));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_div2() {
    let actual = parse_and_eval("1 + 1 / 2");
    let expect = new_object(ObjectKind::Integer(1));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_eq1() {
    let actual = parse_and_eval("1 == 1");
    let expect = new_object(ObjectKind::Boolean(true));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_eq2() {
    let actual = parse_and_eval("1 == 1 * 3");
    let expect = new_object(ObjectKind::Boolean(false));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_noteq1() {
    let actual = parse_and_eval("1 != 1");
    let expect = new_object(ObjectKind::Boolean(false));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_noteq2() {
    let actual = parse_and_eval("1 + 1 != 2");
    let expect = new_object(ObjectKind::Boolean(false));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_lt1() {
    let actual = parse_and_eval("1 < 1");
    let expect = new_object(ObjectKind::Boolean(false));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_lt2() {
    let actual = parse_and_eval("1 < 1 * 2");
    let expect = new_object(ObjectKind::Boolean(true));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_gt1() {
    let actual = parse_and_eval("1 > 1");
    let expect = new_object(ObjectKind::Boolean(false));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_infix_gt2() {
    let actual = parse_and_eval("1 * 3 > 2");
    let expect = new_object(ObjectKind::Boolean(true));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_prefix_sub1() {
    let actual = parse_and_eval("-1");
    let expect = new_object(ObjectKind::Integer(-1));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_prefix_sub2() {
    let actual = parse_and_eval("-(1 + 1 * 4)");
    let expect = new_object(ObjectKind::Integer(-5));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_prefix_not1() {
    let actual = parse_and_eval("!true");
    let expect = new_object(ObjectKind::Boolean(false));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_prefix_not2() {
    let actual = parse_and_eval("!(1 > 2 * 3)");
    let expect = new_object(ObjectKind::Boolean(true));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_ident1() {
    let actual = parse_and_eval("i");
    let expect = new_object(ObjectKind::Integer(1));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_ident2() {
    let actual = parse_and_eval("b");
    let expect = new_object(ObjectKind::Boolean(true));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_call1() {
    let actual = parse_and_eval("f(1)");
    let expect = new_object(ObjectKind::Integer(2));
    assert_eq!(expect, actual)
}

#[test]
fn test_eval_call2() {
    let actual = parse_and_eval("(fn(x) { return x + i; })(1)");
    let expect = new_object(ObjectKind::Integer(2));
    assert_eq!(expect, actual)
}
