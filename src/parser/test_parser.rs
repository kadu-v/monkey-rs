use crate::ast::Program;
use crate::lexer::lexer::Lexer;
use crate::parser::parser::Parser;
use crate::{
    ast::{BlockStmt, Expr, ExprKind, Ident, Op, Stmt, StmtKind},
    loc::Loc,
};

use super::parser::LOWEST;

//-----------------------------------------------------------------------------
// Helper functions for unit tests of AST
//-----------------------------------------------------------------------------

fn assert_stmt(expect: Stmt, actual: Stmt) {
    match (expect.kind.clone(), actual.kind.clone()) {
        (StmtKind::Let(ident0, expr0), StmtKind::Let(ident1, expr1)) => {
            assert_ident(ident0, ident1);
            assert_exp(*expr0, *expr1);
        }
        _ => assert_eq!(expect.kind, actual.kind),
    }
}

fn assert_ident(expect: Ident, actual: Ident) {
    assert_eq!(expect.name, actual.name)
}

fn assert_exp(expect: Expr, actual: Expr) {
    match (expect.kind.clone(), actual.kind.clone()) {
        (ExprKind::LitInt(n0), ExprKind::LitInt(n1)) => {
            assert_eq!(n0, n1);
        }
        (ExprKind::LitString(s0), ExprKind::LitString(s1)) => {
            assert_eq!(s0, s1);
        }
        (ExprKind::LitBool(b0), ExprKind::LitBool(b1)) => {
            assert_eq!(b0, b1);
        }
        (ExprKind::LitFunc(idents0, block0), ExprKind::LitFunc(idents1, block1)) => {
            for (ident0, ident1) in idents0.into_iter().zip(idents1) {
                assert_ident(ident0, ident1);
            }
            assert_block_stmt(block0, block1);
        }
        (ExprKind::LitArray(arry0), ExprKind::LitArray(arry1)) => {
            for (i0, i1) in arry0.into_iter().zip(arry1) {
                assert_exp(i0, i1);
            }
        }
        (ExprKind::Infix(op0, expr0, expr1), ExprKind::Infix(op1, expr2, expr3)) => {
            assert_eq!(op0, op1);
            assert_exp(*expr0, *expr2);
            assert_exp(*expr1, *expr3);
        }
        (ExprKind::Prefix(op0, expr0), ExprKind::Prefix(op1, expr1)) => {
            assert_eq!(op0, op1);
            assert_exp(*expr0, *expr1);
        }

        (ExprKind::If(expr0, block0, block1), ExprKind::If(expr3, block2, block3)) => {
            assert_exp(*expr0, *expr3);
            assert_block_stmt(block0, block1);
            assert_block_stmt(block2, block3);
        }
        _ => assert_eq!(expect.kind, actual.kind),
    }
}

fn assert_block_stmt(expect: BlockStmt, actual: BlockStmt) {
    todo!("can not implement a assert_blockstmt")
}

fn new_dummy_loc() -> Loc {
    Loc::new(0, 0, 0, 0)
}

fn new_expr_lit_integer(n: usize) -> Expr {
    let kind = ExprKind::LitInt(n);
    let loc = new_dummy_loc();
    Expr::new(kind, loc)
}

fn new_expr_lit_string(s: String) -> Expr {
    let kind = ExprKind::LitString(s);
    let loc = new_dummy_loc();
    Expr::new(kind, loc)
}

fn new_expr_lit_bool(b: bool) -> Expr {
    let kind = ExprKind::LitBool(b);
    let loc = new_dummy_loc();
    Expr::new(kind, loc)
}

fn new_expr_lit_func(func: Vec<Ident>, block: BlockStmt) -> Expr {
    let kind = ExprKind::LitFunc(func, block);
    let loc = new_dummy_loc();
    Expr::new(kind, loc)
}

fn new_expr_lit_array(arry: Vec<Expr>) -> Expr {
    let kind = ExprKind::LitArray(arry);
    let loc = new_dummy_loc();
    Expr::new(kind, loc)
}

fn new_expr_infix(op: Op, expr0: Expr, expr1: Expr) -> Expr {
    let kind = ExprKind::Infix(op, expr0.into(), expr1.into());
    let loc = new_dummy_loc();
    Expr::new(kind, loc)
}

fn new_expr_prefix(op: Op, expr0: Expr) -> Expr {
    let kind = ExprKind::Prefix(op, expr0.into());
    let loc = new_dummy_loc();
    Expr::new(kind, loc)
}

fn new_expr_if(expr0: Expr, block0: BlockStmt, block1: BlockStmt) -> Expr {
    let kind = ExprKind::If(expr0.into(), block0, block1);
    let loc = new_dummy_loc();
    Expr::new(kind, loc)
}

fn new_expr_call(expr0: Expr, exprs: Vec<Expr>) -> Expr {
    let kind = ExprKind::Call(expr0.into(), exprs);
    let loc = new_dummy_loc();
    Expr::new(kind, loc)
}

fn new_expr_index(expr0: Expr, expr1: Expr) -> Expr {
    let kind = ExprKind::Index(expr0.into(), expr1.into());
    let loc = new_dummy_loc();
    Expr::new(kind, loc)
}

fn new_stmt_let(ident: Ident, expr: Expr) -> Stmt {
    let kind = StmtKind::Let(ident, expr.into());
    let loc = new_dummy_loc();
    Stmt::new(kind, loc)
}

fn new_stmt_return(expr: Expr) -> Stmt {
    let kind = StmtKind::Return(expr.into());
    let loc = new_dummy_loc();
    Stmt::new(kind, loc)
}

fn new_stmt_exprstmt(expr: Expr) -> Stmt {
    let kind = StmtKind::ExprStmt(expr.into());
    let loc = new_dummy_loc();
    Stmt::new(kind, loc)
}

fn new_ident(name: String) -> Ident {
    let loc = new_dummy_loc();
    Ident::new(name, loc)
}

fn new_program(stmts: Vec<Stmt>) -> Program {
    Program::new(stmts)
}

#[test]
fn test_parse_let_expression() {
    let input = "let x = 1;";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_let_statement()
        .expect("can not parse let expression");

    let expect = new_stmt_let(new_ident("x".to_string()), new_expr_lit_integer(1));
    assert_stmt(expect, actual)
}

//-----------------------------------------------------------------------------
// Unit tests of Prefix Expressions
//-----------------------------------------------------------------------------

#[test]
fn test_parse_prefix_expression_minus_one() {
    let input = "-1";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_prefix_expression()
        .expect("can not parse a prefix expression");

    let expect = new_expr_prefix(Op::Sub, new_expr_lit_integer(1));

    assert_exp(expect, actual)
}

#[test]
fn test_parse_prefix_expression_not_true() {
    let input = "!true";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_prefix_expression()
        .expect("can not parse a prefix_expression");

    let expect = new_expr_prefix(Op::Not, new_expr_lit_bool(true));

    assert_exp(expect, actual)
}

//-----------------------------------------------------------------------------
// Unit tests of Infix Expression
//-----------------------------------------------------------------------------

#[test]
fn test_parse_infix_expression_add() {
    let input = "1 + 2";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = new_expr_infix(Op::Add, new_expr_lit_integer(1), new_expr_lit_integer(2));

    assert_exp(expect, actual)
}

#[test]
fn test_parse_infix_expression_sub() {
    let input = "1 - 10";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = new_expr_infix(Op::Sub, new_expr_lit_integer(1), new_expr_lit_integer(10));

    assert_exp(expect, actual)
}

#[test]
fn test_parse_infix_expression_mul() {
    let input = "10 * 10";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = new_expr_infix(Op::Mul, new_expr_lit_integer(10), new_expr_lit_integer(10));

    assert_exp(expect, actual)
}

#[test]
fn test_parse_infix_expression_div() {
    let input = "1 / 10";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = new_expr_infix(Op::Div, new_expr_lit_integer(1), new_expr_lit_integer(10));

    assert_exp(expect, actual)
}

#[test]
fn test_parse_infix_expression_eq() {
    let input = "true == false";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = new_expr_infix(Op::Eq, new_expr_lit_bool(true), new_expr_lit_bool(false));

    assert_exp(expect, actual)
}

#[test]
fn test_parse_infix_expression_noteq() {
    let input = "true != false";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = new_expr_infix(Op::NotEq, new_expr_lit_bool(true), new_expr_lit_bool(false));

    assert_exp(expect, actual)
}

#[test]
fn test_parse_infix_expression_paren() {
    let input = "(1 + 2)";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = new_expr_infix(Op::Add, new_expr_lit_integer(1), new_expr_lit_integer(2));

    assert_exp(expect, actual)
}

//-----------------------------------------------------------------------------
// Unit tests of Expressions
//-----------------------------------------------------------------------------

#[test]
fn test_parse_precedence_of_expression1() {
    let input = "1 + 2 * 3";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = new_expr_infix(
        Op::Add,
        new_expr_lit_integer(1),
        new_expr_infix(Op::Mul, new_expr_lit_integer(2), new_expr_lit_integer(3)),
    );

    assert_exp(expect, actual)
}

#[test]
fn test_parse_precedence_of_expression2() {
    let input = "1 * 2 + 3";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = new_expr_infix(
        Op::Add,
        new_expr_infix(Op::Mul, new_expr_lit_integer(1), new_expr_lit_integer(2)),
        new_expr_lit_integer(3),
    );

    assert_exp(expect, actual)
}

#[test]
fn test_parse_precedence_of_expression3() {
    let input = "1+2 < 3+4";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = new_expr_infix(
        Op::Lt,
        new_expr_infix(Op::Add, new_expr_lit_integer(1), new_expr_lit_integer(2)),
        new_expr_infix(Op::Add, new_expr_lit_integer(3), new_expr_lit_integer(4)),
    );

    assert_exp(expect, actual)
}

#[test]
fn test_parse_precedence_of_expression4() {
    let input = "!(1+2 < 3+4) == false";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");
    let expect = new_expr_infix(
        Op::Eq,
        new_expr_prefix(
            Op::Not,
            new_expr_infix(
                Op::Lt,
                new_expr_infix(Op::Add, new_expr_lit_integer(1), new_expr_lit_integer(2)),
                new_expr_infix(Op::Add, new_expr_lit_integer(3), new_expr_lit_integer(4)),
            ),
        ),
        new_expr_lit_bool(false),
    );

    assert_exp(expect, actual)
}
