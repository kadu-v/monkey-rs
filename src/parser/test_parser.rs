use super::parser::LOWEST;
use crate::lexer::lexer::Lexer;
use crate::parser::parser::Parser;
use crate::{
    ast::{BlockStmt, Expr, ExprKind, Op, Program, Stmt, StmtKind},
    loc::Loc,
};

//-----------------------------------------------------------------------------
// Helper functions for unit tests of AST
//-----------------------------------------------------------------------------

fn assert_stmt(expect: Stmt, actual: Stmt) {
    match (expect.kind.clone(), actual.kind.clone()) {
        (StmtKind::Let(expr0, expr1), StmtKind::Let(expr2, expr3)) => {
            assert_expr(*expr0, *expr2);
            assert_expr(*expr1, *expr3);
        }
        (StmtKind::Return(expr0), StmtKind::Return(expr1)) => {
            assert_expr(*expr0, *expr1);
        }
        (StmtKind::ExprStmt(expr0), StmtKind::ExprStmt(expr1)) => {
            assert_expr(*expr0, *expr1);
        }
        (StmtKind::If(cond0, block0, block1), StmtKind::If(cond1, block2, block3)) => {
            assert_expr(*cond0, *cond1);
            assert_block_stmt(block0, block2);
            if block1.is_some() && block3.is_some() {
                assert_block_stmt(block1.unwrap(), block3.unwrap());
            } else if (block1.is_some() && !block3.is_some())
                || (!block1.is_some() && block3.is_some())
            {
                assert_eq!(block1, block3)
            }
        }
        _ => assert_eq!(expect.kind, actual.kind),
    }
}

fn assert_expr(expect: Expr, actual: Expr) {
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
        (ExprKind::LitFunc(exprs0, block0), ExprKind::LitFunc(exprs1, block1)) => {
            for (expr0, expr1) in exprs0.into_iter().zip(exprs1) {
                assert_expr(expr0, expr1);
            }
            assert_block_stmt(block0, block1);
        }
        // (ExprKind::LitArray(arry0), ExprKind::LitArray(arry1)) => {
        //     for (i0, i1) in arry0.into_iter().zip(arry1) {
        //         assert_expr(i0, i1);
        //     }
        // }
        (ExprKind::Infix(op0, expr0, expr1), ExprKind::Infix(op1, expr2, expr3)) => {
            assert_eq!(op0, op1);
            assert_expr(*expr0, *expr2);
            assert_expr(*expr1, *expr3);
        }
        (ExprKind::Prefix(op0, expr0), ExprKind::Prefix(op1, expr1)) => {
            assert_eq!(op0, op1);
            assert_expr(*expr0, *expr1);
        }

        // (ExprKind::If(expr0, block0, block1), ExprKind::If(expr3, block2, block3)) => {
        //     assert_expr(*expr0, *expr3);
        //     assert_block_stmt(block0, block1);
        //     assert_block_stmt(block2, block3);
        // }
        (ExprKind::Call(f0, args0), ExprKind::Call(f1, args1)) => {
            assert_expr(*f0, *f1);

            for (arg0, arg1) in args0.into_iter().zip(args1) {
                assert_expr(arg0, arg1);
            }
        }
        _ => assert_eq!(expect.kind, actual.kind),
    }
}

fn assert_block_stmt(expect: BlockStmt, actual: BlockStmt) {
    for (stmt0, stmt1) in expect.block.into_iter().zip(actual.block) {
        assert_stmt(stmt0, stmt1);
    }
}

fn new_dummy_loc() -> Loc {
    Loc::new(0, 0, 0, 0)
}

fn new_expr_lit_integer(n: isize) -> Expr {
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

fn new_expr_lit_func(func: Vec<Expr>, block: BlockStmt) -> Expr {
    let kind = ExprKind::LitFunc(func, block);
    let loc = new_dummy_loc();
    Expr::new(kind, loc)
}

// fn new_expr_lit_array(arry: Vec<Expr>) -> Expr {
//     let kind = ExprKind::LitArray(arry);
//     let loc = new_dummy_loc();
//     Expr::new(kind, loc)
// }

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

fn new_expr_ident(name: impl Into<String>) -> Expr {
    let kind = ExprKind::Ident(name.into());
    let loc = new_dummy_loc();
    Expr::new(kind, loc)
}

// fn new_expr_if(expr0: Expr, block0: BlockStmt, block1: BlockStmt) -> Expr {
//     let kind = ExprKind::If(expr0.into(), block0, block1);
//     let loc = new_dummy_loc();
//     Expr::new(kind, loc)
// }

fn new_expr_call(expr0: Expr, exprs: Vec<Expr>) -> Expr {
    let kind = ExprKind::Call(expr0.into(), exprs);
    let loc = new_dummy_loc();
    Expr::new(kind, loc)
}

// fn new_expr_index(expr0: Expr, expr1: Expr) -> Expr {
//     let kind = ExprKind::Index(expr0.into(), expr1.into());
//     let loc = new_dummy_loc();
//     Expr::new(kind, loc)
// }

fn new_stmt_let(ident: Expr, expr: Expr) -> Stmt {
    let kind = StmtKind::Let(ident.into(), expr.into());
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

fn new_stmt_if(cond: Expr, block0: BlockStmt, block1: Option<BlockStmt>) -> Stmt {
    let kind = StmtKind::If(cond.into(), block0, block1);
    let loc = new_dummy_loc();
    Stmt::new(kind, loc)
}

fn new_block_stmt(block: Vec<Stmt>) -> BlockStmt {
    let loc = new_dummy_loc();
    BlockStmt::new(block, loc)
}

fn new_program(stmts: Vec<Stmt>) -> Program {
    let loc = new_dummy_loc();

    Program::new(stmts, loc)
}

//-----------------------------------------------------------------------------
// Helper macro
//-----------------------------------------------------------------------------

macro_rules! int {
    ($i:literal) => {
        new_expr_lit_integer($i)
    };
}

macro_rules! bool {
    ($b:literal) => {
        new_expr_lit_bool($b)
    };
}

macro_rules! params {
    ($($x:expr),*) => {{
        let mut params = vec![];
        $(
            params.push($x);
        )*
        params
    }};
}
macro_rules! func {
    // function
    ($x:expr, $y:expr) => {
        new_expr_lit_func($x, $y)
    };
}

macro_rules! array {
    ($($x:expr);*) => {{
        let mut arr = vec![];
        $(
            arr.push($x);
        )*
        arr
    }};
}

macro_rules! expr {
    // prefix expressions
    (!, $x:expr) => {
        new_expr_prefix(Op::Not, $x)
    };
    (-, $x:expr) => {
        new_expr_prefix(Op::Sub, $x)
    };

    // infix expressions
    ($x:expr, +, $y:expr) => {
        new_expr_infix(Op::Add, $x, $y)
    };
    ($x:expr, - ,$y:expr) => {
        new_expr_infix(Op::Sub, $x, $y)
    };
    ($x:expr, *, $y:expr) => {
        new_expr_infix(Op::Mul, $x, $y)
    };
    ($x:expr, /, $y:expr) => {
        new_expr_infix(Op::Div, $x, $y)
    };
    ($x:expr, <, $y:expr) => {
        new_expr_infix(Op::Lt, $x, $y)
    };
    ($x:expr, >, $y:expr) => {
        new_expr_infix(Op::Gt, $x, $y)
    };
    ($x:expr, ==, $y:expr) => {
        new_expr_infix(Op::Eq, $x, $y)
    };
    ($x:expr, !=, $y:expr) => {
        new_expr_infix(Op::NotEq, $x, $y)
    };

    // identifier
    ($x:expr) => {
        new_expr_ident($x)
    };

    // if expression
    (if, $cond:expr, $x:expr, $y:expr) => {
        new_expr_if($cond, $x, $y)
    };

    // call expression
    ($x:literal, $($y:expr),*) => {
        {
            let f = new_expr_ident($x);
            let mut params = vec![];
            $(
                params.push($y);
            )*
            new_expr_call(f, params)
        }
    };
}

macro_rules! stmt {
    (let, $i:expr, =, $x:expr, ;) => {
        new_stmt_let(new_expr_ident($i), $x)
    };
    (return, $x:expr, ;) => {
        new_stmt_return($x)
    };
    (if, $cond:expr, $x:expr) => {
        new_stmt_if($cond, $x, None)
    };
    (if, $cond:expr, $x:expr, $y:expr) => {
        new_stmt_if($cond, $x, Some($y))
    };
    ($x:expr, ;) => {
        new_stmt_exprstmt($x)
    };
}

macro_rules! blockstmt {
    ($($x:expr);* ) => {{
        let mut block = vec![];
        $(
            block.push($x);
        )*
        new_block_stmt(block)}
    };
}

//-----------------------------------------------------------------------------
// Unit tests of Literals
//-----------------------------------------------------------------------------
#[test]
fn test_parse_lit_function_simple() {
    let input = "fn(x) { return x; }";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix expression");

    let expect = func!(
        params!(expr!("x")),
        blockstmt!(stmt!(return, expr!("x"), ;))
    );
    assert_expr(expect, actual)
}

#[test]
fn test_parse_lit_function_complex() {
    let input = "fn(x, y) { return x + y; }";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix expression");

    let expect = func!(
        params!(expr!("x"), expr!("y")),
        blockstmt!(stmt!(return, expr!(expr!("x"), +, expr!("y")), ;))
    );
    assert_expr(expect, actual)
}

//-----------------------------------------------------------------------------
// Unit tests of Infix Expressions
//-----------------------------------------------------------------------------

#[test]
fn test_parse_infix_expression_add() {
    let input = "1 + 2";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = expr!(int!(1), +, int!(2));

    assert_expr(expect, actual)
}

#[test]
fn test_parse_infix_expression_sub() {
    let input = "1 - 10";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = expr!(int!(1), -, int!(10));

    assert_expr(expect, actual)
}

#[test]
fn test_parse_infix_expression_mul() {
    let input = "10 * 10";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = expr!(int!(10), *, int!(10));

    assert_expr(expect, actual)
}

#[test]
fn test_parse_infix_expression_div() {
    let input = "1 / 10";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = expr!(int!(1), /, int!(10));

    assert_expr(expect, actual)
}

#[test]
fn test_parse_infix_expression_eq() {
    let input = "true == false";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = expr!(bool!(true), ==, bool!(false));

    assert_expr(expect, actual)
}

#[test]
fn test_parse_infix_expression_eq_integer() {
    let input = "1 + 1 == 1";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = expr!(expr!(int!(1), +, int!(1)), ==, int!(1));

    assert_expr(expect, actual)
}

#[test]
fn test_parse_infix_expression_noteq() {
    let input = "true != false";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = expr!(bool!(true), !=, bool!(false));

    assert_expr(expect, actual)
}

#[test]
fn test_parse_infix_expression_paren() {
    let input = "(1 + 2)";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = expr!(int!(1), +, int!(2));

    assert_expr(expect, actual)
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

    let expect = expr!(-, int!(1));
    assert_expr(expect, actual)
}

#[test]
fn test_parse_prefix_expression_not_true() {
    let input = "!true";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_prefix_expression()
        .expect("can not parse a prefix_expression");

    let expect = expr!(!, bool!(true));

    assert_expr(expect, actual)
}

//-----------------------------------------------------------------------------
// Unit tests of Identifier Expression
//-----------------------------------------------------------------------------
#[test]
fn test_parse_identifier_expression1() {
    let input = "x";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a identifier_expression");

    let expect = expr!("x");

    assert_expr(expect, actual)
}

#[test]
fn test_parse_identifier_expression2() {
    let input = "b";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a identifier_expression");

    let expect = expr!("b");

    assert_expr(expect, actual)
}

//-----------------------------------------------------------------------------
// Unit tests of Call Expression
//-----------------------------------------------------------------------------
#[test]
fn test_parse_call_expression() {
    let input = "f(1, 2)";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a call_expression");

    let expect = expr!("f", int!(1), int!(2));

    assert_expr(expect, actual)
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

    let expect = expr!(int!(1), +, expr!(int!(2), *, int!(3)));

    assert_expr(expect, actual)
}

#[test]
fn test_parse_precedence_of_expression2() {
    let input = "1 * 2 + 3";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = expr!(expr!(int!(1), * , int!(2)), +, int!(3));

    assert_expr(expect, actual)
}

#[test]
fn test_parse_precedence_of_expression3() {
    let input = "1+2 < 3+4";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");

    let expect = expr!(expr!(int!(1), +, int!(2)), <, expr!(int!(3), +, int!(4)));

    assert_expr(expect, actual)
}

#[test]
fn test_parse_precedence_of_expression4() {
    let input = "!(1+2 < 3+4) == false";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_expression(LOWEST)
        .expect("can not parse a prefix_expression");
    let expect = expr!(expr!(!, expr!(
                                expr!(int!(1), +, int!(2)), 
                                <, 
                                expr!(int!(3), +, int!(4)))), 
                 ==, 
                 bool!(false));

    assert_expr(expect, actual)
}

//-----------------------------------------------------------------------------
// Unit tests of Statements
//-----------------------------------------------------------------------------

#[test]
fn test_parse_let_statement() {
    let input = "let x = 1;";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p.parse_statement().expect("can not parse let statement");

    let expect = stmt!(let, "x", =,  int!(1), ;);
    assert_stmt(expect, actual)
}

#[test]
fn test_parse_return_statement() {
    let input = "return 1 + 1;";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p.parse_statement().expect("can not parse return statement");

    let expect = stmt!(return, expr!(int!(1), +, int!(1)), ;);
    assert_stmt(expect, actual)
}

#[test]
fn test_parse_expression_statement() {
    let input = "1 + 2;\n";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p.parse_statement().expect("can not parse e statement");

    let expect = stmt!(expr!(int!(1), + , int!(2)), ;);
    assert_stmt(expect, actual)
}

#[test]
fn test_parse_if_statement() {
    let input = "if true { 1; } else { 2; } ";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_statement()
        .expect("can not parse a prefix_expression");

    let expect = stmt!(
        if,
        bool!(true),
        blockstmt!(stmt!(int!(1), ;)),
        blockstmt!(stmt!(int!(2), ;))
    );

    assert_stmt(expect, actual)
}

//-----------------------------------------------------------------------------
// Unit tests of Block Statements
//-----------------------------------------------------------------------------

#[test]
fn test_parse_block_statement() {
    let input = "{ 1+2; let x = 1; return x; }";
    let mut l = Lexer::new(input);
    let mut p = Parser::new(&mut l);
    let actual = p
        .parse_block_statement()
        .expect("can not parse e statement");

    let expect = blockstmt!(
                    stmt!(expr!(int!(1), +, int!(2)), ;);
                    stmt!(let, "x", =,  int!(1), ;);
                    stmt!(return, expr!("x"), ;)
    );
    assert_block_stmt(expect, actual)
}
