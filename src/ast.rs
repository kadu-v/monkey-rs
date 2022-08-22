//! AST of monkey

use crate::loc::Loc;

//-----------------------------------------------------------------------------
// AST of Expressions
//-----------------------------------------------------------------------------

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Expr {
    pub kind: ExprKind,
    pub loc: Loc,
}

impl Expr {
    pub fn new(kind: ExprKind, loc: Loc) -> Self {
        Self { kind, loc }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum ExprKind {
    // Literal
    LitInt(usize),                 // "1"
    LitString(String),             // "hoge"
    LitBool(bool),                 // "true"
    LitFunc(Vec<Expr>, BlockStmt), // "fn(x, y)  blockstmt "
    LitArray(Vec<Expr>),           // "[1, 2, 3]"
    // LitHash(HashMap<Expr, Expr>),   // hash.get(x)

    // Expression
    Infix(Op, Box<Expr>, Box<Expr>), // "1 + 2"
    Prefix(Op, Box<Expr>),           // "-1"
    Ident(String),                   // "x"
    // If(Box<Expr>, BlockStmt, BlockStmt), // "if true 1 else 2"
    Call(Box<Expr>, Vec<Expr>),  // "f(1, 2)"
    Index(Box<Expr>, Box<Expr>), // "a[i]"
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum Op {
    Add,   // "+"
    Sub,   // "-"
    Mul,   // "*"
    Div,   // "/"
    Eq,    // "=="
    NotEq, // "!="
    Lt,    // "<"
    Gt,    // ">"
    Not,   // "!"
}

//-----------------------------------------------------------------------------
// AST of Statements
//-----------------------------------------------------------------------------

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct BlockStmt {
    pub block: Vec<Stmt>, // "stmt1 stmt2"
    pub loc: Loc,
}

impl BlockStmt {
    pub fn new(block: Vec<Stmt>, loc: Loc) -> Self {
        Self { block, loc }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Stmt {
    pub kind: StmtKind,
    pub loc: Loc,
}

impl Stmt {
    pub fn new(kind: StmtKind, loc: Loc) -> Self {
        Self { kind, loc }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum StmtKind {
    Let(Box<Expr>, Box<Expr>),                   // "let x = 1"
    Return(Box<Expr>),                           // "return x"
    ExprStmt(Box<Expr>),                         // "e;"
    If(Box<Expr>, BlockStmt, Option<BlockStmt>), // "if true 1 else 2"
}

//-----------------------------------------------------------------------------
// AST of Program
//-----------------------------------------------------------------------------

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Program {
    pub stmts: Vec<Stmt>,
}

impl Program {
    pub fn new(stmts: Vec<Stmt>) -> Self {
        Self { stmts }
    }
}
