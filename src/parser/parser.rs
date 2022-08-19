use std::{collections::HashMap, hash::Hash};

use crate::{
    ast::{
        Expr,
        ExprKind::{self, *},
        Ident, Op, Program, Stmt,
        StmtKind::*,
    },
    error::{ParseError, Result},
    lexer::lexer::Lexer,
    token::{Token, TokenKind},
};
use once_cell::sync::Lazy;

//-----------------------------------------------------------------------------
// PRECENDES
//-----------------------------------------------------------------------------
pub(super) const LOWEST: isize = 0;
pub(super) const EQUALS: isize = 1;
pub(super) const LESSGREATER: isize = 2;
pub(super) const SUM: isize = 3;
pub(super) const PRODUCT: isize = 4;
pub(super) const PREFIX: isize = 5;
pub(super) const CALL: isize = 6;
pub(super) const INDEX: isize = 7;

static PRECEDENCES: Lazy<HashMap<TokenKind, isize>> = Lazy::new(|| {
    [
        (TokenKind::EQ, EQUALS),
        (TokenKind::NOT_EQ, EQUALS),
        (TokenKind::LT, LESSGREATER),
        (TokenKind::GT, LESSGREATER),
        (TokenKind::PLUS, SUM),
        (TokenKind::MINUS, SUM),
        (TokenKind::SLASH, PRODUCT),
        (TokenKind::ASTERISK, PRODUCT),
        (TokenKind::LPAREN, CALL),
        (TokenKind::RPAREN, INDEX),
    ]
    .iter()
    .cloned()
    .collect::<HashMap<TokenKind, isize>>()
});

//-----------------------------------------------------------------------------
// Parser
//-----------------------------------------------------------------------------
// type PrefixParseFn = fn() -> Result<Expr>;
// type InfixParseFn = fn(Expr) -> Result<Expr>;

#[derive(Debug, PartialEq)]
pub struct Parser<'input> {
    lex: &'input mut Lexer<'input>,
    cur_token: Token,
    peek_token: Token,
    // prefix_parse_fns: HashMap<TokenKind, PrefixParseFn>,
    // infix_parse_fns: HashMap<TokenKind, InfixParseFn>,
}

impl<'input> Parser<'input> {
    pub fn new(lex: &'input mut Lexer<'input>) -> Self {
        let cur_token = lex.next_token();
        let peek_token = lex.next_token();

        Self {
            lex,
            cur_token,
            peek_token,
        }
    }

    // fn regisiter_prefix_fn(&mut self, kind: TokenKind, f: fn() -> Expr) {
    //     self.prefix_parse_fns.insert(kind, f);
    // }

    // fn regisiter_infix_fn(&mut self, kind: TokenKind, f: fn(Expr) -> Expr) {
    //     self.infix_parse_fns.insert(kind, f);
    // }

    fn next_token(&mut self) {
        self.cur_token = self.peek_token.clone();
        self.peek_token = self.lex.next_token();
    }

    fn cur_token_kind_is(&self, kind: TokenKind) -> bool {
        self.cur_token.kind == kind
    }

    fn peek_token_kind_is(&self, kind: TokenKind) -> bool {
        self.peek_token.kind == kind
    }

    fn expect_peek(&mut self, kind: TokenKind) -> Result<Option<String>> {
        if self.peek_token_kind_is(kind) {
            self.next_token();
            Ok(self.cur_token.val.clone())
        } else {
            let loc = self.peek_token.loc;
            Err(ParseError::new(loc).into())
        }
    }

    fn peek_precedence(&self) -> isize {
        if let Some(&p) = PRECEDENCES.get(&self.cur_token.kind) {
            p
        } else {
            LOWEST
        }
    }

    fn cur_precedence(&self) -> isize {
        if let Some(&p) = PRECEDENCES.get(&self.cur_token.kind) {
            p
        } else {
            LOWEST
        }
    }

    pub fn prefix_parse_fns(&mut self, kind: TokenKind) -> Result<Expr> {
        match kind {
            TokenKind::MINUS => self.parse_prefix_expression(),
            _ => unimplemented!("prefix_parse_fns has not implemented yet"),
        }
    }

    fn parse_program(&mut self) -> Result<Program> {
        let mut stmts = Vec::new();
        while self.cur_token_kind_is(TokenKind::EOF) {
            let stmt = self.parse_statement()?;
            stmts.push(stmt);
            self.next_token();
        }

        Ok(Program::new(stmts))
    }

    fn parse_statement(&mut self) -> Result<Stmt> {
        match self.cur_token.kind {
            TokenKind::LET => self.parse_let_statement(),
            _ => Err(ParseError::new(self.cur_token.loc).into()),
        }
    }

    pub fn parse_let_statement(&mut self) -> Result<Stmt> {
        let loc0 = self.cur_token.loc;

        // parse an identifier
        let ident = (self.expect_peek(TokenKind::IDENT)?).unwrap();
        let ident = Ident::new(ident, self.cur_token.loc);

        // check that next token is assign
        self.expect_peek(TokenKind::ASSIGN)?;
        self.next_token();

        // parse an expression
        let val = Box::new(Expr::new(LitInt(0), self.cur_token.loc));

        // check that an end of let-expression is semicolon
        self.expect_peek(TokenKind::SEMICOLON)?;

        // calculate a location of let-statement
        let loc = loc0 + self.cur_token.loc;

        Ok(Stmt::new(Let(ident, val), loc))
    }

    pub fn parse_expression(&mut self, precedence: isize) -> Result<Expr> {
        let loc0 = self.cur_token.loc;

        // parse a left expression
        let mut expr = match self.cur_token.kind {
            TokenKind::INT => self.parse_lit_integer()?,
            TokenKind::STRING => unimplemented!(
                "STRING case of parse_expression has not implemented yet. A current token is {:?}",
                self.cur_token.kind
            ),
            TokenKind::TRUE | TokenKind::FALSE => self.parse_lit_boolean()?,
            TokenKind::IDENT => unimplemented!(
                "IDENT case of parse_expression has not implemented yet. A current token is {:?}",
                self.cur_token.kind
            ),
            TokenKind::MINUS | TokenKind::BANG => self.parse_prefix_expression()?,
            TokenKind::LPAREN => unimplemented!(
                "LPAREN case of parse_expression has not implemented yet. A current token is {:?}",
                self.cur_token.kind
            ),
            TokenKind::IF => unimplemented!(
                "IF case of parse_expression has not implemented yet. A current token is {:?}",
                self.cur_token.kind
            ),
            TokenKind::FUNCITON => unimplemented!(
                "FUNCTION case of parse_expression has not implemented yet. A current token is {:?}",
                self.cur_token.kind
            ),
            TokenKind::LBRACKET => unimplemented!(
                "LBRACKET case of parse_expression has not implemented yet. A current token is {:?}",
                self.cur_token.kind
            ),
            TokenKind::LBRACE => unimplemented!(
                "LBRACE case of parse_expression has not implemented yet. A current token is {:?}",
                self.cur_token.kind
            ),
            _ => unimplemented!(
                "parse_expression has not implemented yet. A current token is {:?}",
                self.cur_token.kind
            ),
        };

        // parse a right expression
        while !self.peek_token_kind_is(TokenKind::SEMICOLON) && precedence < self.peek_precedence()
        {
            expr = match self.cur_token.kind {
                TokenKind::PLUS
                | TokenKind::MINUS
                | TokenKind::SLASH
                | TokenKind::ASTERISK
                | TokenKind::GT
                | TokenKind::LT
                | TokenKind::EQ
                | TokenKind::NOT_EQ => self.parse_infix_epxression(expr)?,
                _ => unimplemented!("parse_expression has not implemented yet"),
            };

            // self.next_token();
        }

        Ok(expr)
    }

    // Assume that a first token of expression is "-" or "!"
    pub fn parse_prefix_expression(&mut self) -> Result<Expr> {
        // parse a prefix operetor
        // "+", "-", "*", "/" or "!"
        let loc0 = self.cur_token.loc;
        let op = self.parse_operator()?;

        // parse a right expression
        let right_expr = self.parse_expression(LOWEST)?;

        // calculate a whole location of the prefix expression
        let loc = loc0 + self.cur_token.loc;

        Ok(Expr::new(ExprKind::Prefix(op, right_expr.into()), loc))
    }

    // Assume that a first token of expression is "+", "-", "*", "/", etc..
    pub fn parse_infix_epxression(&mut self, left_expr: Expr) -> Result<Expr> {
        let loc0 = self.cur_token.loc;

        // parse a infix opereator
        let precedence = self.cur_precedence(); // get a precedence of current operator
        let op = self.parse_operator()?;

        // parse a right expression
        let right_expr = self.parse_expression(precedence)?;

        // calculate a whole location of the prefix expression
        let loc = loc0 + self.cur_token.loc;

        Ok(Expr::new(
            ExprKind::Infix(op, left_expr.into(), right_expr.into()),
            loc,
        ))
    }

    pub fn parse_operator(&mut self) -> Result<Op> {
        let op = match self.cur_token.kind {
            TokenKind::PLUS => Ok(Op::Add),
            TokenKind::MINUS => Ok(Op::Sub),
            TokenKind::ASTERISK => Ok(Op::Mul),
            TokenKind::SLASH => Ok(Op::Div),
            TokenKind::EQ => Ok(Op::Eq),
            TokenKind::NOT_EQ => Ok(Op::NotEq),
            TokenKind::LT => Ok(Op::Lt),
            TokenKind::GT => Ok(Op::Gt),
            TokenKind::BANG => Ok(Op::Not),
            _ => {
                let loc = self.cur_token.loc;
                Err(ParseError::new(loc).into())
            }
        };

        // consume a token of operator
        self.next_token();

        op
    }

    pub fn parse_lit_boolean(&mut self) -> Result<Expr> {
        let loc = self.cur_token.loc;
        if let Some(s) = self.cur_token.val.clone() {
            self.next_token();
            match s.parse::<bool>() {
                Ok(b) => Ok(Expr::new(LitBool(b), loc)),
                Err(_) => Err(ParseError::new(loc).into()),
            }
        } else {
            Err(ParseError::new(loc).into())
        }
    }

    // Assume that a kind of first token is INT
    pub fn parse_lit_integer(&mut self) -> Result<Expr> {
        let loc = self.cur_token.loc;
        if let Some(s) = self.cur_token.val.clone() {
            self.next_token();
            match s.parse::<usize>() {
                Ok(n) => Ok(Expr::new(LitInt(n), loc)),
                Err(_) => Err(ParseError::new(loc).into()),
            }
        } else {
            Err(ParseError::new(loc).into())
        }
    }
}
