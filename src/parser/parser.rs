use std::{collections::HashMap, hash::Hash, vec};

use crate::{
    ast::{
        BlockStmt, Expr,
        ExprKind::{self, *},
        Op, Program, Stmt,
        StmtKind::{self, *},
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
        (TokenKind::RBRACKET, INDEX),
    ]
    .iter()
    .cloned()
    .collect::<HashMap<TokenKind, isize>>()
});

//-----------------------------------------------------------------------------
// Parser
//-----------------------------------------------------------------------------

#[derive(Debug, PartialEq)]
pub struct Parser<'input> {
    lex: &'input mut Lexer<'input>,
    cur_token: Token,
    peek_token: Token,
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

    fn expect_cur_token_and_consume(&mut self, kind: TokenKind) -> Result<Option<String>> {
        if self.cur_token_kind_is(kind) {
            let cur_token_val = self.cur_token.val.clone();
            self.next_token();
            Ok(cur_token_val)
        } else {
            let loc = self.peek_token.loc;
            ParseError::not_match_token(self.cur_token.loc, self.cur_token.kind, kind)
        }
    }

    // fn expect_peek_token_and_consume(&mut self, kind: TokenKind) -> Result<Option<String>> {
    //     if self.peek_token_kind_is(kind) {
    //         self.next_token();
    //         Ok(self.cur_token.val.clone()) // a cur_token has already consumed
    //     } else {
    //         let loc = self.peek_token.loc;
    //         Err(ParseError::new(loc).into())
    //     }
    // }

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

    //-----------------------------------------------------------------------------
    // Parser for a program
    //-----------------------------------------------------------------------------

    fn parse_program(&mut self) -> Result<Program> {
        let mut stmts = Vec::new();
        while self.cur_token_kind_is(TokenKind::EOF) {
            let stmt = self.parse_statement()?;
            stmts.push(stmt);
            self.next_token();
        }

        Ok(Program::new(stmts))
    }

    //-----------------------------------------------------------------------------
    // Parser for a statement
    //-----------------------------------------------------------------------------

    pub fn parse_statement(&mut self) -> Result<Stmt> {
        match self.cur_token.kind {
            TokenKind::LET => self.parse_let_statement(),
            TokenKind::RETURN => self.parse_return_statement(),
            TokenKind::IF => self.parse_if_statement(),
            _ => self.parse_expression_statement(),
        }
    }

    pub fn parse_let_statement(&mut self) -> Result<Stmt> {
        let loc0 = self.cur_token.loc;

        self.expect_cur_token_and_consume(TokenKind::LET)?;

        let ident = self.parse_identifier_expression()?;

        // check that next token is assign
        self.expect_cur_token_and_consume(TokenKind::ASSIGN)?;

        // parse an expression
        let expr = self.parse_expression(LOWEST)?;

        // check that an end of let-expression is semicolon
        self.expect_cur_token_and_consume(TokenKind::SEMICOLON)?;

        // calculate a location of let-statement
        let loc = loc0 + self.cur_token.loc;

        Ok(Stmt::new(Let(ident.into(), expr.into()), loc))
    }

    pub fn parse_return_statement(&mut self) -> Result<Stmt> {
        let loc0 = self.cur_token.loc;

        self.expect_cur_token_and_consume(TokenKind::RETURN)?;

        let expr = self.parse_expression(LOWEST)?;

        // check that an end of let-expression is semicolon
        self.expect_cur_token_and_consume(TokenKind::SEMICOLON)?;

        // calculate a location of let-statement
        let loc = loc0 + self.cur_token.loc;

        Ok(Stmt::new(StmtKind::Return(expr.into()), loc))
    }

    pub fn parse_expression_statement(&mut self) -> Result<Stmt> {
        let loc0 = self.cur_token.loc;

        let expr = self.parse_expression(LOWEST)?;

        // check that an end of let-expression is semicolon
        self.expect_cur_token_and_consume(TokenKind::SEMICOLON)?;

        // calculate a location of let-statement
        let loc = loc0 + self.cur_token.loc;

        Ok(Stmt::new(StmtKind::ExprStmt(expr.into()), loc))
    }

    pub fn parse_if_statement(&mut self) -> Result<Stmt> {
        let loc0 = self.cur_token.loc;

        self.expect_cur_token_and_consume(TokenKind::IF)?; // "if"

        let cond = self.parse_expression(LOWEST)?; // condition

        let then_block = self.parse_block_statement()?; // block

        let else_block = if self.cur_token_kind_is(TokenKind::ELSE) {
            self.next_token();

            let else_block = self.parse_block_statement()?; // expr

            Some(else_block)
        } else {
            None
        };

        let loc = loc0 + self.cur_token.loc;

        Ok(Stmt::new(
            StmtKind::If(cond.into(), then_block, else_block),
            loc,
        ))
    }

    //-----------------------------------------------------------------------------
    // Parser for a block statement
    //-----------------------------------------------------------------------------

    pub fn parse_block_statement(&mut self) -> Result<BlockStmt> {
        let mut block = vec![];
        let mut loc = self.cur_token.loc;

        self.expect_cur_token_and_consume(TokenKind::LBRACE)?;

        while !self.cur_token_kind_is(TokenKind::RBRACE) && !self.cur_token_kind_is(TokenKind::EOF)
        {
            let stmt = self.parse_statement()?;
            loc = loc + stmt.loc;
            block.push(stmt);
        }

        self.expect_cur_token_and_consume(TokenKind::RBRACE)?;

        Ok(BlockStmt::new(block, loc))
    }
    //-----------------------------------------------------------------------------
    // Parser for an expression
    //-----------------------------------------------------------------------------

    pub fn parse_expression(&mut self, precedence: isize) -> Result<Expr> {
        // parse a left expression
        let mut expr = match self.cur_token.kind {
            TokenKind::INT => self.parse_lit_integer()?,
            TokenKind::STRING => unimplemented!(
                "STRING case of parse_expression has not implemented yet. A current token is {:?}",
                self.cur_token.kind
            ),
            TokenKind::TRUE | TokenKind::FALSE => self.parse_lit_boolean()?,
            TokenKind::IDENT => self.parse_identifier_expression()?,
            TokenKind::MINUS | TokenKind::BANG => self.parse_prefix_expression()?,
            TokenKind::LPAREN => self.parse_grouped_expression()?,
            // TokenKind::IF => self.parse_if_expression()?,
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
                _ => unimplemented!(
                    "parse_expression has not implemented yet, cur_token: {:?}",
                    self.cur_token
                ),
            };
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
        let right_expr = self.parse_expression(PREFIX)?;

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
                ParseError::report_error_message(
                    self.cur_token.loc,
                    self.cur_token.kind,
                    "expected token is operator (+, -, *, /,...)",
                )
            }
        };

        // consume a token of operator
        self.next_token();

        op
    }

    pub fn parse_identifier_expression(&mut self) -> Result<Expr> {
        // parse an identifier
        if let Some(ident) = self.expect_cur_token_and_consume(TokenKind::IDENT)? {
            Ok(Expr::new(ExprKind::Ident(ident), self.cur_token.loc))
        } else {
            ParseError::not_match_token(self.cur_token.loc, self.cur_token.kind, TokenKind::INT)
        }
    }

    pub fn parse_grouped_expression(&mut self) -> Result<Expr> {
        self.expect_cur_token_and_consume(TokenKind::LPAREN)?;

        let expr = self.parse_expression(LOWEST)?;

        self.expect_cur_token_and_consume(TokenKind::RPAREN)?;

        Ok(expr)
    }

    //-----------------------------------------------------------------------------
    // Parser for a literal
    //-----------------------------------------------------------------------------

    // Assume that a kind of first token is TRUE or FALSE
    pub fn parse_lit_boolean(&mut self) -> Result<Expr> {
        let loc = self.cur_token.loc;
        let kind = self.cur_token.kind;
        self.next_token(); // consume a cur_token

        match kind {
            TokenKind::TRUE => Ok(Expr::new(LitBool(true), loc)),
            TokenKind::FALSE => Ok(Expr::new(LitBool(false), loc)),
            _ => ParseError::report_error_message(
                self.cur_token.loc,
                self.cur_token.kind,
                "expected token is boolean literal (true or false)",
            ),
        }
    }

    // Assume that a kind of first token is INT
    pub fn parse_lit_integer(&mut self) -> Result<Expr> {
        let loc = self.cur_token.loc;
        if let Some(s) = self.cur_token.val.clone() {
            self.next_token();
            match s.parse::<usize>() {
                Ok(n) => Ok(Expr::new(LitInt(n), loc)),
                Err(_) => ParseError::report_error_message(
                    self.cur_token.loc,
                    self.cur_token.kind,
                    "cannot parse a integer literal by Rust's parse function",
                ),
            }
        } else {
            ParseError::not_match_token(self.cur_token.loc, self.cur_token.kind, TokenKind::INT)
        }
    }

    // Assume that a kind of first token is STRING
    pub fn parse_lit_string(&mut self) -> Result<Expr> {
        let loc = self.cur_token.loc;
        unimplemented!("parse_lit_string")
    }
    // Assume that a kind of first token is FUNCTION
    pub fn parse_lit_function(&mut self) -> Result<Expr> {
        let loc = self.cur_token.loc;

        self.expect_cur_token_and_consume(TokenKind::FUNCITON)?;

        self.expect_cur_token_and_consume(TokenKind::LPAREN)?;
        let params = self.parse_parameters()?;
        self.expect_cur_token_and_consume(TokenKind::RPAREN)?;
    }

    pub fn parse_parameters(&mut self) -> Result<Vec<Expr>> {
        unimplemented!()
    }
}