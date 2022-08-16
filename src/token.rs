//! Token struct of monkey compiler

use crate::loc::*;

use once_cell::sync::Lazy;
use std::collections::HashMap;

static KEYWORDS: Lazy<HashMap<&str, TokenKind>> = Lazy::new(|| {
    [
        ("fn", TokenKind::FUNCITON),
        ("let", TokenKind::LET),
        ("true", TokenKind::TRUE),
        ("false", TokenKind::FALSE),
        ("if", TokenKind::IF),
        ("else", TokenKind::ELSE),
        ("return", TokenKind::RETURN),
    ]
    .iter()
    .cloned()
    .collect::<HashMap<&str, TokenKind>>()
});

// ident が予約後の場合は対応する TokenKind を返す
pub fn lookup_keyword(ident: &str) -> Option<TokenKind> {
    if let Some(kind) = KEYWORDS.get(ident) {
        return Some(kind.clone());
    }
    None
}

// TokenKind for Hack VM
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    EOF,
    NEWLINE,
    ILLEGAL,

    // 数字とシンボル
    INT(usize),
    STRING(String),

    // 演算子
    ASSIGN,   // "="
    PLUS,     // "+"
    MINUS,    // "-"
    BANG,     // "!"
    ASTERISK, // "*"
    SLASH,    // "/"

    LT,     // "<"
    GT,     // ">"
    EQ,     // "="
    NOT_EQ, // "!="

    // デリミタ
    COMMA,     // ","
    SEMICOLON, // ";"
    COLON,     // ":"

    LPAREN,   // "("
    RPAREN,   // ")"
    LBRACE,   // "{"
    RBRACE,   // "}"
    LBRACKET, // "["
    RBRACKET, // "]"

    // キーワード
    FUNCITON, // "fn"
    LET,      // "let"
    TRUE,     // "true"
    FALSE,    // "false"
    IF,       // "if"
    ELSE,     // "else"
    RETURN,   // "return"
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub loc: Loc,
}

impl Token {
    pub fn new(kind: TokenKind, loc: Loc) -> Self {
        Token { kind, loc }
    }
}
