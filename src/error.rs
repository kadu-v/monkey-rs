//! Error structs of monkey
use std::fmt::Debug;

use crate::{loc::Loc, token::TokenKind};

//-----------------------------------------------------------------------------
// Trait for Error
//-----------------------------------------------------------------------------\
pub trait Error: Debug {
    fn do_error_report(&self, code: &str);
}

pub type Result<T> = std::result::Result<T, Box<dyn Error>>;

//-----------------------------------------------------------------------------
// Error struct for Parser
//-----------------------------------------------------------------------------
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct ParseError {
    pub loc: Loc,
    pub actual_token: TokenKind,
    pub expect_token: Option<TokenKind>,
    pub error_msg: String,
}

impl ParseError {
    pub fn new(
        loc: Loc,
        actual_token: TokenKind,
        expect_token: Option<TokenKind>,
        error_msg: String,
    ) -> Self {
        Self {
            loc,
            actual_token,
            expect_token,
            error_msg,
        }
    }

    pub fn not_match_token<T>(
        loc: Loc,
        actual_kind: TokenKind,
        expect_kind: TokenKind,
    ) -> Result<T> {
        let error_msg = format!(
            "got token: {:?}, expected token: {:?}",
            actual_kind, expect_kind,
        );

        Err(ParseError::new(loc, actual_kind, Some(expect_kind), error_msg).into())
    }

    pub fn report_error_message<T>(
        loc: Loc,
        actual_kind: TokenKind,
        error_msg: impl Into<String>,
    ) -> Result<T> {
        let error_msg = format!("got token: {:?}, {}", actual_kind, error_msg.into());
        Err(ParseError::new(loc, actual_kind, None, error_msg).into())
    }
}

impl Error for ParseError {
    fn do_error_report(&self, code: &str) {
        println!("Parse Error: ");
        println!("{:?}", code);
    }
}

impl From<ParseError> for Box<dyn Error> {
    fn from(item: ParseError) -> Self {
        Box::new(item)
    }
}

//-----------------------------------------------------------------------------
// Error struct for Evaluation
//-----------------------------------------------------------------------------\
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct EvalError {
    pub loc: Loc,
    pub error_msg: String,
}

impl EvalError {
    pub fn new(loc: Loc, error_msg: impl Into<String>) -> Self {
        Self {
            loc,
            error_msg: error_msg.into(),
        }
    }

    pub fn report_error_message<T>(loc: Loc, error_msg: impl Into<String>) -> Result<T> {
        let error_msg = format!("woops!! cannot evaluate this object: {}", error_msg.into());
        Err(EvalError::new(loc, error_msg).into())
    }
}

impl Error for EvalError {
    fn do_error_report(&self, code: &str) {
        println!("Eval Error: ");
        println!("{:?}", code);
    }
}

impl From<EvalError> for Box<dyn Error> {
    fn from(item: EvalError) -> Self {
        Box::new(item)
    }
}
