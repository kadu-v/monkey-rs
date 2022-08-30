//! Error structs of monkey
use std::fmt::Debug;

use crate::{ast::Node, loc::Loc, token::TokenKind};

//-----------------------------------------------------------------------------
// Trait for Error
//-----------------------------------------------------------------------------\
pub trait Error: Debug {}

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

impl Error for ParseError {}

impl From<ParseError> for Box<dyn Error> {
    fn from(item: ParseError) -> Self {
        Box::new(item)
    }
}

//-----------------------------------------------------------------------------
// Error struct for Evaluation
//-----------------------------------------------------------------------------\
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct EvalError<T>
where
    T: Node + Debug + 'static,
{
    pub loc: Loc,
    pub prg: T,
    pub error_msg: String,
}

impl<T> EvalError<T>
where
    T: Node + Debug + 'static,
{
    pub fn new(loc: Loc, prg: T, error_msg: String) -> Self {
        Self {
            loc,
            prg,
            error_msg,
        }
    }

    pub fn report_error_message(loc: Loc, prg: T, error_msg: impl Into<String>) -> Result<T> {
        let error_msg = format!(
            "woops!! cannot evaluate this object: {:?}, {}",
            prg,
            error_msg.into()
        );
        Err(EvalError::new(loc, prg, error_msg).into())
    }
}

impl<T> Error for EvalError<T> where T: Node + Debug {}

impl<T> From<EvalError<T>> for Box<dyn Error>
where
    T: Node + Debug + 'static,
{
    fn from(item: EvalError<T>) -> Self {
        Box::new(item)
    }
}
