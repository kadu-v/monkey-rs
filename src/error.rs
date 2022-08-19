//! Error structs of monkey
use std::fmt::Debug;

use crate::loc::Loc;

pub trait Error: Debug {}

pub type Result<T> = std::result::Result<T, Box<dyn Error>>;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct ParseError {
    pub loc: Loc,
}

impl ParseError {
    pub fn new(loc: Loc) -> Self {
        Self { loc }
    }
}

impl Error for ParseError {}

impl From<ParseError> for Box<dyn Error> {
    fn from(item: ParseError) -> Self {
        Box::new(item)
    }
}
