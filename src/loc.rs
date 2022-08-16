
//! Loc struct of monkey compiler

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Loc {
    pub line: usize,
    pub left: usize,
    pub width: usize,
}

impl Loc {
    pub fn new(line: usize, left: usize, width: usize) -> Self {
        Loc { line, left, width }
    }
}