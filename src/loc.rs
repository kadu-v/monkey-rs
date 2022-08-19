//! Loc struct of monkey compiler
use std::cmp::{max, min};
use std::ops::Add;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Loc {
    pub line_top: usize,
    pub line_bottom: usize,
    pub left: usize,
    pub right: usize,
}

impl Loc {
    pub fn new(line_top: usize, line_bottom: usize, left: usize, right: usize) -> Self {
        Self {
            line_top,
            line_bottom,
            left,
            right,
        }
    }
}

impl Add for Loc {
    type Output = Loc;
    fn add(self, rhs: Self) -> Self::Output {
        let line_top = max(self.line_top, rhs.line_top);
        let line_bottom = min(self.line_bottom, rhs.line_bottom);
        let left = min(self.left, rhs.left);
        let right = max(self.right, rhs.right);

        Self::Output {
            line_top,
            line_bottom,
            left,
            right,
        }
    }
}
