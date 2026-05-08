#![allow(dead_code)]

use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd, Default)]
pub struct SourceLocation {
    pub file: String,
    pub line: u32,
    pub column: u32,
}

impl SourceLocation {
    pub fn new(file: impl Into<String>, line: u32, column: u32) -> Self {
        Self {
            file: file.into(),
            line,
            column,
        }
    }
}

impl fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.file.is_empty() {
            write!(f, "<unknown>:{}:{}", self.line, self.column)
        } else {
            write!(f, "{}:{}:{}", self.file, self.line, self.column)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_with_file() {
        let loc = SourceLocation::new("main.c", 12, 4);
        assert_eq!(loc.to_string(), "main.c:12:4");
    }

    #[test]
    fn display_without_file() {
        let loc = SourceLocation::new("", 0, 0);
        assert_eq!(loc.to_string(), "<unknown>:0:0");
    }
}
