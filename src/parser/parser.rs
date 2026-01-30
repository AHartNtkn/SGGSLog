//! Parser for SGGSLog syntax.

use super::ast::Statement;
use crate::syntax::Literal;

/// Parse error with location information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub line: usize,
    pub column: usize,
    pub span: Option<(usize, usize)>,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.column, self.message)
    }
}

impl std::error::Error for ParseError {}

/// Parse a source file into statements.
pub fn parse_file(_source: &str) -> Result<Vec<Statement>, ParseError> {
    todo!("parse_file implementation")
}

/// Parse a single query.
pub fn parse_query(_source: &str) -> Result<Vec<Literal>, ParseError> {
    todo!("parse_query implementation")
}
