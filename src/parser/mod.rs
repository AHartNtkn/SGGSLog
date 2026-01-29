//! Parser for SGGSLog surface syntax.

mod lexer;
mod ast;
mod parser;

pub use ast::{Statement, Directive};
pub use parser::{parse_file, parse_query, ParseError};
