//! Parser for SGGSLog surface syntax.

mod ast;
mod lexer;
mod parser;

pub use ast::{Directive, Statement};
pub use parser::{parse_file, parse_query, ParseError};
