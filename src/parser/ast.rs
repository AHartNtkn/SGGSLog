//! AST types for SGGSLog surface syntax.

use crate::syntax::{Clause, Literal};

/// A statement in a SGGSLog source file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    /// A clause (disjunction of literals)
    Clause(Clause),
    /// A query to prove
    Query(Vec<Literal>),
    /// A directive
    Directive(Directive),
}

/// A directive in SGGSLog.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Directive {
    /// Load a file
    Load(String),
    /// Set a configuration option
    Set(String, String),
}
