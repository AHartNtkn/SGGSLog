//! AST types for SGGSLog surface syntax.

use crate::syntax::{Clause, Formula, Literal};

/// A statement in a SGGSLog source file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    /// A clause (disjunction of literals)
    Clause(Clause),
    /// A formula (surface syntax, not yet normalized)
    Formula(Formula),
    /// A query to prove
    Query(Vec<Literal>),
    /// A directive
    Directive(Directive),
}

/// A typed configuration setting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Setting {
    TimeoutMs(u64),
    Projection(ProjectionSetting),
    Unknown { key: String, value: String },
}

/// Projection modes for user-visible answers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProjectionSetting {
    OnlyUserSymbols,
    AllowInternal,
}

/// A directive in SGGSLog.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Directive {
    /// Load a file
    Load(String),
    /// Set a configuration option
    Set(Setting),
    /// Request the next answer in the current query stream
    Next,
}
