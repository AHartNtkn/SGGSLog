//! Normalization (clausification) from surface formulas to clauses.

use crate::parser::Statement;
use crate::syntax::{Clause, Formula};

/// Error during normalization.
#[derive(Debug, Clone)]
pub struct NormalizeError {
    pub message: String,
}

impl std::fmt::Display for NormalizeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for NormalizeError {}

/// Normalize a formula into a set of clauses (CNF + Skolemization).
pub fn clausify_formula(_formula: &Formula) -> Result<Vec<Clause>, NormalizeError> {
    todo!("clausify_formula implementation")
}

/// Normalize a single statement into clauses.
pub fn clausify_statement(_stmt: &Statement) -> Result<Vec<Clause>, NormalizeError> {
    todo!("clausify_statement implementation")
}

/// Normalize a list of statements into clauses.
///
/// This should use a single Skolem symbol generator across all statements.
pub fn clausify_statements(_stmts: &[Statement]) -> Result<Vec<Clause>, NormalizeError> {
    todo!("clausify_statements implementation")
}
