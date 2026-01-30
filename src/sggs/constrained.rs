//! Constrained clauses for SGGS.

use super::TrailInterpretation;
use crate::constraint::Constraint;
use crate::syntax::{Clause, Literal};

/// A constrained clause with a selected literal.
///
/// In SGGS, each clause on the trail has:
/// - A constraint that restricts which ground instances are represented
/// - A selected literal that contributes to the model
#[derive(Debug, Clone)]
pub struct ConstrainedClause {
    /// The constraint on ground instances
    pub constraint: Constraint,
    /// The clause itself
    pub clause: Clause,
    /// Index of the selected literal
    pub selected: usize,
}

impl ConstrainedClause {
    /// Create a constrained clause with no constraint (True).
    pub fn new(clause: Clause, selected: usize) -> Self {
        todo!("ConstrainedClause::new implementation")
    }

    /// Create a constrained clause with an explicit constraint.
    pub fn with_constraint(clause: Clause, constraint: Constraint, selected: usize) -> Self {
        todo!("ConstrainedClause::with_constraint implementation")
    }

    /// Get the selected literal.
    pub fn selected_literal(&self) -> &Literal {
        todo!("ConstrainedClause::selected_literal implementation")
    }

    /// Check if this is a conflict clause in the given interpretation.
    pub fn is_conflict(&self, _interp: &TrailInterpretation) -> bool {
        todo!("ConstrainedClause::is_conflict implementation")
    }
}
