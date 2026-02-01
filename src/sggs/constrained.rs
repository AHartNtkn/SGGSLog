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
        ConstrainedClause {
            constraint: Constraint::True,
            clause,
            selected,
        }
    }

    /// Create a constrained clause with an explicit constraint.
    pub fn with_constraint(clause: Clause, constraint: Constraint, selected: usize) -> Self {
        ConstrainedClause {
            constraint,
            clause,
            selected,
        }
    }

    /// Get the selected literal.
    pub fn selected_literal(&self) -> &Literal {
        &self.clause.literals[self.selected]
    }

    /// Check if this is a conflict clause in the given interpretation.
    /// A conflict clause has all literals uniformly false.
    pub fn is_conflict(&self, interp: &TrailInterpretation) -> bool {
        self.clause.literals.iter().all(|lit| interp.is_uniformly_false(lit))
    }
}
