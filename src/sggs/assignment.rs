//! SGGS assignment functions (Dependence and Assignment).

use std::collections::HashMap;

use super::Trail;
use crate::syntax::Literal;

/// Assignment mapping from (clause index, literal index) to justifying clause index.
#[derive(Debug, Clone, Default)]
pub struct Assignments {
    map: HashMap<(usize, usize), usize>,
}

impl Assignments {
    pub fn new(map: HashMap<(usize, usize), usize>) -> Self {
        Assignments { map }
    }

    /// Get the assigned justification index for a literal in a clause.
    pub fn assigned_to(&self, clause_idx: usize, lit_idx: usize) -> Option<usize> {
        self.map.get(&(clause_idx, lit_idx)).copied()
    }
}

/// Compute assignments for the given trail.
///
/// Assignments map I-true literals to I-false selected literals to the left
/// as defined in BP16a (Definitions 11 & 12).
pub fn compute_assignments(_trail: &Trail) -> Assignments {
    todo!("compute_assignments implementation")
}

/// Utility: find the literal index of a literal in a clause.
pub fn literal_index(clause: &[Literal], lit: &Literal) -> Option<usize> {
    clause.iter().position(|l| l == lit)
}
