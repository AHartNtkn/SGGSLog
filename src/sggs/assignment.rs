//! SGGS assignment functions (Dependence and Assignment).

use std::collections::HashMap;

use super::Trail;

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
///
/// For each clause C_i and each I-true literal L in C_i (other than the selected literal),
/// the assignment records which earlier clause's selected literal justifies L being true.
pub fn compute_assignments(trail: &Trail) -> Assignments {
    let mut map = std::collections::HashMap::new();

    for (clause_idx, clause) in trail.clauses().iter().enumerate() {
        // For each literal in the clause
        for (lit_idx, lit) in clause.clause.literals.iter().enumerate() {
            // In normal clauses, skip the selected literal (it's I-false).
            // In conflict clauses (I-all-true), the selected literal is also I-true
            // and needs assignment for conflict resolution.
            // So we only skip if the selected literal is I-false.
            if lit_idx == clause.selected && trail.initial_interpretation().is_false(lit) {
                continue;
            }

            // Check if this literal is I-true
            if trail.initial_interpretation().is_true(lit) {
                // Find the earliest clause whose selected literal justifies this
                // An I-true literal L is justified by an I-false selected literal ~L
                // that appears earlier in the trail
                let negated = lit.negated();

                for (earlier_idx, earlier_clause) in
                    trail.clauses()[..clause_idx].iter().enumerate()
                {
                    let selected = earlier_clause.selected_literal();

                    // Selected must be I-false
                    if !trail.initial_interpretation().is_false(selected) {
                        continue;
                    }

                    // Check if the negated literal unifies with the selected literal
                    if negated.positive == selected.positive
                        && negated.atom.predicate == selected.atom.predicate
                        && crate::unify::unify_literals(&negated, selected).is_success()
                    {
                        map.insert((clause_idx, lit_idx), earlier_idx);
                        break;
                    }
                }
            }
        }
    }

    Assignments::new(map)
}
