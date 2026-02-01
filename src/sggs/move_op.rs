//! SGGS-Move for conflict solving.

use super::{ConstrainedClause, Trail};
use crate::unify::{unify_literals, UnifyResult};

/// Errors that can occur during SGGS-Move.
#[derive(Debug)]
pub enum MoveError {
    /// The clause at the given index is not a conflict clause
    NotConflictClause,
    /// No valid position found to move the clause
    NoValidPosition,
}

/// SGGS-Move: relocate I-all-true conflict clause leftward.
///
/// After conflict explanation produces an I-all-true conflict clause,
/// we move it leftward in the trail to "flip" its selected literal
/// from being uniformly false to being an implied literal.
///
/// The clause is moved to just before its rightmost justification,
/// which is the latest clause on the trail that makes one of the
/// conflict's literals uniformly false.
pub fn sggs_move(trail: &mut Trail, conflict_idx: usize) -> Result<(), MoveError> {
    // Check bounds
    if conflict_idx >= trail.clauses().len() {
        return Err(MoveError::NotConflictClause);
    }

    let conflict = trail.clauses()[conflict_idx].clone();

    // Check if it's a conflict clause (all literals uniformly false in I[Γ])
    if !is_conflict_clause(&conflict, trail) {
        return Err(MoveError::NotConflictClause);
    }

    // Find the rightmost justification: the latest clause that makes a literal false
    // A literal L is made false by an earlier clause C if C's selected literal is the
    // complement of L (i.e., C selects ¬L, making L false in I[Γ]).
    let rightmost_idx = find_rightmost_justification(&conflict, trail, conflict_idx);

    match rightmost_idx {
        Some(idx) => {
            // Check the condition from Def. 25: no other literal of the conflict
            // can be assigned to the same clause as the selected literal.
            // This means we can't have two literals of the conflict both assigned
            // to the same trail clause.
            if has_multiple_assignments_to_same_clause(&conflict, trail, idx) {
                return Err(MoveError::NoValidPosition);
            }

            // Move the conflict clause to just before the rightmost justification
            // Remove from current position
            let clause = trail.remove_clause(conflict_idx);

            // Calculate the new insert position
            // After removal, indices shift: if conflict_idx < idx, idx becomes idx-1
            let insert_pos = if conflict_idx < idx { idx - 1 } else { idx };

            // Insert before the rightmost justification
            trail.insert_clause(insert_pos, clause);

            Ok(())
        }
        None => Err(MoveError::NoValidPosition),
    }
}

/// Check if a clause is a conflict clause (all literals uniformly false in I[Γ]).
fn is_conflict_clause(clause: &ConstrainedClause, trail: &Trail) -> bool {
    let _init_interp = trail.initial_interpretation();
    let trail_interp = trail.interpretation();

    for lit in &clause.clause.literals {
        // A literal is uniformly false if its complement is uniformly true
        let complement = lit.negated();
        if !is_uniformly_true_or_i_false_not_assigned(&complement, lit, trail, &trail_interp) {
            return false;
        }
    }
    true
}

/// Check if a literal is uniformly true OR if the original literal is I-false and not assigned.
fn is_uniformly_true_or_i_false_not_assigned(
    complement: &crate::syntax::Literal,
    original: &crate::syntax::Literal,
    trail: &Trail,
    trail_interp: &super::TrailInterpretation,
) -> bool {
    // If complement is uniformly true, original is uniformly false
    if trail_interp.is_uniformly_true(complement) {
        return true;
    }

    // Otherwise, check if original is I-false and not made true by I^p(Γ)
    let init_interp = trail.initial_interpretation();
    if init_interp.is_false(original) {
        let partial = trail.partial_interpretation();
        return !partial.contains_ground(original);
    }

    false
}

/// Find the rightmost (latest) justification clause for the conflict.
///
/// A justification is a clause whose selected literal is the complement of
/// one of the conflict's literals, making that literal uniformly false.
fn find_rightmost_justification(
    conflict: &ConstrainedClause,
    trail: &Trail,
    conflict_idx: usize,
) -> Option<usize> {
    let init_interp = trail.initial_interpretation();
    let mut rightmost: Option<usize> = None;

    for lit in &conflict.clause.literals {
        let complement = lit.negated();

        // Find the latest clause that selects the complement
        for idx in 0..conflict_idx {
            let clause = &trail.clauses()[idx];
            let selected = clause.selected_literal();

            // Check if selected matches the complement
            if selected.positive == complement.positive
                && selected.atom.predicate == complement.atom.predicate
            {
                // Check if they unify (for non-ground cases)
                if let UnifyResult::Success(_) = unify_literals(selected, &complement) {
                    // Selected literal is I-false (contributes to model)
                    if init_interp.is_false(selected) && clause.constraint.is_satisfiable() {
                        match rightmost {
                            None => rightmost = Some(idx),
                            Some(r) if idx > r => rightmost = Some(idx),
                            _ => {}
                        }
                    }
                }
            }
        }
    }

    rightmost
}

/// Check if multiple literals of the conflict are assigned to the same clause.
///
/// According to Def. 25, move is not applicable if another literal of the
/// conflict clause is also assigned to the same clause.
fn has_multiple_assignments_to_same_clause(
    conflict: &ConstrainedClause,
    trail: &Trail,
    justification_idx: usize,
) -> bool {
    let justification = &trail.clauses()[justification_idx];
    let justification_selected = justification.selected_literal();
    let init_interp = trail.initial_interpretation();

    // Count how many literals of the conflict are assigned to this justification
    let mut count = 0;
    for lit in &conflict.clause.literals {
        let complement = lit.negated();

        if justification_selected.positive == complement.positive
            && justification_selected.atom.predicate == complement.atom.predicate
        {
            if let UnifyResult::Success(_) = unify_literals(justification_selected, &complement) {
                if init_interp.is_false(justification_selected)
                    && justification.constraint.is_satisfiable()
                {
                    count += 1;
                }
            }
        }
    }

    count > 1
}
