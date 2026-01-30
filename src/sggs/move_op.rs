//! SGGS-Move for conflict solving.

use super::Trail;

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
pub fn sggs_move(_trail: &mut Trail, _conflict_idx: usize) -> Result<(), MoveError> {
    todo!("sggs_move implementation")
}
