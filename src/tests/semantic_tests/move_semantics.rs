use super::*;

// =============================================================================
// SGGS MOVE SEMANTICS
// =============================================================================
//
// Reference: [BP17] conflict-solving rules (move)
use crate::constraint::Constraint;
use crate::sggs::{sggs_move, ConstrainedClause, InitialInterpretation, MoveError, Trail};

#[test]
fn sggs_move_reorders_conflict_before_justification() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let c1 = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        Constraint::True,
        0,
    );
    let c2 = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
        Constraint::True,
        0,
    );
    trail.push(c1);
    trail.push(c2);

    let result = sggs_move(&mut trail, 1);
    assert!(result.is_ok());
    assert_eq!(
        trail.clauses()[0].selected_literal(),
        &Literal::neg("P", vec![Term::constant("a")])
    );
}

#[test]
fn sggs_move_rejects_non_conflict_clause() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));
    let result = sggs_move(&mut trail, 0);
    assert!(matches!(result, Err(MoveError::NotConflictClause)));
}
