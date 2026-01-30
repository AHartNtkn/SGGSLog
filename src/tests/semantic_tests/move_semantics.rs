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

#[test]
fn sggs_move_rejects_conflict_without_assignment() {
    // A conflict clause with no assignment should not be movable.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));
    let result = sggs_move(&mut trail, 0);
    assert!(matches!(result, Err(MoveError::NoValidPosition)));
}

#[test]
fn sggs_move_moves_before_rightmost_assignment() {
    // Source: paper6.pdf, assignment rule: selected I-true literal is assigned rightmost.
    // Source: SGGSdpFOL.pdf, Fig. 2 (move rule).
    // Move should relocate the conflict clause just before its rightmost justification.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    // Two identical P(a) premises make ¬P(a) depend on both; rightmost is index 1.
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));

    // I-all-true conflict clause with selected literal assigned rightmost by Def. 9.
    let conflict = ConstrainedClause::new(
        Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
        0,
    );
    trail.push(conflict);

    let result = sggs_move(&mut trail, 2);
    assert!(result.is_ok());
    // Conflict clause should now be just before the rightmost justification (second P).
    assert_eq!(
        trail.clauses()[1].selected_literal(),
        &Literal::neg("P", vec![Term::constant("a")])
    );
    assert_eq!(
        trail.clauses()[2].selected_literal(),
        &Literal::pos("P", vec![Term::constant("a")])
    );
}
