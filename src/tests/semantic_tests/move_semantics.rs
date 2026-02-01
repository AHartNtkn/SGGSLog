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
fn sggs_move_succeeds_with_valid_assignment() {
    // SGGSdpFOL (Fig. 2, move rule) formal conditions:
    // - Assuming A ⊲ C[L] ∈ dp(Γ), D[M] is I-all-true, and M is assigned to A ⊲ C[L].
    // - Move applies if ¬Gr(B ⊲ M) = pcgi(A ⊲ L, Γ) and no other literal of D is assigned to C.
    // Quote: "if ¬Gr(B B M) = pcgi(A B L, Γ ) and no other literal of D is assigned to C".
    // A conflict clause with a valid justification in dp(Γ) should be movable.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    // P(a) is I-false, contributes to model, makes ¬P(a) uniformly false.
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));
    // ¬P(a) is now a conflict clause (uniformly false in I[Γ]).
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
        0,
    ));
    // Move should work here because P(a) justifies ¬P(a).
    let result = sggs_move(&mut trail, 1);
    assert!(
        result.is_ok(),
        "move should succeed with valid justification"
    );
}

#[test]
fn sggs_move_rejects_conflict_when_other_literal_assigned_to_same_clause() {
    // Def. 25: move requires that no other literal of the conflict clause is assigned to C.
    let a = Term::constant("a");
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![a.clone()])]),
        0,
    ));
    let conflict = ConstrainedClause::new(
        Clause::new(vec![
            Literal::neg("P", vec![a.clone()]),
            Literal::neg("P", vec![a.clone()]),
        ]),
        0,
    );
    trail.push(conflict);

    let result = sggs_move(&mut trail, 1);
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
