use super::*;

// =============================================================================
// CONFLICT-SOLVING INTEGRATION (EXTENSION -> CONFLICT -> MOVE -> RESOLUTION)
// =============================================================================
//
// References: Semantically_Guided_Goal_Sensitive_Reaso.pdf (Example 9),
// SGGSdpFOL.pdf (conflict explanation and move rules).

use crate::constraint::Constraint;
use crate::sggs::{
    sggs_extension, sggs_factoring, sggs_left_split, sggs_move, sggs_resolution, ConstrainedClause,
    ExtensionResult, InitialInterpretation, ResolutionResult, Trail,
};

#[test]
fn conflict_solving_chain_reaches_empty_clause() {
    // Theory: P(a), ¬P(x) ∨ Q(x), ¬Q(a)
    let a = Term::constant("a");
    let theory = theory_from_clauses(vec![
        Clause::new(vec![Literal::pos("P", vec![a.clone()])]),
        Clause::new(vec![
            Literal::neg("P", vec![Term::var("X")]),
            Literal::pos("Q", vec![Term::var("X")]),
        ]),
        Clause::new(vec![Literal::neg("Q", vec![a.clone()])]),
    ]);

    let mut trail = Trail::new(InitialInterpretation::AllNegative);

    // Extension 1: add P(a)
    match sggs_extension(&trail, &theory) {
        ExtensionResult::Extended(cc) => trail.push(cc),
        other => panic!("Expected extension for P(a), got {:?}", other),
    }

    // Extension 2: add ¬P(a) ∨ Q(a)
    match sggs_extension(&trail, &theory) {
        ExtensionResult::Extended(cc) => trail.push(cc),
        other => panic!("Expected extension for ¬P(a) ∨ Q(a), got {:?}", other),
    }

    // Extension 3: add ¬Q(a) as a conflict clause
    let conflict = match sggs_extension(&trail, &theory) {
        ExtensionResult::Conflict(cc) => cc,
        other => panic!("Expected conflict extension, got {:?}", other),
    };
    trail.push(conflict.clone());

    // Move conflict clause before its rightmost justification (Q(a)).
    let conflict_idx = trail.clauses().len() - 1;
    sggs_move(&mut trail, conflict_idx).expect("move failed");

    let moved_idx = trail
        .clauses()
        .iter()
        .position(|c| c.selected_literal() == &Literal::neg("Q", vec![a.clone()]))
        .expect("moved conflict clause not found");

    // Resolve ¬Q(a) with ¬P(a) ∨ Q(a) to get ¬P(a), which is I-all-true.
    let conflict_clause = trail.clauses()[moved_idx].clone();
    let res1 = sggs_resolution(&conflict_clause, &trail);
    let cc = match res1 {
        ResolutionResult::ConflictClause(cc) => cc,
        other => panic!("Expected conflict clause resolvent, got {:?}", other),
    };
    assert_eq!(cc.clause.literals, vec![Literal::neg("P", vec![a.clone()])]);

    // Resolve ¬P(a) with P(a) to derive the empty clause.
    let res2 = sggs_resolution(&cc, &trail);
    assert!(matches!(res2, ResolutionResult::EmptyClause));
}

#[test]
fn resolution_can_return_conflict_clause() {
    // If resolution yields an I-all-true clause, it should return ConflictClause.
    let a = Term::constant("a");
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![a.clone()])));
    trail.push(unit(Literal::pos("Q", vec![a.clone()])));

    let conflict = ConstrainedClause::with_constraint(
        Clause::new(vec![
            Literal::neg("P", vec![a.clone()]),
            Literal::neg("Q", vec![a.clone()]),
        ]),
        Constraint::True,
        0,
    );
    trail.push(conflict.clone());

    match sggs_resolution(&conflict, &trail) {
        ResolutionResult::ConflictClause(cc) => {
            assert!(cc.clause.literals.iter().all(|l| !l.positive));
        }
        other => panic!("Expected ConflictClause, got {:?}", other),
    }
}

#[test]
fn conflict_solving_chain_with_factoring() {
    // Source: SGGSdpFOL, Fig. 2 (factor) and conflict solving sequence.
    // Conflict clause with duplicate same-sign literal should be factored before resolution.
    let a = Term::constant("a");
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![a.clone()])));

    let conflict = ConstrainedClause::with_constraint(
        Clause::new(vec![
            Literal::neg("P", vec![a.clone()]),
            Literal::neg("P", vec![a.clone()]),
        ]),
        Constraint::True,
        0,
    );

    let factored = sggs_factoring(&conflict, 1).expect("expected factoring");
    trail.push(factored.clone());

    let res = sggs_resolution(&factored, &trail);
    assert!(
        matches!(res, ResolutionResult::EmptyClause),
        "factoring should allow resolution to reach empty clause"
    );
}

#[test]
fn conflict_solving_chain_with_left_split() {
    // Source: SGGSdpFOL, Fig. 2 (l-split) and conflict solving sequence.
    // Left-split should isolate the intersection so resolution can eliminate the conflict.
    let a = Term::constant("a");
    let mut trail = Trail::new(InitialInterpretation::AllNegative);

    let base = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
        Constraint::True,
        0,
    );
    trail.push(base.clone());

    let conflict = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::neg("P", vec![a.clone()])]),
        Constraint::True,
        0,
    );

    let split = sggs_left_split(&base, &conflict).expect("expected left split");
    let x_eq_a = Constraint::Atomic(crate::constraint::AtomicConstraint::Identical(
        Term::var("x"),
        a.clone(),
    ));
    let representative = split
        .parts
        .iter()
        .find(|p| p.constraint.clone().and(x_eq_a.clone()).is_satisfiable())
        .expect("expected representative intersecting with P(a)")
        .clone();

    let mut trail2 = Trail::new(InitialInterpretation::AllNegative);
    trail2.push(representative.clone());
    trail2.push(conflict.clone());

    let res = sggs_resolution(&conflict, &trail2);
    assert!(
        matches!(
            res,
            ResolutionResult::EmptyClause | ResolutionResult::ConflictClause(_)
        ),
        "left split should enable conflict solving on the isolated intersection"
    );
}
