use super::*;

// =============================================================================
// SGGS RESOLUTION SEMANTIC PROPERTIES
// =============================================================================
//
// Reference: SGGSdpFOL Definition 2 (SGGS-Resolution)
// "SGGS-resolution resolves a conflict clause with justifications from the
// trail's disjoint prefix."
//
// Reference: [BP17] Section 5 - Conflict Explanation
// "Resolution is used to explain conflicts and derive lemmas."
use crate::constraint::{AtomicConstraint, Constraint};
use crate::sggs::{
    sggs_resolution, ConstrainedClause, InitialInterpretation, ResolutionResult, Trail,
};

#[test]
fn resolution_preserves_conflict() {
    // [BP17] Def 6: Resolution explains conflicts while preserving conflict status.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let left = ConstrainedClause::new(
        Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
        0,
    );
    trail.push(left);

    let conflict = ConstrainedClause::new(
        Clause::new(vec![
            Literal::pos("P", vec![Term::constant("a")]),
            Literal::pos("Q", vec![Term::constant("a")]),
        ]),
        0,
    );
    trail.push(conflict.clone());

    let interp = trail.interpretation();
    match sggs_resolution(&conflict, &trail) {
        ResolutionResult::Resolvent(res) => {
            assert!(res.is_conflict(&interp));
        }
        ResolutionResult::EmptyClause => {
            panic!("Expected non-empty conflict-preserving resolvent");
        }
        ResolutionResult::Inapplicable => {
            panic!("Resolution should be applicable");
        }
    }
}

#[test]
fn resolution_uses_conflict_constraint_when_entails_justification() {
    // SGGSdpFOL Def. 26: requires A |= Bϑ; resolvent keeps A as its constraint.
    let a = Term::constant("a");
    let b = Term::constant("b");
    let x = Term::var("X");
    let constraint_a = Constraint::Atomic(AtomicConstraint::Identical(x.clone(), a.clone()));
    let constraint_b = Constraint::Or(
        Box::new(Constraint::Atomic(AtomicConstraint::Identical(
            x.clone(),
            a.clone(),
        ))),
        Box::new(Constraint::Atomic(AtomicConstraint::Identical(
            x.clone(),
            b.clone(),
        ))),
    );

    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let justification = ConstrainedClause::with_constraint(
        Clause::new(vec![
            Literal::neg("P", vec![x.clone()]),
            Literal::pos("S", vec![a.clone()]),
        ]),
        constraint_b.clone(),
        0,
    );
    trail.push(justification);

    let conflict = ConstrainedClause::with_constraint(
        Clause::new(vec![
            Literal::pos("P", vec![x.clone()]),
            Literal::pos("R", vec![a.clone()]),
        ]),
        constraint_a.clone(),
        0,
    );
    trail.push(conflict.clone());

    match sggs_resolution(&conflict, &trail) {
        ResolutionResult::Resolvent(res) => {
            assert_eq!(res.constraint, constraint_a);
            let lits: std::collections::HashSet<_> =
                res.clause.literals.iter().cloned().collect();
            let expected: std::collections::HashSet<_> = vec![
                Literal::pos("R", vec![a.clone()]),
                Literal::pos("S", vec![a.clone()]),
            ]
            .into_iter()
            .collect();
            assert_eq!(lits, expected);
        }
        ResolutionResult::EmptyClause => {
            panic!("Expected non-empty resolvent with preserved constraint");
        }
        ResolutionResult::Inapplicable => {
            panic!("Resolution should be applicable");
        }
    }
}

#[test]
fn resolution_inapplicable_when_constraint_not_entails() {
    // SGGS-resolution requires A |= Bϑ; if not, resolution is inapplicable.
    let x = Term::var("X");
    let a = Term::constant("a");
    let b = Term::constant("b");
    let constraint_a = Constraint::Atomic(AtomicConstraint::Identical(x.clone(), a.clone()));
    let constraint_b = Constraint::Atomic(AtomicConstraint::Identical(x.clone(), b.clone()));

    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let justification = ConstrainedClause::with_constraint(
        Clause::new(vec![
            Literal::neg("P", vec![x.clone()]),
            Literal::pos("S", vec![b.clone()]),
        ]),
        constraint_b.clone(),
        0,
    );
    trail.push(justification);

    let conflict = ConstrainedClause::with_constraint(
        Clause::new(vec![
            Literal::pos("P", vec![x.clone()]),
            Literal::pos("R", vec![a.clone()]),
        ]),
        constraint_a.clone(),
        0,
    );
    trail.push(conflict.clone());

    match sggs_resolution(&conflict, &trail) {
        ResolutionResult::Inapplicable => {}
        other => panic!("Expected inapplicable resolution, got {:?}", other),
    }
}

#[test]
fn resolution_inapplicable_when_clause_is_not_conflict() {
    // Resolution applies only to conflict clauses (all literals uniformly false).
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    // I-all-true justification in dp(Γ).
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
        0,
    ));

    // Not a conflict: contains an I-true literal under I⁻.
    let not_conflict = ConstrainedClause::new(
        Clause::new(vec![
            Literal::pos("P", vec![Term::constant("a")]),
            Literal::neg("Q", vec![Term::constant("a")]),
        ]),
        0,
    );
    trail.push(not_conflict.clone());

    match sggs_resolution(&not_conflict, &trail) {
        ResolutionResult::Inapplicable => {}
        other => panic!("Expected inapplicable resolution, got {:?}", other),
    }
}

#[test]
fn resolution_inapplicable_when_justification_outside_dp() {
    // Resolution requires the justification to be in dp(Γ).
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    // dp(Γ) will stop at index 1 due to unifiable selected literals.
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::neg("P", vec![Term::constant("b")])]),
        0,
    ));
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::neg("P", vec![Term::var("X")])]),
        0,
    ));

    let conflict = ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    );
    trail.push(conflict.clone());

    match sggs_resolution(&conflict, &trail) {
        ResolutionResult::Inapplicable => {}
        other => panic!("Expected inapplicable resolution, got {:?}", other),
    }
}

#[test]
fn resolution_inapplicable_when_justification_not_i_all_true() {
    // Justification must be I-all-true; under I⁻ a positive clause is I-false.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let justification = ConstrainedClause::new(
        Clause::new(vec![
            Literal::neg("P", vec![Term::constant("a")]),
            Literal::pos("Q", vec![Term::constant("a")]),
        ]),
        0,
    );
    trail.push(justification);

    let conflict = ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    );
    trail.push(conflict.clone());

    match sggs_resolution(&conflict, &trail) {
        ResolutionResult::Inapplicable => {}
        other => panic!("Expected inapplicable resolution, got {:?}", other),
    }
}
