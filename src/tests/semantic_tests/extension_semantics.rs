use super::*;

// =============================================================================
// SGGS EXTENSION SEMANTIC PROPERTIES
// =============================================================================
//
// Reference: [BP17] Definition 4 - SGGS-Extension
// "SGGS-extension adds an instance E of input clause C to the trail when the
// I-true literals of C unify with I-false selected literals on the trail."
//
// [BW20] Definition 1 also describes the extension rule.
use crate::sggs::{sggs_extension, ConstrainedClause, ExtensionResult, InitialInterpretation, Trail};

#[test]
fn extension_on_satisfiable_theory() {
    // [BP17] Def 4, [BW20] Def 1: Extension advances satisfiable theories
    let theory = theory_from_clauses(vec![
        // p(a) (fact)
        Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]),
        // ¬p(X) ∨ q(X) (rule: p(X) → q(X))
        Clause::new(vec![
            Literal::neg("p", vec![Term::var("X")]),
            Literal::pos("q", vec![Term::var("X")]),
        ]),
    ]);
    let trail = Trail::new(InitialInterpretation::AllNegative);
    let result = sggs_extension(&trail, &theory);
    match result {
        ExtensionResult::Extended(_) => {
            // Good - found an extension
        }
        ExtensionResult::NoExtension => {
            // Only valid if trail is complete
        }
        ExtensionResult::Conflict(_) => {
            panic!("[BP17] Satisfiable theory should not immediately conflict");
        }
    }
}

#[test]
fn extension_returns_no_extension_when_complete() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::NoExtension => {}
        other => panic!("Expected NoExtension on complete trail, got {:?}", other),
    }
}

#[test]
fn extension_uses_simultaneous_unification_of_i_true_literals() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("Q", vec![Term::constant("b")])]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::neg("Q", vec![Term::var("Y")]),
        Literal::pos("R", vec![Term::var("X"), Term::var("Y")]),
    ])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::Extended(cc) => {
            let got: std::collections::HashSet<_> =
                cc.clause.literals.clone().into_iter().collect();
            let expected: std::collections::HashSet<_> = vec![
                Literal::neg("P", vec![Term::constant("a")]),
                Literal::neg("Q", vec![Term::constant("b")]),
                Literal::pos("R", vec![Term::constant("a"), Term::constant("b")]),
            ]
            .into_iter()
            .collect();
            assert_eq!(got, expected);
            assert_eq!(
                cc.selected_literal(),
                &Literal::pos("R", vec![Term::constant("a"), Term::constant("b")])
            );
        }
        other => panic!("Expected Extended for simultaneous unification, got {:?}", other),
    }
}

#[test]
fn extension_inherits_constraints_from_side_premises() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let constrained = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
        crate::constraint::Constraint::Atomic(
            crate::constraint::AtomicConstraint::NotIdentical(
                Term::var("x"),
                Term::constant("a"),
            ),
        ),
        0,
    );
    trail.push(constrained);

    let theory = theory_from_clauses(vec![Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("Q", vec![Term::var("X")]),
    ])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::Extended(cc) => {
            let mut found = false;
            for v in cc.clause.variables() {
                let constraint = crate::constraint::Constraint::Atomic(
                    crate::constraint::AtomicConstraint::NotIdentical(
                        Term::Var(v.clone()),
                        Term::constant("a"),
                    ),
                );
                if !cc.constraint.intersects(&constraint.not()) {
                    found = true;
                    break;
                }
            }
            assert!(found, "extension should inherit side-premise constraints");
        }
        other => panic!("Expected extension, got {:?}", other),
    }
}
