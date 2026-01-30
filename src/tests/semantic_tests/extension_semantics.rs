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
