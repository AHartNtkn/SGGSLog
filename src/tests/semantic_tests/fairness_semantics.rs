use super::*;

// =============================================================================
// FAIRNESS / SENSIBLE DERIVATION SCHEDULING
// =============================================================================
//
// Reference: SGGSdpFOL Def. 32 (Sensible SGGS-derivation).
// We require a fair, non-heuristic scheduler that never starves applicable
// non-extension inferences.

use crate::sggs::{
    applicable_inferences, next_inference, ConstrainedClause, InferenceRule, InitialInterpretation,
    Trail,
};

fn assert_next_is_applicable(trail: &Trail, theory: &crate::theory::Theory) {
    let next = next_inference(trail, theory);
    let applicable = applicable_inferences(trail, theory);
    assert!(
        applicable.contains(&next),
        "next_inference must return an applicable rule"
    );
}

fn assert_no_extension_when_non_extension_exists(trail: &Trail, theory: &crate::theory::Theory) {
    let applicable = applicable_inferences(trail, theory);
    let has_non_extension = applicable
        .iter()
        .any(|r| *r != InferenceRule::Extension && *r != InferenceRule::None);
    if has_non_extension {
        let next = next_inference(trail, theory);
        assert_ne!(
            next,
            InferenceRule::Extension,
            "extension must not be chosen when a non-extension rule applies"
        );
    }
}

#[test]
fn fairness_prefers_resolution_on_conflict() {
    // Conflict clause present with a resolvable justification on the left.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::neg("P", vec![Term::constant("a")])));
    trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("Q", vec![])])]);
    assert_next_is_applicable(&trail, &theory);
    assert_no_extension_when_non_extension_exists(&trail, &theory);
}

#[test]
fn fairness_prefers_splitting_over_extension_when_intersection_exists() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![Term::var("X")])));
    trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("Q", vec![])])]);
    assert_next_is_applicable(&trail, &theory);
    assert_no_extension_when_non_extension_exists(&trail, &theory);
}

#[test]
fn fairness_prefers_deletion_when_disposable_exists() {
    // Disposable clause example from SGGS deletion tests.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
    trail.push(unit(Literal::neg("Q", vec![Term::var("x")])));
    trail.push(unit(Literal::pos("P", vec![Term::var("x")])));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("R", vec![])])]);
    assert_next_is_applicable(&trail, &theory);
    assert_no_extension_when_non_extension_exists(&trail, &theory);
}

#[test]
fn fairness_uses_extension_when_no_other_rule_applies() {
    let trail = Trail::new(InitialInterpretation::AllNegative);
    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos(
        "P",
        vec![Term::constant("a")],
    )])]);

    assert_eq!(next_inference(&trail, &theory), InferenceRule::Extension);
}
