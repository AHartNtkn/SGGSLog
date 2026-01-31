use super::*;

// =============================================================================
// FAIRNESS / SENSIBLE DERIVATION SCHEDULING
// =============================================================================
//
// Reference: SGGSdpFOL Def. 32 (Sensible SGGS-derivation).
// We require a fair, non-heuristic scheduler that never starves applicable
// non-extension inferences.

use crate::sggs::{
    applicable_inferences, next_inference, InferenceRule, InitialInterpretation, Trail,
};

fn assert_next_is_applicable(trail: &Trail, theory: &crate::theory::Theory) {
    let next = next_inference(trail, theory);
    let applicable = applicable_inferences(trail, theory);
    assert!(
        applicable.contains(&next),
        "next_inference must return an applicable rule"
    );
}

/// "An inference is applied whenever ⊥ ∉ Γ and I[Γ ] ⊭ S."
/// (SGGSdpFOL, fairness paragraph)
///
/// Requirement: next_inference must return some applicable rule when a conflict exists.
#[test]
fn fairness_returns_applicable_rule_on_conflict() {
    // Conflict clause present with a resolvable justification on the left.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::neg("P", vec![Term::constant("a")])));
    trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("Q", vec![])])]);
    assert_next_is_applicable(&trail, &theory);
}

/// "Inferences applying to shorter prefixes of the trail are never neglected in favor of others
/// applying to longer prefixes."
/// (SGGSdpFOL, fairness paragraph)
///
/// Requirement: if splitting is applicable, it must appear among applicable rules.
#[test]
fn fairness_reports_splitting_applicable_on_intersection() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![Term::var("X")])));
    trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("Q", vec![])])]);
    let applicable = applicable_inferences(&trail, &theory);
    assert!(
        applicable.contains(&InferenceRule::Splitting)
            || applicable.contains(&InferenceRule::Deletion),
        "splitting or deletion should be applicable when selected literals intersect"
    );
    assert_next_is_applicable(&trail, &theory);
}

/// "SGGSdeletion is applied eagerly."
/// (SGGSdpFOL, fairness paragraph)
///
/// Requirement: deletion must be applicable when a disposable clause exists.
#[test]
fn fairness_reports_deletion_applicable_when_disposable_exists() {
    // Disposable clause example from SGGS deletion tests.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
    trail.push(unit(Literal::neg("Q", vec![Term::var("x")])));
    trail.push(unit(Literal::pos("P", vec![Term::var("x")])));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("R", vec![])])]);
    let applicable = applicable_inferences(&trail, &theory);
    assert!(
        applicable.contains(&InferenceRule::Deletion),
        "deletion should be applicable when a disposable clause exists"
    );
    assert_next_is_applicable(&trail, &theory);
}

#[test]
fn fairness_reports_deletion_applicable_when_prefix_satisfies_clause() {
    // Disposable by left-prefix satisfaction (Bonacina 2016, Example 2).
    // Source: SGGSdpFOL.pdf, fairness paragraph.
    // Quote: "SGGS-deletion is applied eagerly."
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
    trail.push(unit(Literal::neg("Q", vec![Term::var("x")])));
    trail.push(unit(Literal::pos("P", vec![Term::var("x")])));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("R", vec![])])]);
    let applicable = applicable_inferences(&trail, &theory);
    assert!(
        applicable.contains(&InferenceRule::Deletion),
        "deletion should be applicable for a clause satisfied by its prefix"
    );
    assert_next_is_applicable(&trail, &theory);
}

#[test]
fn fairness_excludes_extension_when_conflict_exists() {
    // When a conflict clause exists, conflict-solving or deletion must take precedence
    // in the scheduling policy (Def. 32 sensible SGGS-derivation).
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));
    trail.push(unit(Literal::neg("P", vec![Term::constant("a")])));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("Q", vec![])])]);
    let next = next_inference(&trail, &theory);
    assert!(
        !matches!(next, InferenceRule::Extension),
        "extension must not be chosen while a conflict exists"
    );
}

#[test]
fn fairness_excludes_trivial_splitting() {
    // Trivial splitting (singleton partition) must not be scheduled.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![Term::var("X")])));
    trail.push(unit(Literal::pos("P", vec![Term::var("Y")]))); // alpha-equivalent, trivial split

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("Q", vec![])])]);
    let applicable = applicable_inferences(&trail, &theory);
    assert!(
        !applicable.contains(&InferenceRule::Splitting),
        "trivial splitting should not be applicable"
    );
    assert!(
        applicable.contains(&InferenceRule::Deletion),
        "deletion should be applicable for a disposable duplicate"
    );
}

/// "An inference is applied whenever ⊥ ∉ Γ and I[Γ ] ⊭ S."
/// (SGGSdpFOL, fairness paragraph)
///
/// Requirement: if no non-extension rule applies, extension should be chosen.
#[test]
fn fairness_uses_extension_when_no_other_rule_applies() {
    let trail = Trail::new(InitialInterpretation::AllNegative);
    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos(
        "P",
        vec![Term::constant("a")],
    )])]);

    assert_eq!(next_inference(&trail, &theory), InferenceRule::Extension);
}
