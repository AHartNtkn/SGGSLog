use super::*;

// =============================================================================
// FAIRNESS / SENSIBLE DERIVATION SCHEDULING
// =============================================================================
//
// Reference: SGGSdpFOL Def. 32 (Sensible SGGS-derivation).
// We require a fair, non-heuristic scheduler that never starves applicable
// non-extension inferences.

use crate::sggs::{InferenceRule, next_inference, ConstrainedClause, Trail, InitialInterpretation};
use crate::constraint::Constraint;

fn unit(lit: Literal) -> ConstrainedClause {
    ConstrainedClause::with_constraint(Clause::new(vec![lit]), Constraint::True, 0)
}

#[test]
fn fairness_prefers_resolution_on_conflict() {
    // Conflict clause present with a resolvable justification on the left.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::neg("P", vec![Term::constant("a")])));
    trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("Q", vec![])])]);
    let rule = next_inference(&trail, &theory);
    assert_ne!(
        rule,
        InferenceRule::Extension,
        "non-extension inferences must not be starved when a conflict exists"
    );
    assert_ne!(rule, InferenceRule::None, "an applicable inference should be chosen");
}

#[test]
fn fairness_prefers_splitting_over_extension_when_intersection_exists() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![Term::var("X")])));
    trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("Q", vec![])])]);
    let rule = next_inference(&trail, &theory);
    assert_ne!(
        rule,
        InferenceRule::Extension,
        "non-extension inferences must not be starved when an intersection exists"
    );
    assert_ne!(rule, InferenceRule::None, "an applicable inference should be chosen");
}

#[test]
fn fairness_prefers_deletion_when_disposable_exists() {
    // Disposable clause example from SGGS deletion tests.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
    trail.push(unit(Literal::neg("Q", vec![Term::var("x")])));
    trail.push(unit(Literal::pos("P", vec![Term::var("x")])));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("R", vec![])])]);
    let rule = next_inference(&trail, &theory);
    assert_ne!(
        rule,
        InferenceRule::Extension,
        "non-extension inferences must not be starved when a disposable clause exists"
    );
    assert_ne!(rule, InferenceRule::None, "an applicable inference should be chosen");
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
