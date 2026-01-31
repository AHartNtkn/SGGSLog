use super::*;

// =============================================================================
// FAIRNESS PROGRESS REQUIREMENTS
// =============================================================================

use crate::sggs::{
    applicable_inferences, next_inference, InferenceRule, InitialInterpretation, Trail,
};

/// Conflict-solving rules must be reported as applicable when a conflict exists.
/// (SGGSdpFOL, fairness paragraph)
///
/// Scheduling among applicable rules is nondeterministic; do not require
/// conflict-solving to be chosen immediately (spec.md).
#[test]
fn fairness_reports_conflict_solving_applicable_on_conflict() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));
    trail.push(unit(Literal::neg("P", vec![Term::constant("a")])));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("Q", vec![])])]);
    let applicable = applicable_inferences(&trail, &theory);
    let has_conflict_solving = applicable.iter().any(|r| {
        matches!(
            r,
            InferenceRule::Resolution
                | InferenceRule::Move
                | InferenceRule::LeftSplit
                | InferenceRule::Factoring
        )
    });
    assert!(
        has_conflict_solving,
        "conflict-solving should be applicable when a conflict exists"
    );
    let next = next_inference(&trail, &theory);
    assert!(
        applicable.contains(&next),
        "next_inference must return an applicable rule"
    );
}
