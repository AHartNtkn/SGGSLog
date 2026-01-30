use super::*;

// =============================================================================
// FAIRNESS PROGRESS REQUIREMENTS
// =============================================================================

use crate::sggs::{
    applicable_inferences, next_inference, InferenceRule, InitialInterpretation, Trail,
};

/// "All conflicting SGGS-extensions are followed right away by conflict solving."
/// (SGGSdpFOL, fairness paragraph)
///
/// Requirement: when a conflict-solving rule is applicable, next_inference must not choose extension.
#[test]
fn fairness_conflict_solving_not_starved_by_extension() {
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
    if has_conflict_solving {
        assert_ne!(
            next_inference(&trail, &theory),
            InferenceRule::Extension,
            "conflict solving should not be starved by extension"
        );
    }
}
