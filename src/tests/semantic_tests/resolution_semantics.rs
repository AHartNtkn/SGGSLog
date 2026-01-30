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

    match sggs_resolution(&conflict, &trail) {
        ResolutionResult::Resolvent(res) => {
            let interp = trail.interpretation();
            assert!(res.is_conflict(&interp));
        }
        other => panic!("Expected resolvent, got {:?}", other),
    }
}
