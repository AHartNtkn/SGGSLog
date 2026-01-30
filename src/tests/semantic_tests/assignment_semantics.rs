use super::*;

// =============================================================================
// ASSIGNMENT SEMANTIC PROPERTIES
// =============================================================================
//
// Reference: [BP16a] Definitions 8-9 (Dependence and Assignment)
use crate::constraint::Constraint;
use crate::sggs::{compute_assignments, ConstrainedClause, InitialInterpretation, Trail};

#[test]
fn assignment_maps_i_true_literals_to_justification() {
    // Under I⁻: P(x) is selected (I-false), so ¬P(f(y)) depends on it.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let c1 = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
        Constraint::True,
        0,
    );
    let c2 = ConstrainedClause::with_constraint(
        Clause::new(vec![
            Literal::neg("P", vec![Term::app("f", vec![Term::var("y")])]),
            Literal::pos("Q", vec![Term::var("y")]),
        ]),
        Constraint::True,
        1,
    );
    trail.push(c1);
    trail.push(c2);

    let assigns = compute_assignments(&trail);
    let lit_idx = 0; // ¬P(f(y))
    let assigned = assigns.assigned_to(1, lit_idx);
    assert_eq!(assigned, Some(0));
}
