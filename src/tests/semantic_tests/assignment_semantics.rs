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

#[test]
fn assignment_selected_i_true_is_rightmost_dependency() {
    // Under I⁻, negative literals are I-true. Selected I-true should be assigned rightmost.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let c1 = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        Constraint::True,
        0,
    );
    let c2 = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("Q", vec![Term::constant("a")])]),
        Constraint::True,
        0,
    );
    let c3 = ConstrainedClause::with_constraint(
        Clause::new(vec![
            Literal::neg("P", vec![Term::constant("a")]),
            Literal::neg("Q", vec![Term::constant("a")]),
        ]),
        Constraint::True,
        0, // select ¬P(a) (I-true)
    );
    trail.push(c1);
    trail.push(c2);
    trail.push(c3);

    let assigns = compute_assignments(&trail);
    // Clause index 2, literal 0 (selected) should be assigned to rightmost dependency (index 1).
    assert_eq!(assigns.assigned_to(2, 0), Some(1));
    // The other literal depends on clause 1 as well.
    assert_eq!(assigns.assigned_to(2, 1), Some(1));
}

#[test]
fn assignment_selected_i_true_only_if_possible() {
    // [BP16a] Def 12: Non-selected I-true must be assigned if possible;
    // selected I-true is assigned only if possible.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let c1 = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        Constraint::True,
        0,
    );
    // I-all-true clause with two negative literals, but only ¬P(a) has a dependency.
    let c2 = ConstrainedClause::with_constraint(
        Clause::new(vec![
            Literal::neg("P", vec![Term::constant("a")]),
            Literal::neg("Q", vec![Term::constant("a")]),
        ]),
        Constraint::True,
        1, // select ¬Q(a), which has no justification
    );
    trail.push(c1);
    trail.push(c2);

    let assigns = compute_assignments(&trail);
    // Non-selected I-true literal ¬P(a) should be assigned to clause 0.
    assert_eq!(assigns.assigned_to(1, 0), Some(0));
    // Selected I-true literal ¬Q(a) has no dependency, so remains unassigned.
    assert_eq!(assigns.assigned_to(1, 1), None);
}

#[test]
fn assignment_ignores_i_false_literals() {
    // Under I⁻, positive literals are I-false and should not be assigned.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let c1 = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        Constraint::True,
        0,
    );
    trail.push(c1);

    let assigns = compute_assignments(&trail);
    assert_eq!(assigns.assigned_to(0, 0), None);
}
