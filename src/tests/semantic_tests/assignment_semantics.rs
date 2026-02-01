use super::*;

// =============================================================================
// ASSIGNMENT SEMANTIC PROPERTIES
// =============================================================================
//
// Reference: [BP16a] Definitions 8-9 (Dependence and Assignment)
use crate::constraint::AtomicConstraint;
use crate::constraint::Constraint;
use crate::sggs::sggs_factoring;
use crate::sggs::sggs_left_split;
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
    // Source: bonacina2016.pdf, Definition 9 (Assignment), condition (4).
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    // Two identical selected premises make ¬P(a) depend on multiple clauses.
    // This makes the "rightmost" condition meaningful without inventing spurious dependencies.
    trail.push(ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        Constraint::True,
        0,
    ));
    trail.push(ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        Constraint::True,
        0,
    ));
    // Clause with two I-true literals; select one of them.
    trail.push(ConstrainedClause::with_constraint(
        Clause::new(vec![
            Literal::neg("P", vec![Term::constant("a")]),
            Literal::neg("P", vec![Term::constant("a")]),
        ]),
        Constraint::True,
        0,
    ));

    let assigns = compute_assignments(&trail);
    let j = 2; // clause index of the I-all-true clause
    let selected_idx = 0;
    let selected_assigned = assigns
        .assigned_to(j, selected_idx)
        .expect("selected assigned");
    // Condition (4) Def. 9: selected I-true literal assigned rightmost among assignments in clause.
    let mut max_assigned = selected_assigned;
    for lit_idx in 0..trail.clauses()[j].clause.literals.len() {
        if let Some(k) = assigns.assigned_to(j, lit_idx) {
            if k > max_assigned {
                max_assigned = k;
            }
        }
    }
    assert_eq!(selected_assigned, max_assigned);
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
fn conflict_requires_assignment_for_selected_i_true_literal() {
    // Source: Semantically_Guided_Goal_Sensitive_Reaso.pdf, Def. 12 (Assignment),
    // and SGGSdpFOL.pdf (conflict clause definition near Def. 1).
    //
    // Formal requirements:
    // - Conflict clause: all literals of the clause are uniformly false in I[Γ].
    // - Assignment (I-true literals): if an I-true literal is not selected, it must be assigned;
    //   if the selected literal is I-true and depends on some earlier selected literal, then it
    //   must be assigned (rightmost among assignments in the clause).
    //
    // Short quotes:
    // - "is a conflict clause, if all the literals of Cn are uniformly false in I[Γ]." (SGGSdpFOL)
    // - "selected I-true literals are assigned if possible;" (Bonacina 2016, Def. 12)

    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    // I-false selected literal makes P(a) true in I[Γ].
    trail.push(ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        Constraint::True,
        0,
    ));
    // I-true literal ¬P(a) is uniformly false in I[Γ] and becomes a conflict clause.
    trail.push(ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
        Constraint::True,
        0,
    ));

    let assigns = compute_assignments(&trail);
    let conflict_idx = 1;
    let selected_idx = 0;
    assert_eq!(
        assigns.assigned_to(conflict_idx, selected_idx),
        Some(0),
        "conflict selected I-true literal must be assigned when possible"
    );

    let interp = trail.interpretation();
    assert!(
        trail.clauses()[conflict_idx].is_conflict(&interp),
        "clause should be a conflict under I[Γ]"
    );
}

#[test]
fn i_all_true_selected_unassigned_is_not_conflict() {
    // Source: Semantically_Guided_Goal_Sensitive_Reaso.pdf, Def. 10 (Induced interpretation)
    // and Def. 12 (Assignment).
    //
    // Formal requirement:
    // - For ground literals not determined by I^p(Γ), I[Γ] agrees with I. Thus, an I-true
    //   selected literal with no dependency remains true in I[Γ], so the clause is not a conflict.
    //
    // Short quote:
    // - "if at (L) ∉ at (I p (Ŵ)), then I [Ŵ] |= L if and only if I |= L." (Bonacina 2016, Def. 10)
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    // Single I-all-true clause, no earlier clause to justify assignment.
    trail.push(ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
        Constraint::True,
        0,
    ));

    let assigns = compute_assignments(&trail);
    assert_eq!(
        assigns.assigned_to(0, 0),
        None,
        "no dependency => selected I-true literal may remain unassigned"
    );

    let interp = trail.interpretation();
    assert!(
        !trail.clauses()[0].is_conflict(&interp),
        "unassigned I-true selected literal should not yield a conflict"
    );
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

#[test]
fn assignment_preserved_after_factoring() {
    // Factoring should preserve the justification assignment of the selected literal.
    let a = Term::constant("a");
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![a.clone()])]),
        Constraint::True,
        0,
    ));
    let conflict = ConstrainedClause::with_constraint(
        Clause::new(vec![
            Literal::neg("P", vec![a.clone()]),
            Literal::neg("P", vec![a.clone()]),
        ]),
        Constraint::True,
        0,
    );
    trail.push(conflict.clone());

    let assigns = compute_assignments(&trail);
    assert_eq!(assigns.assigned_to(1, 0), Some(0));
    assert_eq!(assigns.assigned_to(1, 1), Some(0));

    let factored = sggs_factoring(&conflict, 1).expect("expected factoring");
    let mut trail2 = Trail::new(InitialInterpretation::AllNegative);
    trail2.push(ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![a.clone()])]),
        Constraint::True,
        0,
    ));
    trail2.push(factored);
    let assigns2 = compute_assignments(&trail2);
    assert_eq!(assigns2.assigned_to(1, 0), Some(0));
}

#[test]
fn assignment_after_left_split_representative() {
    // Left-split should preserve the dependency assignment on the representative.
    let base = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
        Constraint::True,
        0,
    );
    let conflict = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
        Constraint::True,
        0,
    );
    let split = sggs_left_split(&base, &conflict).expect("expected left split");
    let x_eq_a = Constraint::Atomic(AtomicConstraint::Identical(
        Term::var("x"),
        Term::constant("a"),
    ));
    let representative = split
        .parts
        .iter()
        .find(|p| p.constraint.clone().and(x_eq_a.clone()).is_satisfiable())
        .expect("expected representative intersecting with P(a)")
        .clone();

    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(representative);
    trail.push(conflict);

    let assigns = compute_assignments(&trail);
    assert_eq!(assigns.assigned_to(1, 0), Some(0));
}
