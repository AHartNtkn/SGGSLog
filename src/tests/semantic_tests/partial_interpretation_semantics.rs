use super::*;

// =============================================================================
// PARTIAL INTERPRETATION / PCGI / CCGI SEMANTICS
// =============================================================================
//
// References: Semantically_Guided_Goal_Sensitive_Reaso.pdf
// - Definitions 6-8 (I^p, pcgi, ccgi)
// - Definition 10 (induced interpretation I[Γ])

use crate::constraint::{AtomicConstraint, Constraint};
use crate::sggs::{ConstrainedClause, InitialInterpretation, Trail};

#[test]
fn partial_interpretation_respects_constraints() {
    // pcgi should include only instances satisfying the clause constraint.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let constrained = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
        Constraint::Atomic(AtomicConstraint::NotIdentical(
            Term::var("x"),
            Term::constant("a"),
        )),
        0,
    );
    trail.push(constrained);

    let ip = trail.partial_interpretation();
    let p_a = Literal::pos("P", vec![Term::constant("a")]);
    let p_b = Literal::pos("P", vec![Term::constant("b")]);
    assert!(!ip.contains_ground(&p_a));
    assert!(ip.contains_ground(&p_b));
}

#[test]
fn partial_interpretation_example_2_membership() {
    // Source: bonacina2016.pdf, Example 2 (pcgi examples).
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos(
        "P",
        vec![Term::constant("a"), Term::var("x")],
    )));
    trail.push(unit(Literal::pos(
        "P",
        vec![Term::constant("b"), Term::var("y")],
    )));
    trail.push(unit(Literal::neg(
        "P",
        vec![Term::var("z"), Term::var("z")],
    )));
    trail.push(unit(Literal::pos(
        "P",
        vec![Term::var("u"), Term::var("v")],
    )));

    let ip = trail.partial_interpretation();
    assert!(ip.contains_ground(&Literal::pos(
        "P",
        vec![Term::constant("a"), Term::constant("a")]
    )));
    assert!(ip.contains_ground(&Literal::pos(
        "P",
        vec![Term::constant("b"), Term::constant("a")]
    )));

    // Complementary instance of ¬P(z,z) should not be in I^p.
    assert!(!ip.contains_ground(&Literal::neg(
        "P",
        vec![Term::constant("a"), Term::constant("a")]
    )));
    // Proper instance of ¬P(z,z) should be in I^p.
    assert!(ip.contains_ground(&Literal::neg(
        "P",
        vec![Term::constant("c"), Term::constant("c")]
    )));

    // P(u,v) excludes instances already satisfied by earlier clauses.
    assert!(!ip.contains_ground(&Literal::pos(
        "P",
        vec![Term::constant("a"), Term::constant("c")]
    )));
    assert!(ip.contains_ground(&Literal::pos(
        "P",
        vec![Term::constant("c"), Term::constant("d")]
    )));
}

#[test]
fn proper_vs_complementary_instances_unit_clause() {
    // For unit clauses, pcgi/ccgi classification reduces to membership in I^p(Γ|j-1).
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos(
        "P",
        vec![Term::constant("a"), Term::var("x")],
    )));
    trail.push(unit(Literal::pos(
        "P",
        vec![Term::constant("b"), Term::var("y")],
    )));
    trail.push(unit(Literal::neg(
        "P",
        vec![Term::var("z"), Term::var("z")],
    )));

    // For clause index 2 (0-based), ¬P(a,a) is complementary, ¬P(c,c) is proper.
    let neg_p_aa = Literal::neg("P", vec![Term::constant("a"), Term::constant("a")]);
    let neg_p_cc = Literal::neg("P", vec![Term::constant("c"), Term::constant("c")]);

    assert!(trail.is_complementary_selected_instance(2, &neg_p_aa));
    assert!(!trail.is_proper_selected_instance(2, &neg_p_aa));

    assert!(trail.is_proper_selected_instance(2, &neg_p_cc));
    assert!(!trail.is_complementary_selected_instance(2, &neg_p_cc));
}

#[test]
fn induced_interpretation_all_true_clause_no_effect() {
    // I-all-true clauses do not change I[Γ] (Definition 10 / Theorem 1).
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::neg("P", vec![Term::constant("a")])));
    let interp = trail.interpretation();

    let p_a = Literal::pos("P", vec![Term::constant("a")]);
    let not_p_a = Literal::neg("P", vec![Term::constant("a")]);
    assert!(interp.is_uniformly_false(&p_a));
    assert!(interp.is_uniformly_true(&not_p_a));
}

#[test]
fn uniform_falsity_from_selected_literal() {
    // If P(x) is selected (I-false under I-), then all ¬P(t) are uniformly false in I[Γ].
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
    let interp = trail.interpretation();

    let not_p_a = Literal::neg("P", vec![Term::constant("a")]);
    assert!(interp.is_uniformly_false(&not_p_a));
}

#[test]
fn disposable_when_no_constrained_instances() {
    // If Gr(A ⊲ C) is empty, then pcgi and ccgi are empty, so the clause is disposable.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let clause = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
        Constraint::False,
        0,
    );
    trail.push(clause);

    let lit = Literal::pos("P", vec![Term::constant("a")]);
    assert!(!trail.is_proper_selected_instance(0, &lit));
    assert!(!trail.is_complementary_selected_instance(0, &lit));
    assert!(crate::sggs::is_disposable(&trail.clauses()[0], &trail));
}
