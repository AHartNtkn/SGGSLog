use super::*;

// =============================================================================
// SGGS TRAIL INVARIANTS
// =============================================================================
//
// These tests verify the invariants of SGGS trails as defined in [BP16a].
//
// Key concepts from [BP16a]:
// - Trail Γ = C₁[L₁], ..., Cₙ[Lₙ] is a sequence of constrained clauses
// - Each clause has a selected literal Lᵢ
// - The trail represents a partial interpretation I^p(Γ)
// - Literals are "I-false" (uniformly false in I) or "I-true" (true in I)
// - Selected literals should be I-false to "differentiate from I"
use crate::constraint::{AtomicConstraint, Constraint};
use crate::sggs::{ConstrainedClause, InitialInterpretation, Trail};

// -------------------------------------------------------------------------
// Property: Selected literals are I-false
//
// Reference: [BP16a] Section 3 - Trail Interpretation
// "SGGS requires that if a clause in the trail has I-false literals, one is
// selected, so as to differentiate from I."
//
// Under I⁻ (all atoms false): positive literals are I-false
// Under I⁺ (all atoms true): negative literals are I-false
// -------------------------------------------------------------------------
#[test]
fn selected_literal_must_be_i_false_under_i_negative() {
    // [BP16a] Under I⁻, positive literals are I-false
    let _trail = Trail::new(InitialInterpretation::AllNegative);
    let clause = Clause::new(vec![
        Literal::pos("p", vec![Term::constant("a")]), // I-false under I⁻
        Literal::neg("q", vec![Term::constant("b")]), // I-true under I⁻
    ]);
    let constrained = ConstrainedClause::new(clause.clone(), 0); // select positive
    let selected = constrained.selected_literal();
    assert!(
        selected.positive,
        "[BP16a] Selected literal under I⁻ should be positive (I-false)"
    );
}

#[test]
fn trail_len_and_is_empty_track_clause_count() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    assert_eq!(trail.len(), 0);
    assert!(trail.is_empty());
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]),
        0,
    ));
    assert_eq!(trail.len(), 1);
    assert!(!trail.is_empty());
}

#[test]
fn trail_prefix_takes_first_n_clauses() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let c1 = ConstrainedClause::new(
        Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]),
        0,
    );
    let c2 = ConstrainedClause::new(
        Clause::new(vec![Literal::pos("q", vec![Term::constant("b")])]),
        0,
    );
    trail.push(c1.clone());
    trail.push(c2.clone());

    let prefix0 = trail.prefix(0);
    assert_eq!(prefix0.len(), 0);
    assert!(matches!(
        prefix0.initial_interpretation(),
        InitialInterpretation::AllNegative
    ));

    let prefix1 = trail.prefix(1);
    assert_eq!(prefix1.len(), 1);
    assert_eq!(prefix1.clauses()[0].selected_literal(), c1.selected_literal());
}

#[test]
fn selected_literal_must_be_i_false_under_i_positive() {
    // [BP16a] Under I⁺, negative literals are I-false
    let _trail = Trail::new(InitialInterpretation::AllPositive);
    let clause = Clause::new(vec![
        Literal::pos("p", vec![Term::constant("a")]), // I-true under I⁺
        Literal::neg("q", vec![Term::constant("b")]), // I-false under I⁺
    ]);
    let constrained = ConstrainedClause::new(clause.clone(), 1); // select negative
    let selected = constrained.selected_literal();
    assert!(
        !selected.positive,
        "[BP16a] Selected literal under I⁺ should be negative (I-false)"
    );
}

#[test]
fn trail_rejects_i_true_selection_when_i_false_available() {
    // [BP16a] Def 1: if a clause has I-false literals, one of them must be selected.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let clause = Clause::new(vec![
        Literal::pos("p", vec![Term::constant("a")]), // I-false under I⁻
        Literal::neg("q", vec![Term::constant("b")]), // I-true under I⁻
    ]);
    // Select the I-true literal, which violates the SGGS clause sequence invariant.
    let constrained = ConstrainedClause::new(clause, 1);
    let err = trail
        .push_checked(constrained)
        .expect_err("expected invalid selection to be rejected");
    assert!(
        err.message.to_lowercase().contains("i-false"),
        "error should mention I-false selection requirement"
    );
}

// -------------------------------------------------------------------------
// Property: Disjoint prefix
//
// Reference: [BP16a] Definition 5 - Disjoint Prefix
// "The disjoint prefix is the maximal prefix where no two selected literals
// have unifiable atoms."
//
// Selected literals in the disjoint prefix represent distinct parts of the
// model being constructed.
// -------------------------------------------------------------------------
#[test]
fn disjoint_prefix_has_no_overlapping_selections() {
    // [BP16a] Def 8: Non-unifiable selected literals extend disjoint prefix
    let trail = Trail::new(InitialInterpretation::AllNegative);
    // p(a) and p(b) don't unify - both should be in disjoint prefix
    let c1 = Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
    let c2 = Clause::new(vec![Literal::pos("p", vec![Term::constant("b")])]);
    let cc1 = ConstrainedClause::new(c1, 0);
    let cc2 = ConstrainedClause::new(c2, 0);
    let mut trail_mut = trail;
    trail_mut.push(cc1);
    trail_mut.push(cc2);
    assert!(
        trail_mut.disjoint_prefix_length() >= 2,
        "[BP16a] Def 8: Non-unifiable selected literals extend disjoint prefix"
    );
}

#[test]
fn disjoint_prefix_stops_on_unifiable_selected_literals() {
    // [BP16a] Def 5: unifiable selected literals cannot both be in dp(Γ)
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let c1 = Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
    let c2 = Clause::new(vec![Literal::pos("p", vec![Term::var("X")])]);
    trail.push(ConstrainedClause::new(c1, 0));
    trail.push(ConstrainedClause::new(c2, 0));

    assert_eq!(
        trail.disjoint_prefix_length(),
        1,
        "Unifiable selected literals should end the disjoint prefix"
    );
}

#[test]
fn disjoint_prefix_respects_constraints() {
    // [BP16a] Def 5: disjointness is about intersection of constrained ground instances,
    // not just syntactic unifiability.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let c1 = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
        Constraint::Atomic(AtomicConstraint::RootNotEquals(
            Term::var("x"),
            "f".to_string(),
        )),
        0,
    );
    let c2 = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos(
            "P",
            vec![Term::app("f", vec![Term::var("y")])],
        )]),
        Constraint::True,
        0,
    );
    trail.push(c1);
    trail.push(c2);

    assert_eq!(
        trail.disjoint_prefix_length(),
        2,
        "Constraints can make unifiable literals disjoint"
    );
}

// -------------------------------------------------------------------------
// Property: Conflict clause definition
//
// Reference: [BW20] Definition 1: "A clause C is a conflict clause if all
// literals of C are uniformly false in the trail interpretation."
// (Uniform falsity is defined earlier in [BP16a], Section 2.)
// -------------------------------------------------------------------------
#[test]
fn conflict_clause_all_literals_false() {
    // [BW20] Def 1: Conflict = all literals uniformly false
    let trail = Trail::new(InitialInterpretation::AllNegative);
    let interp = trail.interpretation();
    // Under I⁻ with empty trail, all positive literals are uniformly false
    let conflict_candidate = Clause::new(vec![
        Literal::pos("p", vec![Term::constant("a")]),
        Literal::pos("q", vec![Term::constant("b")]),
    ]);
    let constrained = ConstrainedClause::new(conflict_candidate, 0);
    assert!(
        constrained.is_conflict(&interp),
        "[BP16a] Def 11: All-positive clause is conflict under I⁻ with empty trail"
    );
}

#[test]
fn non_conflict_has_satisfiable_literal() {
    // [BW20] Def 1: Clause with an I-true literal is not a conflict
    let trail = Trail::new(InitialInterpretation::AllNegative);
    let interp = trail.interpretation();
    // Negative literal is I-true under I⁻
    let non_conflict = Clause::new(vec![
        Literal::pos("p", vec![Term::constant("a")]), // I-false
        Literal::neg("q", vec![Term::constant("b")]), // I-true
    ]);
    let constrained = ConstrainedClause::new(non_conflict, 0);
    assert!(
        !constrained.is_conflict(&interp),
        "[BP16a] Clause with I-true literal cannot be conflict"
    );
}

#[test]
fn interpretation_uses_initial_for_unassigned_literals() {
    // [BP16a] Def 7: I[Γ] extends I for literals not defined in I^p(Γ).
    let trail_neg = Trail::new(InitialInterpretation::AllNegative);
    let interp_neg = trail_neg.interpretation();
    let pos = Literal::pos("P", vec![Term::constant("a")]);
    let neg = Literal::neg("P", vec![Term::constant("a")]);
    assert!(interp_neg.is_uniformly_false(&pos));
    assert!(interp_neg.is_uniformly_true(&neg));

    let trail_pos = Trail::new(InitialInterpretation::AllPositive);
    let interp_pos = trail_pos.interpretation();
    assert!(interp_pos.is_uniformly_true(&pos));
    assert!(interp_pos.is_uniformly_false(&neg));
}

// -------------------------------------------------------------------------
// Property: I-false selected literals are enumerated
//
// Reference: [BP17] Definition 4 (extension side premises are I-false)
// -------------------------------------------------------------------------
#[test]
fn i_false_selected_reports_only_i_false_literals() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let c1 = ConstrainedClause::new(
        Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]),
        0,
    );
    let c2 = ConstrainedClause::new(
        Clause::new(vec![Literal::neg("q", vec![Term::constant("b")])]),
        0,
    );
    trail.push(c1);
    trail.push(c2);

    let interp = trail.interpretation();
    let i_false = interp.i_false_selected();
    let indices: Vec<usize> = i_false.iter().map(|(idx, _)| *idx).collect();

    assert!(
        indices.contains(&0),
        "I-false selected literal should be reported"
    );
    assert!(
        !indices.contains(&1),
        "I-true selected literal should not be reported"
    );
}

#[test]
fn interpretation_respects_constraints_on_selected_literals() {
    // Selected P(x) with constraint x ≠ a should make P(b) true but not P(a) under I⁻.
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
    let interp = trail.interpretation();
    let p_a = Literal::pos("P", vec![Term::constant("a")]);
    let p_b = Literal::pos("P", vec![Term::constant("b")]);
    assert!(interp.is_uniformly_false(&p_a));
    assert!(interp.is_uniformly_true(&p_b));
}

#[test]
fn trail_completeness_simple_theory() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "P",
        vec![Term::constant("a")],
    )]));

    assert!(!trail.is_complete(&theory));
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));
    assert!(trail.is_complete(&theory));
}

// -------------------------------------------------------------------------
// Property: Conflict detection on the trail
//
// Reference: [BW20] Definition 1 (conflict clause)
// -------------------------------------------------------------------------
#[test]
fn find_conflict_detects_uniformly_false_clause() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]),
        0,
    ));
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::neg("p", vec![Term::constant("a")])]),
        0,
    ));

    assert_eq!(trail.find_conflict(), Some(1));
}

// -------------------------------------------------------------------------
// Property: Trail completeness
//
// Reference: [BP17] Definition 4 - extension applies only if I[Γ] \|= S
// -------------------------------------------------------------------------
#[test]
fn trail_complete_when_theory_satisfied() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )])]);

    assert!(trail.is_complete(&theory));
}

#[test]
fn trail_not_complete_when_clause_unsatisfied() {
    let trail = Trail::new(InitialInterpretation::AllNegative);
    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )])]);

    assert!(!trail.is_complete(&theory));
}

#[test]
fn trail_complete_when_satisfied_by_initial_interpretation() {
    // Under I⁻, negative literals are true, so an empty trail satisfies ¬p(a).
    let trail = Trail::new(InitialInterpretation::AllNegative);
    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::neg(
        "p",
        vec![Term::constant("a")],
    )])]);

    assert!(trail.is_complete(&theory));
}
