use super::*;

// =============================================================================
// FRAGMENT DETECTION (DECIDABLE FRAGMENTS)
// =============================================================================
//
// Reference: [BW20] Definitions 3 and 5 (ground-preserving, restrained)

#[test]
fn ground_preserving_check() {
    // Datalog-style clause: Var(C+) ⊆ Var(C-)
    let clause = Clause::new(vec![
        Literal::neg("edge", vec![Term::var("X"), Term::var("Z")]),
        Literal::neg("path", vec![Term::var("Z"), Term::var("Y")]),
        Literal::pos("path", vec![Term::var("X"), Term::var("Y")]),
    ]);
    assert!(clause.is_positively_ground_preserving());
}

#[test]
fn ground_preserving_negative_variant() {
    // Negatively ground-preserving: Var(C) ⊆ Var(C+)
    let clause = Clause::new(vec![
        Literal::neg("q", vec![Term::var("X")]),
        Literal::pos("p", vec![Term::var("X"), Term::var("Y")]),
    ]);
    assert!(clause.is_negatively_ground_preserving());
    assert!(!clause.is_positively_ground_preserving());
    assert!(clause.is_ground_preserving());
}

#[test]
fn restrained_vacuous_for_ground_positive() {
    // No non-ground positive literals => restrained condition is vacuous.
    let clause = Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("Q", vec![Term::constant("a")]),
    ]);
    assert!(clause.is_restrained());
}

#[test]
fn restrained_requires_ground_preserving() {
    // [BW20] Def 5: restrained implies ground-preserving.
    let clause = Clause::new(vec![
        Literal::neg("Q", vec![Term::constant("a")]),
        Literal::pos("P", vec![Term::var("X")]),
    ]);
    assert!(!clause.is_positively_ground_preserving());
    assert!(!clause.is_restrained());
}
