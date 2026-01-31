use super::*;

// =============================================================================
// SGGS COMPLETENESS PROPERTIES
// =============================================================================
//
// Reference: [BP17] Theorem 1 - Refutational Completeness
// "SGGS is refutationally complete: for unsatisfiable input, any fair SGGS
// derivation derives the empty clause."
//
// Reference: [BP17] Theorem 2 - Model Completeness in the Limit
// "SGGS is model complete in the limit: for satisfiable input, any fair SGGS
// derivation constructs a model in the limit."
//
// Reference: [BP17] - Proof Confluence
// "SGGS is proof confluent: it never needs to backtrack."
//
// [BW20] Theorems 1-5 extend these results to decidable fragments.
use crate::sggs::{derive, DerivationConfig, DerivationResult, InitialInterpretation};

fn model_satisfies_ground_clause(model: &crate::sggs::Model, clause: &Clause) -> bool {
    clause.literals.iter().any(|lit| {
        let atom = lit.atom.clone();
        let holds = model.true_atoms.contains(&atom);
        if lit.positive {
            holds
        } else {
            !holds
        }
    })
}

// -------------------------------------------------------------------------
// Property: Unsatisfiable theories derive empty clause
//
// Reference: [BP17] Theorem 1 - Refutational Completeness
// -------------------------------------------------------------------------
#[test]
fn unsatisfiable_derives_empty() {
    // [BP17] Theorem 1: p ∧ ¬p is unsatisfiable → derives □
    let theory = theory_from_clauses(vec![
        Clause::new(vec![Literal::pos("p", vec![])]),
        Clause::new(vec![Literal::neg("p", vec![])]),
    ]);
    let config = DerivationConfig::default();
    let result = derive(&theory, config);
    assert!(
        matches!(result, DerivationResult::Unsatisfiable),
        "[BP17] Theorem 1: p ∧ ¬p must derive empty clause"
    );
}

#[test]
fn harder_unsatisfiable() {
    // [BP17] Theorem 1: (p∨q) ∧ (¬p∨q) ∧ (p∨¬q) ∧ (¬p∨¬q) is unsatisfiable
    let theory = theory_from_clauses(vec![
        Clause::new(vec![Literal::pos("p", vec![]), Literal::pos("q", vec![])]),
        Clause::new(vec![Literal::neg("p", vec![]), Literal::pos("q", vec![])]),
        Clause::new(vec![Literal::pos("p", vec![]), Literal::neg("q", vec![])]),
        Clause::new(vec![Literal::neg("p", vec![]), Literal::neg("q", vec![])]),
    ]);
    let config = DerivationConfig::default();
    let result = derive(&theory, config);
    assert!(
        matches!(result, DerivationResult::Unsatisfiable),
        "[BP17] Theorem 1: All-cases covered contradiction must be unsatisfiable"
    );
}

// -------------------------------------------------------------------------
// Property: Satisfiable theories produce models
//
// Reference: [BP17] Theorem 2 - Model Completeness in the Limit
// -------------------------------------------------------------------------
#[test]
fn satisfiable_produces_model() {
    // [BP17] Theorem 2: Satisfiable input produces a model
    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("p", vec![])])]);
    let config = DerivationConfig::default();
    let result = derive(&theory, config);
    match result {
        DerivationResult::Satisfiable(model) => {
            assert!(
                model.true_atoms.contains(&Atom::prop("p")),
                "[BP17] Theorem 2: Model for {{p}} must include p"
            );
        }
        _ => panic!("[BP17] Theorem 2: Single fact p should be satisfiable"),
    }
}

#[test]
fn model_satisfies_all_ground_clauses() {
    let theory = theory_from_clauses(vec![
        Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]),
        Clause::new(vec![
            Literal::neg("p", vec![Term::constant("a")]),
            Literal::pos("q", vec![Term::constant("b")]),
        ]),
    ]);
    let config = DerivationConfig::default();
    let result = derive(&theory, config);
    match result {
        DerivationResult::Satisfiable(model) => {
            for clause in theory.clauses() {
                assert!(
                    model_satisfies_ground_clause(&model, clause),
                    "model should satisfy ground clause {:?}",
                    clause
                );
            }
        }
        _ => panic!("expected satisfiable model for ground theory"),
    }
}

#[test]
fn satisfiable_horn_produces_model() {
    // [BP17] Theorem 2: Horn theory produces minimal Herbrand model
    // p(a), ¬p(X) ∨ q(X), ¬q(X) ∨ r(X) → model contains {p(a), q(a), r(a)}
    let theory = theory_from_clauses(vec![
        Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]),
        Clause::new(vec![
            Literal::neg("p", vec![Term::var("X")]),
            Literal::pos("q", vec![Term::var("X")]),
        ]),
        Clause::new(vec![
            Literal::neg("q", vec![Term::var("X")]),
            Literal::pos("r", vec![Term::var("X")]),
        ]),
    ]);
    let config = DerivationConfig::default();
    let result = derive(&theory, config);
    match result {
        DerivationResult::Satisfiable(model) => {
            assert!(
                model
                    .true_atoms
                    .contains(&Atom::new("p", vec![Term::constant("a")])),
                "[BP17] Theorem 2: Model should contain p(a)"
            );
        }
        _ => panic!("[BP17] Theorem 2: Horn theory is satisfiable"),
    }
}

// -------------------------------------------------------------------------
// Property: Proof confluence
//
// Reference: [BP17] Section 5 - Proof Confluence
// "SGGS is proof confluent: different search orders reach the same result."
// -------------------------------------------------------------------------
#[test]
fn proof_confluence_unsatisfiable() {
    // [BP17] Proof confluence: same result regardless of initial interpretation
    let theory = theory_from_clauses(vec![
        Clause::new(vec![Literal::pos("p", vec![])]),
        Clause::new(vec![Literal::neg("p", vec![])]),
    ]);
    let config_positive = DerivationConfig {
        timeout_ms: Some(1000),
        initial_interp: InitialInterpretation::AllPositive,
    };
    let config_negative = DerivationConfig {
        timeout_ms: Some(1000),
        initial_interp: InitialInterpretation::AllNegative,
    };
    let result_pos = derive(&theory, config_positive);
    let result_neg = derive(&theory, config_negative);
    assert!(
        matches!(result_pos, DerivationResult::Unsatisfiable),
        "[BP17] Proof confluence: Unsatisfiable with I⁺"
    );
    assert!(
        matches!(result_neg, DerivationResult::Unsatisfiable),
        "[BP17] Proof confluence: Unsatisfiable with I⁻"
    );
}

// -------------------------------------------------------------------------
// Property: Decidable fragments terminate
//
// Reference: [BW20] Theorem 2 - Stratified Fragment
// "Any fair SGGS-derivation from a stratified clause set halts."
//
// Datalog is a subset of the stratified fragment.
// -------------------------------------------------------------------------
#[test]
fn satisfiable_datalog() {
    // [BW20] Theorem 2: Datalog (stratified) terminates and produces model
    // edge(a,b), edge(b,c), path rules → derives path(a,c)
    let a = Term::constant("a");
    let b = Term::constant("b");
    let c = Term::constant("c");
    let theory = theory_from_clauses(vec![
        Clause::new(vec![Literal::pos("edge", vec![a.clone(), b.clone()])]),
        Clause::new(vec![Literal::pos("edge", vec![b.clone(), c.clone()])]),
        Clause::new(vec![
            Literal::neg("edge", vec![Term::var("X"), Term::var("Y")]),
            Literal::pos("path", vec![Term::var("X"), Term::var("Y")]),
        ]),
        Clause::new(vec![
            Literal::neg("path", vec![Term::var("X"), Term::var("Y")]),
            Literal::neg("edge", vec![Term::var("Y"), Term::var("Z")]),
            Literal::pos("path", vec![Term::var("X"), Term::var("Z")]),
        ]),
    ]);
    let config = DerivationConfig::default();
    let result = derive(&theory, config);
    match result {
        DerivationResult::Satisfiable(model) => {
            assert!(
                model
                    .true_atoms
                    .contains(&Atom::new("path", vec![a.clone(), c.clone()])),
                "[BW20] Theorem 2: Model should contain path(a,c) by transitivity"
            );
        }
        DerivationResult::Timeout => {
            panic!("[BW20] Stratified/Datalog should terminate without timeout");
        }
        DerivationResult::Unsatisfiable => {
            panic!("[BW20] Datalog program should be satisfiable");
        }
    }
}
