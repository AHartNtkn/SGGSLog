use super::*;

// =============================================================================
// TERMINATION FOR SGGS-DECIDABLE FRAGMENTS
// =============================================================================
//
// Termination is required only for fragments with SGGS guarantees.

use crate::sggs::{derive, DerivationConfig, DerivationResult, InitialInterpretation};
use crate::syntax::{Atom, AtomCmp, AtomOrder};
use std::collections::HashSet;

fn assert_terminates(theory: &crate::theory::Theory) {
    let config = DerivationConfig {
        timeout_ms: None,
        initial_interp: InitialInterpretation::AllNegative,
    };
    let result = derive(theory, config);
    assert!(
        !matches!(result, DerivationResult::Timeout),
        "derivation should terminate for SGGS-decidable fragments"
    );
}

struct TrivialOrder;

impl AtomOrder for TrivialOrder {
    fn cmp(&self, a: &Atom, b: &Atom) -> AtomCmp {
        if a == b {
            AtomCmp::Equal
        } else {
            AtomCmp::Incomparable
        }
    }
}

#[test]
fn termination_on_epr() {
    // EPR: function-free theory.
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    assert!(theory.is_epr());
    assert_terminates(&theory);
}

#[test]
fn termination_on_bdi() {
    // BDI: no depth increase on positive literals.
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![
        Literal::neg("P", vec![Term::app("f", vec![Term::var("X")])]),
        Literal::pos("P", vec![Term::app("f", vec![Term::var("X")])]),
    ]));
    assert!(theory.is_bdi());
    assert_terminates(&theory);
}

#[test]
fn termination_on_restrained() {
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("Q", vec![Term::constant("a")]),
    ]));
    let order = TrivialOrder;
    assert!(theory.is_restrained(&order));
    assert_terminates(&theory);
}

#[test]
fn termination_on_sort_restrained() {
    // Vacuous when no infinite sorts are declared.
    let mut theory = crate::theory::Theory::new();
    let x = Term::Var(Var::new_with_sort("X", "s_fin"));
    theory.add_clause(Clause::new(vec![Literal::pos("P", vec![x])]));
    let order = TrivialOrder;
    let inf = HashSet::new();
    assert!(theory.is_sort_restrained(&inf, &order));
    assert_terminates(&theory);
}

#[test]
fn termination_on_negatively_restrained() {
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("P", vec![Term::var("X")]),
    ]));
    let order = TrivialOrder;
    assert!(theory.is_negatively_restrained(&order));
    assert_terminates(&theory);
}

#[test]
fn termination_on_sort_negatively_restrained() {
    let mut theory = crate::theory::Theory::new();
    let x = Term::Var(Var::new_with_sort("X", "s_inf"));
    theory.add_clause(Clause::new(vec![
        Literal::neg("P", vec![x.clone()]),
        Literal::pos("P", vec![x]),
    ]));
    let order = TrivialOrder;
    let mut inf = HashSet::new();
    inf.insert("s_inf".to_string());
    assert!(theory.is_sort_negatively_restrained(&inf, &order));
    assert_terminates(&theory);
}

#[test]
fn termination_on_sort_refined_pvd() {
    let mut inf = HashSet::new();
    inf.insert("s_inf".to_string());

    let x = Term::Var(Var::new_with_sort("X", "s_inf"));
    let fx = Term::app_with_sort("f", "s_inf", vec![x.clone()]);
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![
        Literal::neg("P", vec![fx]),
        Literal::pos("P", vec![x]),
    ]));

    assert!(theory.is_sort_refined_pvd(&inf));
    assert_terminates(&theory);
}

#[test]
fn termination_on_stratified_signature() {
    // Stratified signature: acyclic sort graph.
    let x = Term::Var(Var::new_with_sort("X", "s1"));
    let fx = Term::app_with_sort("f", "s2", vec![x]);
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos("P", vec![fx])]));

    assert!(theory.is_stratified());
    assert_terminates(&theory);
}
