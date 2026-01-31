use super::*;
use crate::sggs::{derive, DerivationConfig, DerivationResult};

// =============================================================================
// CLAUSE SEMANTIC PROPERTIES
// =============================================================================
//
// These tests verify properties of clausal representation.
//
// Reference: Standard first-order logic; Horn clause definition from
// logic programming literature.

// -------------------------------------------------------------------------
// Property: Empty clause represents contradiction
//
// Reference:  - The empty clause □ is unsatisfiable
// "Deriving the empty clause proves the original set unsatisfiable."
// -------------------------------------------------------------------------
#[test]
fn empty_clause_represents_false() {
    //  Empty clause = contradiction
    let empty = Clause::empty();
    assert!(empty.is_empty());
    let theory = theory_from_clauses(vec![empty]);
    let result = derive(&theory, DerivationConfig::default());
    assert!(
        matches!(result, DerivationResult::Unsatisfiable),
        "theory containing empty clause must be unsatisfiable"
    );
}

// -------------------------------------------------------------------------
// Property: Complementary literals
//
// Reference:  Definition for resolution
// L and ¬L are complementary if they have same atom, opposite signs.
// -------------------------------------------------------------------------
#[test]
fn clause_with_complementary_literals() {
    //  p(X) and ¬p(X) are complementary
    let lit1 = Literal::pos("p", vec![Term::var("X")]);
    let lit2 = Literal::neg("p", vec![Term::var("X")]);
    let _clause = Clause::new(vec![lit1.clone(), lit2.clone()]);
    assert!(
        lit1.is_complementary(&lit2),
        "p(X) and ¬p(X) should be complementary"
    );
}

// -------------------------------------------------------------------------
// Property: Horn clause definition
//
// Reference: Standard logic programming definition
// A Horn clause has at most one positive literal.
// -------------------------------------------------------------------------
#[test]
fn horn_clause_boundary() {
    // Exactly one positive = definite clause = Horn
    let definite = Clause::new(vec![
        Literal::neg("p", vec![]),
        Literal::neg("q", vec![]),
        Literal::pos("r", vec![]),
    ]);
    assert!(definite.is_horn(), "Definite clause (1 pos) is Horn");
    // Zero positive = goal clause = Horn
    let goal = Clause::new(vec![Literal::neg("p", vec![]), Literal::neg("q", vec![])]);
    assert!(goal.is_horn(), "Goal clause (0 pos) is Horn");
    // Two positive = not Horn
    let non_horn = Clause::new(vec![
        Literal::pos("p", vec![]),
        Literal::pos("q", vec![]),
        Literal::neg("r", vec![]),
    ]);
    assert!(!non_horn.is_horn(), "2+ positive literals is not Horn");
}

#[test]
fn variables_collects_from_all_literals() {
    let clause = Clause::new(vec![
        Literal::pos("p", vec![Term::var("X"), Term::var("Y")]),
        Literal::neg(
            "q",
            vec![Term::var("Z"), Term::app("f", vec![Term::var("W")])],
        ),
    ]);
    let vars = clause.variables();
    assert_eq!(vars.len(), 4, "Should collect X, Y, Z, W");
    assert!(vars.contains(&Var::new("X")));
    assert!(vars.contains(&Var::new("Y")));
    assert!(vars.contains(&Var::new("Z")));
    assert!(vars.contains(&Var::new("W")));
}

#[test]
fn substitution_preserves_literal_count() {
    let clause = Clause::new(vec![
        Literal::pos("p", vec![Term::var("X")]),
        Literal::pos("p", vec![Term::var("X")]),
        Literal::neg("q", vec![Term::var("Y")]),
    ]);
    let mut subst = HashMap::new();
    subst.insert(Var::new("X"), Term::constant("a"));
    subst.insert(Var::new("Y"), Term::constant("b"));
    let result = clause.apply_subst(&subst);
    assert_eq!(
        result.literals.len(),
        clause.literals.len(),
        "Substitution must preserve literal count"
    );
}

#[test]
fn substitution_preserves_signs() {
    let clause = Clause::new(vec![
        Literal::pos("p", vec![Term::var("X")]),
        Literal::neg("q", vec![Term::var("Y")]),
    ]);
    let mut subst = HashMap::new();
    subst.insert(Var::new("X"), Term::constant("a"));
    let result = clause.apply_subst(&subst);
    assert!(result.literals[0].positive, "Sign must be preserved");
    assert!(!result.literals[1].positive, "Sign must be preserved");
}

#[test]
fn substitution_applies_recursively_to_nested_terms() {
    let clause = Clause::new(vec![Literal::pos(
        "p",
        vec![Term::app("f", vec![Term::var("X")])],
    )]);
    let mut subst = HashMap::new();
    subst.insert(Var::new("X"), Term::constant("a"));
    let result = clause.apply_subst(&subst);
    assert_eq!(
        result.literals[0].atom.args[0],
        Term::app("f", vec![Term::constant("a")])
    );
}
