//! Clauses: disjunctions of literals in conjunctive normal form.

use std::collections::HashSet;

use super::literal::Literal;
use super::term::{Term, Var};

/// A clause is a disjunction of literals.
///
/// In CNF, a theory is a conjunction of clauses. Each clause represents
/// a disjunction: `L1 ∨ L2 ∨ ... ∨ Ln`.
///
/// Examples (in our syntax):
/// - Unit clause: `(human socrates)`
/// - Binary: `¬(human X) ∨ (mortal X)`
/// - Ternary: `(p X) ∨ (q X) ∨ (r X)`
/// - Empty clause: `⊥` (contradiction)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    pub literals: Vec<Literal>,
}

impl Clause {
    /// Create a clause from a vector of literals.
    pub fn new(literals: Vec<Literal>) -> Self {
        Clause { literals }
    }

    /// Create the empty clause (represents contradiction/false).
    pub fn empty() -> Self {
        todo!("empty implementation")
    }

    /// Check if this is the empty clause.
    pub fn is_empty(&self) -> bool {
        todo!("is_empty implementation")
    }

    /// Check if this is a unit clause (exactly one literal).
    pub fn is_unit(&self) -> bool {
        todo!("is_unit implementation")
    }

    /// Check if this is a Horn clause (at most one positive literal).
    pub fn is_horn(&self) -> bool {
        todo!("is_horn implementation")
    }

    /// Collect all variables in this clause.
    pub fn variables(&self) -> HashSet<Var> {
        todo!("Clause::variables implementation")
    }

    /// Check if this clause is ground (contains no variables).
    pub fn is_ground(&self) -> bool {
        todo!("Clause::is_ground implementation")
    }

    /// Apply a substitution to this clause.
    pub fn apply_subst(&self, subst: &std::collections::HashMap<Var, Term>) -> Clause {
        todo!("Clause::apply_subst implementation")
    }

    /// Get all positive literals in this clause.
    pub fn positive_literals(&self) -> Vec<&Literal> {
        todo!("positive_literals implementation")
    }

    /// Get all negative literals in this clause.
    pub fn negative_literals(&self) -> Vec<&Literal> {
        todo!("negative_literals implementation")
    }

    /// Get the number of literals in this clause.
    pub fn len(&self) -> usize {
        self.literals.len()
    }

    /// Check if this clause is positively ground-preserving (BW20 Def. 4).
    pub fn is_positively_ground_preserving(&self) -> bool {
        todo!("Clause::is_positively_ground_preserving implementation")
    }

    /// Check if this clause is negatively ground-preserving (BW20 Def. 4).
    pub fn is_negatively_ground_preserving(&self) -> bool {
        todo!("Clause::is_negatively_ground_preserving implementation")
    }

    /// Check if this clause is ground-preserving (positively or negatively).
    pub fn is_ground_preserving(&self) -> bool {
        todo!("Clause::is_ground_preserving implementation")
    }

    /// Check if this clause is restrained (BW20 Def. 6).
    pub fn is_restrained(&self) -> bool {
        todo!("Clause::is_restrained implementation")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::term::Term;

    // === Construction tests ===

    #[test]
    fn test_clause_construction() {
        let lit1 = Literal::pos("p", vec![]);
        let lit2 = Literal::neg("q", vec![]);
        let clause = Clause::new(vec![lit1, lit2]);
        assert_eq!(clause.literals.len(), 2);
    }

    // === Empty clause tests ===

    #[test]
    fn test_empty_clause() {
        let empty = Clause::empty();
        assert!(empty.is_empty());
        assert_eq!(empty.literals.len(), 0);
    }

    #[test]
    fn test_non_empty_clause_not_empty() {
        let clause = Clause::new(vec![Literal::pos("p", vec![])]);
        assert!(!clause.is_empty());
    }

    // === Unit clause tests ===

    #[test]
    fn test_unit_clause() {
        let clause = Clause::new(vec![Literal::pos("p", vec![])]);
        assert!(clause.is_unit());
    }

    #[test]
    fn test_empty_clause_not_unit() {
        let clause = Clause::empty();
        assert!(!clause.is_unit());
    }

    #[test]
    fn test_binary_clause_not_unit() {
        let clause = Clause::new(vec![
            Literal::pos("p", vec![]),
            Literal::neg("q", vec![]),
        ]);
        assert!(!clause.is_unit());
    }

    // === Horn clause tests ===

    #[test]
    fn test_horn_clause_one_positive() {
        // ¬p ∨ ¬q ∨ r (one positive literal)
        let clause = Clause::new(vec![
            Literal::neg("p", vec![]),
            Literal::neg("q", vec![]),
            Literal::pos("r", vec![]),
        ]);
        assert!(clause.is_horn());
    }

    #[test]
    fn test_horn_clause_zero_positive() {
        // ¬p ∨ ¬q (goal clause, zero positive)
        let clause = Clause::new(vec![
            Literal::neg("p", vec![]),
            Literal::neg("q", vec![]),
        ]);
        assert!(clause.is_horn());
    }

    #[test]
    fn test_non_horn_multiple_positive() {
        // p ∨ q (two positive literals)
        let clause = Clause::new(vec![
            Literal::pos("p", vec![]),
            Literal::pos("q", vec![]),
        ]);
        assert!(!clause.is_horn());
    }

    #[test]
    fn test_empty_clause_is_horn() {
        let clause = Clause::empty();
        assert!(clause.is_horn()); // 0 positive literals, so Horn
    }

    // === Variables tests ===

    #[test]
    fn test_clause_variables() {
        let clause = Clause::new(vec![
            Literal::pos("p", vec![Term::var("X")]),
            Literal::neg("q", vec![Term::var("Y")]),
        ]);
        let vars = clause.variables();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&Var::new("X")));
        assert!(vars.contains(&Var::new("Y")));
    }

    #[test]
    fn test_clause_shared_variables() {
        // Variables appearing in multiple literals counted once
        let clause = Clause::new(vec![
            Literal::pos("p", vec![Term::var("X")]),
            Literal::neg("q", vec![Term::var("X")]),
        ]);
        let vars = clause.variables();
        assert_eq!(vars.len(), 1);
    }

    // === Ground tests ===

    #[test]
    fn test_clause_is_ground() {
        let ground = Clause::new(vec![
            Literal::pos("p", vec![Term::constant("a")]),
        ]);
        assert!(ground.is_ground());
    }

    #[test]
    fn test_clause_not_ground() {
        let nonground = Clause::new(vec![
            Literal::pos("p", vec![Term::var("X")]),
        ]);
        assert!(!nonground.is_ground());
    }

    #[test]
    fn test_empty_clause_is_ground() {
        let empty = Clause::empty();
        assert!(empty.is_ground());
    }

    // === Substitution tests ===

    #[test]
    fn test_clause_subst_application() {
        let clause = Clause::new(vec![
            Literal::pos("p", vec![Term::var("X")]),
            Literal::neg("q", vec![Term::var("Y")]),
        ]);
        let mut subst = std::collections::HashMap::new();
        subst.insert(Var::new("X"), Term::constant("a"));
        subst.insert(Var::new("Y"), Term::constant("b"));

        let result = clause.apply_subst(&subst);
        assert_eq!(result.literals.len(), 2);
        assert_eq!(result.literals[0].atom.args[0], Term::constant("a"));
        assert_eq!(result.literals[1].atom.args[0], Term::constant("b"));
    }

    // === Positive/Negative literals extraction ===

    #[test]
    fn test_positive_literals_extraction() {
        let clause = Clause::new(vec![
            Literal::pos("p", vec![]),
            Literal::neg("q", vec![]),
            Literal::pos("r", vec![]),
        ]);
        let positive = clause.positive_literals();
        assert_eq!(positive.len(), 2);
        assert!(positive.iter().all(|l| l.positive));
    }

    #[test]
    fn test_negative_literals_extraction() {
        let clause = Clause::new(vec![
            Literal::pos("p", vec![]),
            Literal::neg("q", vec![]),
            Literal::neg("r", vec![]),
        ]);
        let negative = clause.negative_literals();
        assert_eq!(negative.len(), 2);
        assert!(negative.iter().all(|l| !l.positive));
    }

    #[test]
    fn test_positive_literals_empty_when_none() {
        let clause = Clause::new(vec![
            Literal::neg("p", vec![]),
            Literal::neg("q", vec![]),
        ]);
        let positive = clause.positive_literals();
        assert!(positive.is_empty());
    }
}
