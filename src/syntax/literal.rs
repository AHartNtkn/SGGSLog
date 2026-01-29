//! Literals: signed atoms in first-order logic.

use std::collections::HashSet;

use super::term::{Term, Var};

/// An atom (predicate application).
///
/// In S-expression syntax: `(predicate arg1 arg2 ...)`
/// Examples:
/// - `(human socrates)` - unary predicate
/// - `(parent X Y)` - binary predicate
/// - `(empty)` or `empty` - 0-ary predicate (proposition)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Atom {
    pub predicate: String,
    pub args: Vec<Term>,
}

impl Atom {
    pub fn new(predicate: impl Into<String>, args: Vec<Term>) -> Self {
        Atom {
            predicate: predicate.into(),
            args,
        }
    }

    /// Create a 0-ary atom (proposition).
    pub fn prop(predicate: impl Into<String>) -> Self {
        Atom::new(predicate, vec![])
    }

    /// Collect all variables in this atom.
    pub fn variables(&self) -> HashSet<Var> {
        todo!("Atom::variables implementation")
    }

    /// Check if this atom is ground (contains no variables).
    pub fn is_ground(&self) -> bool {
        todo!("Atom::is_ground implementation")
    }

    /// Apply a substitution to this atom.
    pub fn apply_subst(&self, subst: &std::collections::HashMap<Var, Term>) -> Atom {
        todo!("Atom::apply_subst implementation")
    }
}

/// A literal is a signed atom.
///
/// - Positive literal: `(human socrates)` means "human(socrates) is true"
/// - Negative literal: `¬(human socrates)` means "human(socrates) is false"
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Literal {
    /// True if positive, false if negated
    pub positive: bool,
    /// The underlying atom
    pub atom: Atom,
}

impl Literal {
    /// Create a positive literal.
    pub fn positive(atom: Atom) -> Self {
        Literal {
            positive: true,
            atom,
        }
    }

    /// Create a negative literal.
    pub fn negative(atom: Atom) -> Self {
        Literal {
            positive: false,
            atom,
        }
    }

    /// Create a positive literal from predicate and args.
    pub fn pos(predicate: impl Into<String>, args: Vec<Term>) -> Self {
        Literal::positive(Atom::new(predicate, args))
    }

    /// Create a negative literal from predicate and args.
    pub fn neg(predicate: impl Into<String>, args: Vec<Term>) -> Self {
        Literal::negative(Atom::new(predicate, args))
    }

    /// Return the negation of this literal.
    pub fn negated(&self) -> Literal {
        todo!("negated implementation")
    }

    /// Check if this literal is complementary to another.
    /// Two literals are complementary if they have the same atom but opposite signs.
    pub fn is_complementary(&self, other: &Literal) -> bool {
        todo!("is_complementary implementation")
    }

    /// Collect all variables in this literal.
    pub fn variables(&self) -> HashSet<Var> {
        todo!("Literal::variables implementation")
    }

    /// Check if this literal is ground.
    pub fn is_ground(&self) -> bool {
        todo!("Literal::is_ground implementation")
    }

    /// Apply a substitution to this literal.
    pub fn apply_subst(&self, subst: &std::collections::HashMap<Var, Term>) -> Literal {
        todo!("Literal::apply_subst implementation")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // === Atom construction tests ===

    #[test]
    fn test_atom_construction() {
        let atom = Atom::new("human", vec![Term::constant("socrates")]);
        assert_eq!(atom.predicate, "human");
        assert_eq!(atom.args.len(), 1);
    }

    #[test]
    fn test_atom_prop_construction() {
        let atom = Atom::prop("raining");
        assert_eq!(atom.predicate, "raining");
        assert!(atom.args.is_empty());
    }

    // === Literal construction tests ===

    #[test]
    fn test_positive_literal_construction() {
        let lit = Literal::pos("human", vec![Term::constant("socrates")]);
        assert!(lit.positive);
        assert_eq!(lit.atom.predicate, "human");
    }

    #[test]
    fn test_negative_literal_construction() {
        let lit = Literal::neg("human", vec![Term::constant("socrates")]);
        assert!(!lit.positive);
        assert_eq!(lit.atom.predicate, "human");
    }

    // === Negation tests ===

    #[test]
    fn test_negation_flips_sign() {
        let pos = Literal::pos("p", vec![]);
        let neg = pos.negated();
        assert!(!neg.positive);
        assert_eq!(neg.atom, pos.atom);
    }

    #[test]
    fn test_double_negation_identity() {
        let lit = Literal::pos("p", vec![Term::var("X")]);
        let double_neg = lit.negated().negated();
        assert_eq!(double_neg, lit);
    }

    // === Complementary tests ===

    #[test]
    fn test_complementary_same_atom() {
        let pos = Literal::pos("p", vec![Term::var("X")]);
        let neg = Literal::neg("p", vec![Term::var("X")]);
        assert!(pos.is_complementary(&neg));
        assert!(neg.is_complementary(&pos));
    }

    #[test]
    fn test_not_complementary_different_atoms() {
        let lit1 = Literal::pos("p", vec![Term::var("X")]);
        let lit2 = Literal::neg("q", vec![Term::var("X")]);
        assert!(!lit1.is_complementary(&lit2));
    }

    #[test]
    fn test_not_complementary_same_sign() {
        let lit1 = Literal::pos("p", vec![Term::var("X")]);
        let lit2 = Literal::pos("p", vec![Term::var("X")]);
        assert!(!lit1.is_complementary(&lit2));
    }

    #[test]
    fn test_not_complementary_different_args() {
        let lit1 = Literal::pos("p", vec![Term::var("X")]);
        let lit2 = Literal::neg("p", vec![Term::var("Y")]);
        // These have the same predicate but different args, so NOT complementary
        // (Complementary requires exact atom match, not just unifiable)
        assert!(!lit1.is_complementary(&lit2));
    }

    // === Variables tests ===

    #[test]
    fn test_literal_variables() {
        let lit = Literal::pos("p", vec![Term::var("X"), Term::var("Y")]);
        let vars = lit.variables();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&Var::new("X")));
        assert!(vars.contains(&Var::new("Y")));
    }

    #[test]
    fn test_literal_ground_variables_empty() {
        let lit = Literal::pos("p", vec![Term::constant("a"), Term::constant("b")]);
        let vars = lit.variables();
        assert!(vars.is_empty());
    }

    // === Ground tests ===

    #[test]
    fn test_literal_is_ground() {
        let ground = Literal::pos("p", vec![Term::constant("a")]);
        let nonground = Literal::pos("p", vec![Term::var("X")]);
        assert!(ground.is_ground());
        assert!(!nonground.is_ground());
    }

    // === Substitution tests ===

    #[test]
    fn test_literal_subst_application() {
        let lit = Literal::pos("p", vec![Term::var("X")]);
        let mut subst = std::collections::HashMap::new();
        subst.insert(Var::new("X"), Term::constant("a"));
        let result = lit.apply_subst(&subst);
        assert_eq!(result.atom.args[0], Term::constant("a"));
        assert!(result.positive);
    }

    #[test]
    fn test_literal_subst_preserves_sign() {
        let lit = Literal::neg("p", vec![Term::var("X")]);
        let mut subst = std::collections::HashMap::new();
        subst.insert(Var::new("X"), Term::constant("a"));
        let result = lit.apply_subst(&subst);
        assert!(!result.positive);
    }
}
