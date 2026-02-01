//! Atomic constraints used in SGGS.

use crate::syntax::Term;
use crate::unify::Substitution;

/// Atomic constraint types used in SGGS.
///
/// These are the basic building blocks for constraints on clause instances.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AtomicConstraint {
    /// t ≐ u: syntactic identity (terms must be identical after substitution)
    Identical(Term, Term),
    /// t ≁ u: non-identity (terms must differ after substitution)
    NotIdentical(Term, Term),
    /// root(t) = f: the top symbol of t must be f
    RootEquals(Term, String),
    /// root(t) ≠ f: the top symbol of t must not be f
    RootNotEquals(Term, String),
}

impl AtomicConstraint {
    /// Evaluate this constraint under a substitution.
    /// Returns Some(true) if satisfied, Some(false) if violated,
    /// None if it cannot be determined (contains unbound variables).
    pub fn evaluate(&self, subst: &Substitution) -> Option<bool> {
        match self {
            AtomicConstraint::Identical(t1, t2) => {
                let t1_applied = subst.apply_to_term(t1);
                let t2_applied = subst.apply_to_term(t2);
                // If either term still has variables, result is unknown
                if !t1_applied.is_ground() || !t2_applied.is_ground() {
                    None
                } else {
                    Some(t1_applied == t2_applied)
                }
            }
            AtomicConstraint::NotIdentical(t1, t2) => {
                let t1_applied = subst.apply_to_term(t1);
                let t2_applied = subst.apply_to_term(t2);
                // If either term still has variables, result is unknown
                if !t1_applied.is_ground() || !t2_applied.is_ground() {
                    None
                } else {
                    Some(t1_applied != t2_applied)
                }
            }
            AtomicConstraint::RootEquals(t, symbol) => {
                let t_applied = subst.apply_to_term(t);
                t_applied.root_symbol().map(|root| root == symbol)
            }
            AtomicConstraint::RootNotEquals(t, symbol) => {
                let t_applied = subst.apply_to_term(t);
                t_applied.root_symbol().map(|root| root != symbol)
            }
        }
    }

    /// Return the negation of this constraint.
    pub fn negate(&self) -> AtomicConstraint {
        match self {
            AtomicConstraint::Identical(t1, t2) => {
                AtomicConstraint::NotIdentical(t1.clone(), t2.clone())
            }
            AtomicConstraint::NotIdentical(t1, t2) => {
                AtomicConstraint::Identical(t1.clone(), t2.clone())
            }
            AtomicConstraint::RootEquals(t, s) => {
                AtomicConstraint::RootNotEquals(t.clone(), s.clone())
            }
            AtomicConstraint::RootNotEquals(t, s) => {
                AtomicConstraint::RootEquals(t.clone(), s.clone())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::Term;
    use crate::unify::Substitution;

    #[test]
    fn test_evaluate_identical_ground() {
        // Source: Semantically_Guided_Goal_Sensitive_Reaso.pdf, Definition 1 (Constraint)
        let c = AtomicConstraint::Identical(Term::constant("a"), Term::constant("a"));
        let subst = Substitution::empty();
        assert_eq!(c.evaluate(&subst), Some(true));
    }

    #[test]
    fn test_evaluate_identical_distinct_ground() {
        // Source: Semantically_Guided_Goal_Sensitive_Reaso.pdf, Definition 1
        let c = AtomicConstraint::Identical(Term::constant("a"), Term::constant("b"));
        let subst = Substitution::empty();
        assert_eq!(c.evaluate(&subst), Some(false));
    }

    #[test]
    fn test_evaluate_unbound_is_unknown() {
        // Source: Semantically_Guided_Goal_Sensitive_Reaso.pdf, Definition 1
        let c = AtomicConstraint::Identical(Term::var("X"), Term::constant("a"));
        let subst = Substitution::empty();
        assert_eq!(c.evaluate(&subst), None);
    }

    #[test]
    fn test_evaluate_root_equals() {
        // Source: Semantically_Guided_Goal_Sensitive_Reaso.pdf, Definition 1
        let c = AtomicConstraint::RootEquals(
            Term::app("f", vec![Term::constant("a")]),
            "f".to_string(),
        );
        let subst = Substitution::empty();
        assert_eq!(c.evaluate(&subst), Some(true));
    }

    #[test]
    fn test_negate_swaps_constraint() {
        // Source: Semantically_Guided_Goal_Sensitive_Reaso.pdf, Definition 1
        let c = AtomicConstraint::Identical(Term::var("X"), Term::var("Y"));
        assert!(matches!(c.negate(), AtomicConstraint::NotIdentical(_, _)));
        let c = AtomicConstraint::RootEquals(Term::var("X"), "f".to_string());
        assert!(matches!(c.negate(), AtomicConstraint::RootNotEquals(_, _)));
    }
}
