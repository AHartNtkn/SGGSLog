//! Compound constraints for SGGS.

use super::AtomicConstraint;

/// A constraint is a boolean combination of atomic constraints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constraint {
    /// Always true
    True,
    /// Always false
    False,
    /// An atomic constraint
    Atomic(AtomicConstraint),
    /// Conjunction
    And(Box<Constraint>, Box<Constraint>),
    /// Disjunction
    Or(Box<Constraint>, Box<Constraint>),
    /// Negation
    Not(Box<Constraint>),
}

impl Constraint {
    /// Conjoin two constraints.
    pub fn and(self, other: Constraint) -> Constraint {
        todo!("Constraint::and implementation")
    }

    /// Disjoin two constraints.
    pub fn or(self, other: Constraint) -> Constraint {
        todo!("Constraint::or implementation")
    }

    /// Negate this constraint.
    pub fn not(self) -> Constraint {
        todo!("Constraint::not implementation")
    }

    /// Simplify this constraint.
    pub fn simplify(&self) -> Constraint {
        todo!("Constraint::simplify implementation")
    }

    /// Check if this constraint is satisfiable.
    pub fn is_satisfiable(&self) -> bool {
        todo!("Constraint::is_satisfiable implementation")
    }

    /// Convert to standard form.
    pub fn standardize(&self) -> Constraint {
        todo!("Constraint::standardize implementation")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::AtomicConstraint;
    use crate::syntax::Term;

    #[test]
    fn test_standardize_keeps_standard_form() {
        // Source: Semantically_Guided_Goal_Sensitive_Reaso.pdf, Definition 1 (standard form).
        let c1 = Constraint::Atomic(AtomicConstraint::NotIdentical(
            Term::var("X"),
            Term::var("Y"),
        ));
        let c2 = Constraint::Atomic(AtomicConstraint::RootNotEquals(
            Term::var("X"),
            "f".to_string(),
        ));
        let standard = Constraint::And(Box::new(c1), Box::new(c2));
        assert_eq!(standard.standardize(), standard);
    }

    #[test]
    fn test_simplify_boolean_identities() {
        let c = Constraint::Atomic(AtomicConstraint::NotIdentical(
            Term::var("X"),
            Term::var("Y"),
        ));
        assert_eq!(Constraint::True.and(c.clone()).simplify(), c);
        assert_eq!(Constraint::False.and(c.clone()).simplify(), Constraint::False);
        assert_eq!(Constraint::True.or(c.clone()).simplify(), Constraint::True);
        assert_eq!(Constraint::False.or(c.clone()).simplify(), c);
        assert_eq!(Constraint::True.not().simplify(), Constraint::False);
        assert_eq!(Constraint::False.not().simplify(), Constraint::True);
    }
}
