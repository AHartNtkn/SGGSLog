//! SGGS-Deletion for removing disposable clauses.

use super::{ConstrainedClause, Trail};

/// SGGS-Deletion: remove disposable clauses from trail.
///
/// A clause is disposable if all its atoms are satisfied by the
/// trail interpretation and removing it doesn't affect the model.
pub fn sggs_deletion(_trail: &mut Trail) {
    todo!("sggs_deletion implementation")
}

/// Check if a clause is disposable.
pub fn is_disposable(_clause: &ConstrainedClause, _trail: &Trail) -> bool {
    todo!("is_disposable implementation")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::Constraint;
    use crate::sggs::ConstrainedClause;
    use crate::syntax::{Clause, Literal, Term};

    fn unit(lit: Literal) -> ConstrainedClause {
        ConstrainedClause::with_constraint(Clause::new(vec![lit]), Constraint::True, 0)
    }

    #[test]
    fn test_disposable_example_2_simple_sequences() {
        // Source: bonacina2016.pdf, Example 2 (disposable clauses in unit sequences).
        // Gamma = P(x), not Q(x), P(x): the second P(x) is disposable.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
        trail.push(unit(Literal::neg("Q", vec![Term::var("x")])));
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));

        let clause = &trail.clauses()[2];
        assert!(is_disposable(clause, &trail));
    }

    #[test]
    fn test_not_disposable_example_2_negative_prefix() {
        // Source: bonacina2016.pdf, Example 2.
        // Gamma = not P(x), not Q(x), P(x): P(x) is not disposable.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::neg("P", vec![Term::var("x")])));
        trail.push(unit(Literal::neg("Q", vec![Term::var("x")])));
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));

        let clause = &trail.clauses()[2];
        assert!(!is_disposable(clause, &trail));
    }

    #[test]
    fn test_not_disposable_example_2_duplicate_negative() {
        // Source: bonacina2016.pdf, Example 2.
        // Gamma = P(x), not P(x), not P(x): neither occurrence of not P(x) is disposable.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
        trail.push(unit(Literal::neg("P", vec![Term::var("x")])));
        trail.push(unit(Literal::neg("P", vec![Term::var("x")])));

        let clause1 = &trail.clauses()[1];
        let clause2 = &trail.clauses()[2];
        assert!(!is_disposable(clause1, &trail));
        assert!(!is_disposable(clause2, &trail));
    }

    #[test]
    fn test_disposable_example_2_signature_a_f() {
        // Source: bonacina2016.pdf, Example 2 (signature with one constant a and one function f).
        // In P(a), P(f(x)), P(z), the last P(z) is disposable.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));
        trail.push(unit(Literal::pos("P", vec![Term::app("f", vec![Term::var("x")])])));
        trail.push(unit(Literal::pos("P", vec![Term::var("z")])));

        let clause = &trail.clauses()[2];
        assert!(is_disposable(clause, &trail));
    }

    #[test]
    fn test_disposable_example_2_signature_a_f_reverse() {
        // Source: bonacina2016.pdf, Example 2.
        // In P(z), P(a), P(f(x)), then P(a) and P(f(x)) are disposable.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::var("z")])));
        trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));
        trail.push(unit(Literal::pos("P", vec![Term::app("f", vec![Term::var("x")])])));

        let clause1 = &trail.clauses()[1];
        let clause2 = &trail.clauses()[2];
        assert!(is_disposable(clause1, &trail));
        assert!(is_disposable(clause2, &trail));
    }

    #[test]
    fn test_sggs_deletion_removes_disposable_clause() {
        // Source: bonacina2016.pdf, Example 2 (SGGS-deletion removes disposable clauses).
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
        trail.push(unit(Literal::neg("Q", vec![Term::var("x")])));
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));

        sggs_deletion(&mut trail);

        assert_eq!(trail.clauses().len(), 2);
        let count_p = trail
            .clauses()
            .iter()
            .filter(|c| c.selected_literal() == &Literal::pos("P", vec![Term::var("x")]))
            .count();
        let count_not_q = trail
            .clauses()
            .iter()
            .filter(|c| c.selected_literal() == &Literal::neg("Q", vec![Term::var("x")]))
            .count();
        assert_eq!(count_p, 1);
        assert_eq!(count_not_q, 1);
    }

    #[test]
    fn test_single_clause_not_disposable() {
        // By Def. 6, no clause in the disjoint prefix is disposable.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
        let clause = &trail.clauses()[0];
        assert!(!is_disposable(clause, &trail));
    }

    #[test]
    fn test_deletion_removes_unsatisfiable_constraint_clause() {
        // A clause with no constrained ground instances is disposable.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
            Constraint::False,
            0,
        ));

        sggs_deletion(&mut trail);
        assert!(trail.clauses().is_empty());
    }
}
