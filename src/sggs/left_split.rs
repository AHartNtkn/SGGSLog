//! SGGS Left-Splitting (l-split) for conflict solving.

use super::{ConstrainedClause, SplitResult};

/// SGGS left-splitting: split a clause using a conflicting clause to isolate intersections.
///
/// Returns a partition of the split clause if left-splitting applies.
pub fn sggs_left_split(
    _clause: &ConstrainedClause,
    _other: &ConstrainedClause,
) -> Option<SplitResult> {
    todo!("sggs_left_split implementation")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::{AtomicConstraint, Constraint};
    use crate::syntax::{Clause, Literal, Term};

    #[test]
    fn test_left_split_intersection() {
        // Source: SGGSdpFOL, rule l-split (Fig. 2).
        let clause = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos(
                "P",
                vec![Term::var("x"), Term::var("y")],
            )]),
            Constraint::True,
            0,
        );
        let other = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos(
                "P",
                vec![
                    Term::app("f", vec![Term::var("w")]),
                    Term::app("g", vec![Term::var("z")]),
                ],
            )]),
            Constraint::True,
            0,
        );

        let result = sggs_left_split(&clause, &other).expect("expected left split");
        assert!(
            result.parts.len() >= 2,
            "left split should produce a non-trivial partition"
        );
    }

    #[test]
    fn test_left_split_no_intersection() {
        let clause = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
            Constraint::True,
            0,
        );
        let other = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("Q", vec![Term::var("y")])]),
            Constraint::True,
            0,
        );

        assert!(sggs_left_split(&clause, &other).is_none());
    }

    #[test]
    fn test_left_split_defers_when_factoring_applicable() {
        // Source: SGGSdpFOL, Fig. 2 (l-split applies only if condition (†) does not hold).
        // If the other clause has a same-sign literal unifying with its selected literal,
        // factoring should be preferred, so left-split should not apply.
        let clause = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
            Constraint::True,
            0,
        );
        let other = ConstrainedClause::with_constraint(
            Clause::new(vec![
                Literal::pos("P", vec![Term::var("y")]), // selected
                Literal::pos("P", vec![Term::constant("a")]),
            ]),
            Constraint::True,
            0,
        );

        assert!(sggs_left_split(&clause, &other).is_none());
    }

    #[test]
    fn test_left_split_propagates_constraints() {
        let clause = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
            Constraint::True,
            0,
        );
        let other = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
            Constraint::True,
            0,
        );

        let result = sggs_left_split(&clause, &other).expect("expected left split");
        let x_eq_a = Constraint::Atomic(AtomicConstraint::Identical(
            Term::var("x"),
            Term::constant("a"),
        ));

        let mut intersects = 0;
        let mut disjoint = 0;
        for part in &result.parts {
            if part.constraint.clone().and(x_eq_a.clone()).is_satisfiable() {
                intersects += 1;
            } else {
                disjoint += 1;
            }
        }
        assert_eq!(intersects, 1, "exactly one split part should allow x = a");
        assert!(
            disjoint >= 1,
            "at least one split part should exclude x = a"
        );
    }
}
