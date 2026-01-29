//! SGGS-Splitting for clause decomposition.

use super::ConstrainedClause;

/// Result of SGGS-Splitting.
#[derive(Debug)]
pub struct SplitResult {
    /// The resulting constrained clause parts
    pub parts: Vec<ConstrainedClause>,
}

/// SGGS-Splitting: decompose clause to isolate literal intersections.
///
/// When two clauses have overlapping selected literals, splitting
/// partitions one into constrained instances to handle each case.
pub fn sggs_splitting(
    _clause: &ConstrainedClause,
    _other: &ConstrainedClause,
) -> Option<SplitResult> {
    todo!("sggs_splitting implementation")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::{AtomicConstraint, Constraint};
    use crate::sggs::ConstrainedClause;
    use crate::syntax::{Clause, Literal, Term};

    #[test]
    fn test_splitting_example_from_exposition() {
        // Source: PAAR-2014_pages_25-38.pdf (SGGS exposition),
        // "splitting of true ✄ P(x,y) by true ✄ P(f(w), g(z))".
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

        let result = sggs_splitting(&clause, &other).expect("expected splitting");
        assert_eq!(result.parts.len(), 3);

        let mut found_intersection = false;
        let mut found_top_x = false;
        let mut found_top_y = false;

        for part in result.parts {
            let lit = part.selected_literal();
            let atom = &lit.atom;
            if atom.predicate == "P"
                && atom.args
                    == vec![
                        Term::app("f", vec![Term::var("w")]),
                        Term::app("g", vec![Term::var("z")]),
                    ]
                && part.constraint == Constraint::True
            {
                found_intersection = true;
            } else if atom.predicate == "P"
                && atom.args == vec![Term::var("x"), Term::var("y")]
                && part.constraint
                    == Constraint::Atomic(AtomicConstraint::RootNotEquals(
                        Term::var("x"),
                        "f".to_string(),
                    ))
            {
                found_top_x = true;
            } else if atom.predicate == "P"
                && atom.args
                    == vec![
                        Term::app("f", vec![Term::var("x")]),
                        Term::var("y"),
                    ]
                && part.constraint
                    == Constraint::Atomic(AtomicConstraint::RootNotEquals(
                        Term::var("y"),
                        "g".to_string(),
                    ))
            {
                found_top_y = true;
            }
        }

        assert!(found_intersection);
        assert!(found_top_x);
        assert!(found_top_y);
    }
}
