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
    // Default: split using the selected literal of `other`.
    sggs_splitting_on(_clause, _other, _other.selected)
}

/// SGGS-Splitting by a specific literal of the other clause.
///
/// This allows splitting on a non-selected literal, which is permitted by SGGS
/// to expose intersections and enable deletion (Bonacina 2016, Sect. 4.2).
pub fn sggs_splitting_on(
    _clause: &ConstrainedClause,
    _other: &ConstrainedClause,
    _other_lit_idx: usize,
) -> Option<SplitResult> {
    todo!("sggs_splitting_on implementation")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::{AtomicConstraint, Constraint};
    use crate::sggs::ConstrainedClause;
    use crate::syntax::{Clause, Literal, Term};
    use crate::unify::unify_literals;

    fn intersects(a: &ConstrainedClause, b: &ConstrainedClause) -> bool {
        match unify_literals(a.selected_literal(), b.selected_literal()) {
            crate::unify::UnifyResult::Success(sigma) => {
                let mut combined = Constraint::True;
                for v in sigma.domain() {
                    if let Some(t) = sigma.lookup(v) {
                        combined = combined.and(Constraint::Atomic(AtomicConstraint::Identical(
                            Term::Var(v.clone()),
                            t.clone(),
                        )));
                    }
                }
                combined
                    .and(a.constraint.clone())
                    .and(b.constraint.clone())
                    .is_satisfiable()
            }
            crate::unify::UnifyResult::Failure(_) => false,
        }
    }

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
        assert!(
            result.parts.len() >= 2,
            "splitting should produce a non-trivial partition"
        );

        // Exactly one part should intersect the other clause.
        let intersection_count = result
            .parts
            .iter()
            .filter(|p| intersects(p, &other))
            .count();
        assert_eq!(
            intersection_count, 1,
            "split should isolate exactly one intersection representative"
        );

        // All parts should be satisfiable.
        for part in &result.parts {
            assert!(part.constraint.is_satisfiable());
        }
    }

    #[test]
    fn test_splitting_on_non_selected_literal() {
        // SGGS allows splitting on a non-selected literal to expose intersections.
        // Source: bonacina2016.pdf, discussion before Definition 24 (s-splitting on non-selected literal).
        let clause = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos(
                "P",
                vec![Term::var("x"), Term::var("y")],
            )]),
            Constraint::True,
            0,
        );
        let other = ConstrainedClause::with_constraint(
            Clause::new(vec![
                Literal::pos("Q", vec![Term::var("u")]), // selected (index 0)
                Literal::pos(
                    "P",
                    vec![
                        Term::app("f", vec![Term::var("w")]),
                        Term::app("g", vec![Term::var("z")]),
                    ],
                ),
            ]),
            Constraint::True,
            0,
        );

        let result = sggs_splitting_on(&clause, &other, 1).expect("expected split on non-selected");
        assert!(
            result.parts.len() >= 2,
            "splitting on non-selected literal should be non-trivial"
        );
    }
}
