//! SGGS-Splitting for clause decomposition.

use super::split_common::build_complement_constraint;
use super::ConstrainedClause;
use crate::constraint::{AtomicConstraint, Constraint};
use crate::syntax::Term;
use crate::unify::{unify_literals, UnifyResult};

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
    clause: &ConstrainedClause,
    other: &ConstrainedClause,
) -> Option<SplitResult> {
    // Default: split using the selected literal of `other`.
    sggs_splitting_on(clause, other, other.selected)
}

/// SGGS-Splitting by a specific literal of the other clause.
///
/// This allows splitting on a non-selected literal, which is permitted by SGGS
/// to expose intersections and enable deletion (Bonacina 2016, Sect. 4.2).
pub fn sggs_splitting_on(
    clause: &ConstrainedClause,
    other: &ConstrainedClause,
    other_lit_idx: usize,
) -> Option<SplitResult> {
    let clause_lit = clause.selected_literal();
    let other_lit = &other.clause.literals[other_lit_idx];

    // The literals must have the same predicate to potentially intersect
    if clause_lit.atom.predicate != other_lit.atom.predicate {
        return None;
    }

    // Try to unify the literals (ignoring sign for intersection check)
    let _sigma = match unify_literals(clause_lit, other_lit) {
        UnifyResult::Success(s) => s,
        UnifyResult::Failure(_) => return None,
    };

    // Build the intersection constraint from the unifier
    // For each variable in clause's literal that gets bound, add a constraint
    let mut intersection_constraint = clause.constraint.clone();
    let mut has_constraint = false;

    for (clause_arg, other_arg) in clause_lit.atom.args.iter().zip(other_lit.atom.args.iter()) {
        // Only create constraints for variables in the clause being split
        if let Term::Var(_) = clause_arg {
            match other_arg {
                Term::Var(_) => {
                    // Variable vs variable: no constraint needed.
                    // Both represent all possible ground instances, so the intersection
                    // is everything and the split would be trivial.
                    // Even if the unifier binds clause_arg to other_arg (or vice versa),
                    // this is just a variable renaming, not a real constraint.
                }
                Term::App(fn_sym, _) => {
                    if fn_sym.arity == 0 {
                        // Constant: use Identical constraint
                        intersection_constraint = intersection_constraint.and(Constraint::Atomic(
                            AtomicConstraint::Identical(clause_arg.clone(), other_arg.clone()),
                        ));
                    } else {
                        // Function application: use RootEquals constraint
                        intersection_constraint = intersection_constraint.and(Constraint::Atomic(
                            AtomicConstraint::RootEquals(clause_arg.clone(), fn_sym.name.clone()),
                        ));
                    }
                    has_constraint = true;
                }
            }
        } else if let Term::App(clause_fn, _clause_args) = clause_arg {
            // Clause has a function application, check if it matches other
            match other_arg {
                Term::Var(_) => {
                    // Other is a variable, so it can match anything
                    // No constraint needed
                }
                Term::App(other_fn, _) => {
                    // Both are applications - they must have same root symbol
                    if clause_fn.name != other_fn.name || clause_fn.arity != other_fn.arity {
                        // Different function symbols - no intersection possible
                        return None;
                    }
                    // Same function symbol - recursively check args (handled by unification)
                }
            }
        }
    }

    // If no constraints were added, the split is trivial
    if !has_constraint {
        return None;
    }

    // Check if the intersection constraint combined with other's constraint is satisfiable
    let combined = intersection_constraint
        .clone()
        .and(other.constraint.clone());
    if !combined.is_satisfiable() {
        // Constraints exclude intersection
        return None;
    }

    // Build the complement constraint (negation of intersection conditions)
    let complement_constraint = build_complement_constraint(clause, clause_lit, other_lit);

    // Check if complement is satisfiable
    if !complement_constraint.is_satisfiable() {
        // Degenerate case: everything is in the intersection
        // Return just the intersection part
        return Some(SplitResult {
            parts: vec![ConstrainedClause::with_constraint(
                clause.clause.clone(),
                intersection_constraint.simplify(),
                clause.selected,
            )],
        });
    }

    // Create the two parts
    let intersection_part = ConstrainedClause::with_constraint(
        clause.clause.clone(),
        intersection_constraint.simplify(),
        clause.selected,
    );

    let complement_part = ConstrainedClause::with_constraint(
        clause.clause.clone(),
        complement_constraint.simplify(),
        clause.selected,
    );

    Some(SplitResult {
        parts: vec![intersection_part, complement_part],
    })
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
