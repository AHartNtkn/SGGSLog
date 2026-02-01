//! SGGS Left-Splitting (l-split) for conflict solving.

use super::{ConstrainedClause, SplitResult};
use crate::constraint::{AtomicConstraint, Constraint};
use crate::syntax::Term;
use crate::unify::{unify_literals, UnifyResult};

/// SGGS left-splitting: split a clause using a conflicting clause to isolate intersections.
///
/// Left-split is used when a clause's selected literal intersects with a conflicting
/// clause (opposite polarity). It partitions the clause into an intersection part
/// (instances that unify with the conflict) and a complement part (remaining instances).
///
/// Returns None if:
/// - The literals have different predicates (no possible intersection)
/// - The conflict clause has factorable literals (factoring should be preferred)
/// - No non-trivial split is possible
pub fn sggs_left_split(
    clause: &ConstrainedClause,
    conflict: &ConstrainedClause,
) -> Option<SplitResult> {
    let clause_lit = clause.selected_literal();
    let conflict_lit = conflict.selected_literal();

    // The literals must have the same predicate to potentially intersect
    // (they have opposite signs because conflict is the negation)
    if clause_lit.atom.predicate != conflict_lit.atom.predicate {
        return None;
    }

    // Check if factoring is applicable on the conflict clause (condition †)
    // If the conflict has another same-sign literal unifying with its selected literal,
    // factoring should be preferred over left-split.
    if is_factoring_applicable(conflict) {
        return None;
    }

    // Try to unify the literals (ignoring sign for intersection check)
    let sigma = match unify_literals(clause_lit, conflict_lit) {
        UnifyResult::Success(s) => s,
        UnifyResult::Failure(_) => return None,
    };

    // Build the intersection constraint from the unifier
    let mut intersection_constraint = clause.constraint.clone();
    let mut has_constraint = false;

    for (clause_arg, conflict_arg) in clause_lit
        .atom
        .args
        .iter()
        .zip(conflict_lit.atom.args.iter())
    {
        // Only create constraints for variables in the clause being split
        if let Term::Var(_) = clause_arg {
            match conflict_arg {
                Term::Var(_) => {
                    // Variable vs variable: check if unifier binds clause_arg
                    if let Some(binding) = sigma.lookup(&extract_var(clause_arg)) {
                        if binding != clause_arg {
                            intersection_constraint = intersection_constraint.and(
                                Constraint::Atomic(AtomicConstraint::Identical(
                                    clause_arg.clone(),
                                    binding.clone(),
                                )),
                            );
                            has_constraint = true;
                        }
                    }
                }
                Term::App(fn_sym, _) => {
                    if fn_sym.arity == 0 {
                        // Constant: use Identical constraint
                        intersection_constraint = intersection_constraint.and(
                            Constraint::Atomic(AtomicConstraint::Identical(
                                clause_arg.clone(),
                                conflict_arg.clone(),
                            )),
                        );
                    } else {
                        // Function application: use RootEquals constraint
                        intersection_constraint = intersection_constraint.and(
                            Constraint::Atomic(AtomicConstraint::RootEquals(
                                clause_arg.clone(),
                                fn_sym.name.clone(),
                            )),
                        );
                    }
                    has_constraint = true;
                }
            }
        } else if let Term::App(clause_fn, _) = clause_arg {
            match conflict_arg {
                Term::Var(_) => {
                    // Conflict has variable, clause has application - no constraint needed
                }
                Term::App(conflict_fn, _) => {
                    // Both are applications - must have same root symbol
                    if clause_fn.name != conflict_fn.name || clause_fn.arity != conflict_fn.arity {
                        return None;
                    }
                }
            }
        }
    }

    // If no constraints were added, the split is trivial
    if !has_constraint {
        return None;
    }

    // Check if the intersection constraint is satisfiable
    if !intersection_constraint.is_satisfiable() {
        return None;
    }

    // Build the complement constraint (negation of intersection conditions)
    let complement_constraint = build_complement_constraint(clause, clause_lit, conflict_lit);

    // Check if complement is satisfiable
    if !complement_constraint.is_satisfiable() {
        // Degenerate case: everything is in the intersection
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

/// Check if factoring is applicable on a clause (condition †).
///
/// Factoring is applicable if the clause has another same-sign literal
/// that unifies with its selected literal.
fn is_factoring_applicable(clause: &ConstrainedClause) -> bool {
    let selected = clause.selected_literal();
    let selected_sign = selected.positive;

    for (idx, lit) in clause.clause.literals.iter().enumerate() {
        if idx == clause.selected {
            continue;
        }
        // Same sign required for factoring
        if lit.positive != selected_sign {
            continue;
        }
        // Check if they unify
        if let UnifyResult::Success(_) = unify_literals(selected, lit) {
            return true;
        }
    }
    false
}

/// Extract a Var from a Term::Var
fn extract_var(term: &Term) -> crate::syntax::Var {
    match term {
        Term::Var(v) => v.clone(),
        _ => panic!("expected Var"),
    }
}

/// Build the complement constraint for the split.
fn build_complement_constraint(
    clause: &ConstrainedClause,
    clause_lit: &crate::syntax::Literal,
    conflict_lit: &crate::syntax::Literal,
) -> Constraint {
    let mut complement_parts = Vec::new();

    for (clause_arg, conflict_arg) in clause_lit.atom.args.iter().zip(conflict_lit.atom.args.iter())
    {
        if let Term::Var(_) = clause_arg {
            match conflict_arg {
                Term::Var(_) => {
                    // No constraint contribution from variable vs variable
                }
                Term::App(fn_sym, _) => {
                    if fn_sym.arity == 0 {
                        // Constant: use NotIdentical constraint
                        complement_parts.push(Constraint::Atomic(AtomicConstraint::NotIdentical(
                            clause_arg.clone(),
                            conflict_arg.clone(),
                        )));
                    } else {
                        // Function application: use RootNotEquals constraint
                        complement_parts.push(Constraint::Atomic(AtomicConstraint::RootNotEquals(
                            clause_arg.clone(),
                            fn_sym.name.clone(),
                        )));
                    }
                }
            }
        }
    }

    if complement_parts.is_empty() {
        return Constraint::False; // No complement possible
    }

    // The complement is the disjunction of negated constraints
    let mut result = complement_parts.pop().unwrap();
    for part in complement_parts {
        result = result.or(part);
    }

    // Combine with original clause constraint
    clause.constraint.clone().and(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::{AtomicConstraint, Constraint};
    use crate::syntax::{Clause, Literal, Term};

    #[test]
    fn test_left_split_intersection() {
        // Source: SGGSdpFOL, rule l-split (Fig. 2).
        // Use an I-all-true (negative) clause as the conflict side premise.
        let clause = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos(
                "P",
                vec![Term::var("x"), Term::var("y")],
            )]),
            Constraint::True,
            0,
        );
        let other = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::neg(
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
            Clause::new(vec![Literal::neg("Q", vec![Term::var("y")])]),
            Constraint::True,
            0,
        );

        assert!(sggs_left_split(&clause, &other).is_none());
    }

    #[test]
    fn test_left_split_defers_when_factoring_applicable() {
        // Source: SGGSdpFOL, Fig. 2 (l-split applies only if condition (†) does not hold).
        // If the conflict clause has another same-sign literal unifying with its selected literal,
        // factoring should be preferred, so left-split should not apply.
        let clause = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
            Constraint::True,
            0,
        );
        let other = ConstrainedClause::with_constraint(
            Clause::new(vec![
                Literal::neg("P", vec![Term::var("y")]), // selected (I-all-true)
                Literal::neg("P", vec![Term::constant("a")]),
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
            Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
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
