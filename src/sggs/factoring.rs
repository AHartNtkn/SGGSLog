//! SGGS-Factoring for conflict solving.

use super::ConstrainedClause;
use crate::constraint::{AtomicConstraint, Constraint};
use crate::syntax::{Clause, Term};
use crate::unify::{unify_literals, UnifyResult};

/// SGGS-Factoring: factor a clause by unifying a non-selected literal with the selected literal.
///
/// This is used during conflict solving to avoid losing assignments after a move.
/// Returns the factored clause if applicable.
pub fn sggs_factoring(
    clause: &ConstrainedClause,
    other_lit_idx: usize,
) -> Option<ConstrainedClause> {
    // Can't factor with the selected literal itself
    if other_lit_idx == clause.selected {
        return None;
    }

    // Get the selected literal and the other literal
    let selected = clause.selected_literal();
    let other_lit = clause.clause.literals.get(other_lit_idx)?;

    // Must be same polarity and predicate to factor
    if selected.positive != other_lit.positive ||
       selected.atom.predicate != other_lit.atom.predicate {
        return None;
    }

    // Unify the selected literal with the other literal
    let sigma = match unify_literals(selected, other_lit) {
        UnifyResult::Success(s) => s,
        UnifyResult::Failure(_) => return None,
    };

    // Build constraint from the unifier
    let mut unifier_constraint = Constraint::True;
    for v in sigma.domain() {
        if let Some(t) = sigma.lookup(v) {
            unifier_constraint = unifier_constraint.and(Constraint::Atomic(
                AtomicConstraint::Identical(Term::Var(v.clone()), t.clone()),
            ));
        }
    }

    // Check if the combined constraint is satisfiable
    let combined_constraint = clause.constraint.clone().and(unifier_constraint);
    if !combined_constraint.is_satisfiable() {
        return None;
    }

    // Apply substitution to all literals
    let factored_literals: Vec<_> = clause
        .clause
        .literals
        .iter()
        .map(|lit| lit.apply_subst(&sigma))
        .collect();

    // Remove duplicate literals (the other literal is now identical to selected after unification)
    let mut unique_literals = Vec::new();
    let mut seen_indices = std::collections::HashSet::new();
    for (idx, lit) in factored_literals.iter().enumerate() {
        if idx == other_lit_idx {
            continue; // Skip the factored literal
        }
        // Also avoid duplicates
        let found_dup = unique_literals.iter().any(|l| l == lit);
        if !found_dup {
            unique_literals.push(lit.clone());
            seen_indices.insert(idx);
        }
    }

    // Find new index of the selected literal
    let mut new_selected = 0;
    let selected_after_subst = selected.apply_subst(&sigma);
    for (new_idx, lit) in unique_literals.iter().enumerate() {
        if *lit == selected_after_subst {
            new_selected = new_idx;
            break;
        }
    }

    Some(ConstrainedClause::with_constraint(
        Clause::new(unique_literals),
        combined_constraint.simplify(),
        new_selected,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::Constraint;
    use crate::syntax::{Clause, Literal, Term};
    use std::collections::HashSet;

    #[test]
    fn test_factoring_unifies_selected_with_other_literal() {
        // Source: SGGSdpFOL, rule factor (Fig. 2) and standard factoring.
        let clause = ConstrainedClause::with_constraint(
            Clause::new(vec![
                Literal::pos("P", vec![Term::var("X")]),
                Literal::pos("P", vec![Term::constant("a")]),
                Literal::pos("R", vec![Term::var("X")]),
            ]),
            Constraint::True,
            0,
        );

        let factored = sggs_factoring(&clause, 1).expect("expected factoring");
        let expected: HashSet<_> = vec![
            Literal::pos("P", vec![Term::constant("a")]),
            Literal::pos("R", vec![Term::constant("a")]),
        ]
        .into_iter()
        .collect();
        let got: HashSet<_> = factored.clause.literals.clone().into_iter().collect();
        assert_eq!(got, expected);
        assert_eq!(
            factored.selected_literal(),
            &Literal::pos("P", vec![Term::constant("a")])
        );
    }

    #[test]
    fn test_factoring_not_applicable_when_no_unifier() {
        let clause = ConstrainedClause::with_constraint(
            Clause::new(vec![
                Literal::pos("P", vec![Term::var("X")]),
                Literal::pos("Q", vec![Term::constant("a")]),
            ]),
            Constraint::True,
            0,
        );

        assert!(sggs_factoring(&clause, 1).is_none());
    }

    #[test]
    fn test_factoring_rejects_unsatisfiable_constraints() {
        // If factoring would violate the clause constraint, it should not apply.
        let clause = ConstrainedClause::with_constraint(
            Clause::new(vec![
                Literal::pos("P", vec![Term::var("X")]),
                Literal::pos("P", vec![Term::constant("a")]),
            ]),
            Constraint::Atomic(crate::constraint::AtomicConstraint::NotIdentical(
                Term::var("X"),
                Term::constant("a"),
            )),
            0,
        );

        assert!(sggs_factoring(&clause, 1).is_none());
    }
}
