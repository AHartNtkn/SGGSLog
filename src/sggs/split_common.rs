//! Common utilities for SGGS splitting operations.

use super::ConstrainedClause;
use crate::constraint::{AtomicConstraint, Constraint};
use crate::syntax::{Literal, Term};

/// Build the complement constraint for a split.
///
/// Given the clause being split and two literals (one from the clause, one from the other clause),
/// builds a constraint representing all instances that do NOT fall into the intersection.
pub fn build_complement_constraint(
    clause: &ConstrainedClause,
    clause_lit: &Literal,
    other_lit: &Literal,
) -> Constraint {
    let mut complement_parts = Vec::new();

    for (clause_arg, other_arg) in clause_lit.atom.args.iter().zip(other_lit.atom.args.iter()) {
        if let Term::Var(_) = clause_arg {
            match other_arg {
                Term::Var(_) => {
                    // No constraint contribution from variable vs variable
                }
                Term::App(fn_sym, _) => {
                    if fn_sym.arity == 0 {
                        // Constant: use NotIdentical constraint
                        complement_parts.push(Constraint::Atomic(AtomicConstraint::NotIdentical(
                            clause_arg.clone(),
                            other_arg.clone(),
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
    // (x ≠ a ∨ y ≠ b) is the complement of (x = a ∧ y = b)
    let mut result = complement_parts.pop().unwrap();
    for part in complement_parts {
        result = result.or(part);
    }

    // Combine with original clause constraint
    clause.constraint.clone().and(result)
}
