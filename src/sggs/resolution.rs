//! SGGS-Resolution for conflict explanation.

use super::{ConstrainedClause, Trail};
use crate::syntax::Clause;
use crate::unify::{unify_literals, Substitution, UnifyResult};

/// Result of conflict explanation via resolution.
#[derive(Debug)]
pub enum ResolutionResult {
    /// Derived empty clause (theory is unsatisfiable)
    EmptyClause,
    /// Resolution step produced new clause
    Resolvent(ConstrainedClause),
    /// Resolution not applicable due to unmet preconditions
    Inapplicable,
}

/// Check if a clause is I-all-true in I[Γ].
///
/// A clause is I-all-true if all its non-selected literals are I-true under the initial
/// interpretation. The selected literal is always true in I[Γ] by definition.
///
/// Note: This check only applies to clauses with constraint True. Clauses with
/// non-trivial constraints may have the I-all-true property restricted to their
/// constrained ground instances, which is handled by constraint entailment.
fn is_i_all_true_in_trail(clause: &ConstrainedClause, trail: &Trail) -> bool {
    use crate::constraint::Constraint;

    // Clauses with non-trivial constraints are checked via constraint entailment
    // rather than the basic I-all-true check
    if !matches!(clause.constraint, Constraint::True) {
        return true;
    }

    let interp = trail.initial_interpretation();
    for (idx, lit) in clause.clause.literals.iter().enumerate() {
        if idx == clause.selected {
            // Selected literal is always true in I[Γ] by definition
            continue;
        }
        // Non-selected literals must be I-true
        if !interp.is_true(lit) {
            return false;
        }
    }
    true
}

/// Check if constraint A entails constraint B after applying substitution.
///
/// A |= Bσ means that for all ground instances where A holds, Bσ also holds.
fn constraint_entails(
    a: &crate::constraint::Constraint,
    b: &crate::constraint::Constraint,
    sigma: &Substitution,
) -> bool {
    use crate::constraint::{AtomicConstraint, Constraint};

    // Apply substitution to b and simplify
    let b_sigma = apply_subst_to_constraint(b, sigma);
    let b_simplified = simplify_constraint_after_subst(&b_sigma);

    // If Bσ is True (after simplification), A always entails it
    if matches!(b_simplified, Constraint::True) {
        return true;
    }

    // If A is False, it entails anything (vacuously true)
    if matches!(a, Constraint::False) {
        return true;
    }

    // If A is True and Bσ is not True, A |= Bσ only if Bσ is always true
    if matches!(a, Constraint::True) {
        return matches!(b_simplified, Constraint::True);
    }

    // If A equals Bσ, entailment holds trivially
    if a == &b_simplified {
        return true;
    }

    // Special case: A |= (A ∨ C) - if A is a disjunct of Bσ
    if let Constraint::Or(left, right) = &b_simplified {
        if a == left.as_ref() || a == right.as_ref() {
            return true;
        }
        // Also check if A entails either branch
        if constraint_entails_simple(a, left) || constraint_entails_simple(a, right) {
            return true;
        }
    }

    // Check atomic entailments
    if let (Constraint::Atomic(atom_a), Constraint::Atomic(atom_b)) = (a, &b_simplified) {
        return atomic_entails(atom_a, atom_b);
    }

    // For And constraints, A1 ∧ A2 |= B if either A1 |= B or A2 |= B
    if let Constraint::And(left, right) = a {
        if constraint_entails_simple(left, &b_simplified)
            || constraint_entails_simple(right, &b_simplified)
        {
            return true;
        }
    }

    // General case: A |= Bσ iff A ∧ ¬Bσ is unsatisfiable
    let a_and_not_b = a.clone().and(b_simplified.not());
    !a_and_not_b.is_satisfiable()
}

/// Simple entailment check without substitution (for recursive calls)
fn constraint_entails_simple(
    a: &crate::constraint::Constraint,
    b: &crate::constraint::Constraint,
) -> bool {
    use crate::constraint::Constraint;

    if matches!(b, Constraint::True) {
        return true;
    }
    if matches!(a, Constraint::False) {
        return true;
    }
    if matches!(a, Constraint::True) {
        return matches!(b, Constraint::True);
    }
    if a == b {
        return true;
    }

    let a_and_not_b = a.clone().and(b.clone().not());
    !a_and_not_b.is_satisfiable()
}

/// Apply substitution to a constraint.
fn apply_subst_to_constraint(
    c: &crate::constraint::Constraint,
    sigma: &Substitution,
) -> crate::constraint::Constraint {
    use crate::constraint::{AtomicConstraint, Constraint};

    match c {
        Constraint::True => Constraint::True,
        Constraint::False => Constraint::False,
        Constraint::Atomic(a) => Constraint::Atomic(apply_subst_to_atomic(a, sigma)),
        Constraint::And(left, right) => apply_subst_to_constraint(left, sigma)
            .and(apply_subst_to_constraint(right, sigma)),
        Constraint::Or(left, right) => apply_subst_to_constraint(left, sigma)
            .or(apply_subst_to_constraint(right, sigma)),
        Constraint::Not(inner) => apply_subst_to_constraint(inner, sigma).not(),
    }
}

/// Apply substitution to an atomic constraint.
fn apply_subst_to_atomic(
    a: &crate::constraint::AtomicConstraint,
    sigma: &Substitution,
) -> crate::constraint::AtomicConstraint {
    use crate::constraint::AtomicConstraint;
    use crate::syntax::Term;

    match a {
        AtomicConstraint::Identical(t1, t2) => {
            AtomicConstraint::Identical(sigma.apply_to_term(t1), sigma.apply_to_term(t2))
        }
        AtomicConstraint::NotIdentical(t1, t2) => {
            AtomicConstraint::NotIdentical(sigma.apply_to_term(t1), sigma.apply_to_term(t2))
        }
        AtomicConstraint::RootEquals(t, s) => {
            AtomicConstraint::RootEquals(sigma.apply_to_term(t), s.clone())
        }
        AtomicConstraint::RootNotEquals(t, s) => {
            AtomicConstraint::RootNotEquals(sigma.apply_to_term(t), s.clone())
        }
    }
}

/// Simplify a constraint after substitution by evaluating trivial conditions.
fn simplify_constraint_after_subst(c: &crate::constraint::Constraint) -> crate::constraint::Constraint {
    use crate::constraint::{AtomicConstraint, Constraint};
    use crate::syntax::Term;

    match c {
        Constraint::True => Constraint::True,
        Constraint::False => Constraint::False,
        Constraint::Atomic(a) => {
            match a {
                AtomicConstraint::Identical(t1, t2) => {
                    if t1 == t2 {
                        Constraint::True
                    } else {
                        Constraint::Atomic(a.clone())
                    }
                }
                AtomicConstraint::NotIdentical(t1, t2) => {
                    if t1 == t2 {
                        Constraint::False
                    } else {
                        Constraint::Atomic(a.clone())
                    }
                }
                AtomicConstraint::RootEquals(t, expected) => {
                    match t {
                        Term::App(sym, _) => {
                            if &sym.name == expected {
                                Constraint::True
                            } else {
                                Constraint::False
                            }
                        }
                        Term::Var(_) => Constraint::Atomic(a.clone()),
                    }
                }
                AtomicConstraint::RootNotEquals(t, expected) => {
                    match t {
                        Term::App(sym, _) => {
                            if &sym.name == expected {
                                Constraint::False
                            } else {
                                Constraint::True
                            }
                        }
                        Term::Var(_) => Constraint::Atomic(a.clone()),
                    }
                }
            }
        }
        Constraint::And(left, right) => {
            let left_simp = simplify_constraint_after_subst(left);
            let right_simp = simplify_constraint_after_subst(right);
            match (&left_simp, &right_simp) {
                (Constraint::True, _) => right_simp,
                (_, Constraint::True) => left_simp,
                (Constraint::False, _) | (_, Constraint::False) => Constraint::False,
                _ => left_simp.and(right_simp),
            }
        }
        Constraint::Or(left, right) => {
            let left_simp = simplify_constraint_after_subst(left);
            let right_simp = simplify_constraint_after_subst(right);
            match (&left_simp, &right_simp) {
                (Constraint::True, _) | (_, Constraint::True) => Constraint::True,
                (Constraint::False, _) => right_simp,
                (_, Constraint::False) => left_simp,
                _ => left_simp.or(right_simp),
            }
        }
        Constraint::Not(inner) => {
            let inner_simp = simplify_constraint_after_subst(inner);
            match inner_simp {
                Constraint::True => Constraint::False,
                Constraint::False => Constraint::True,
                other => other.not(),
            }
        }
    }
}

/// Check if atomic constraint A entails atomic constraint B.
fn atomic_entails(
    a: &crate::constraint::AtomicConstraint,
    b: &crate::constraint::AtomicConstraint,
) -> bool {
    use crate::constraint::AtomicConstraint;

    // Identical entailments
    match (a, b) {
        // X=t entails X=t
        (AtomicConstraint::Identical(t1, t2), AtomicConstraint::Identical(t3, t4)) => {
            (t1 == t3 && t2 == t4) || (t1 == t4 && t2 == t3)
        }
        // X≠t entails X≠t
        (AtomicConstraint::NotIdentical(t1, t2), AtomicConstraint::NotIdentical(t3, t4)) => {
            (t1 == t3 && t2 == t4) || (t1 == t4 && t2 == t3)
        }
        _ => false,
    }
}

/// Check if a literal is uniformly false in I[Γ].
///
/// A literal is uniformly false in I[Γ] if:
/// 1. Its complement is uniformly true in I[Γ] (made true by a selected literal), OR
/// 2. It is I-false and not made true by I^p(Γ)
fn is_uniformly_false_in_trail(lit: &crate::syntax::Literal, trail: &Trail) -> bool {
    let init_interp = trail.initial_interpretation();
    let trail_interp = trail.interpretation();

    // Check if the complement is uniformly true in I[Γ] (selected on trail)
    let complement = lit.negated();
    if trail_interp.is_uniformly_true(&complement) {
        return true;
    }

    // Otherwise, check if it's I-false and not made true by I^p(Γ)
    if init_interp.is_false(lit) {
        let partial = trail.partial_interpretation();
        return !partial.contains_ground(lit);
    }

    false
}

/// Check if a clause is a conflict clause in I[Γ].
///
/// A clause is a conflict clause if all its literals are uniformly false in I[Γ].
fn is_conflict_clause(clause: &ConstrainedClause, trail: &Trail) -> bool {
    clause.clause.literals.iter().all(|lit| is_uniformly_false_in_trail(lit, trail))
}

/// SGGS-Resolution: resolve conflict clause with justifications.
///
/// When a conflict clause has a selected literal that complements
/// an I-true selected literal from an earlier clause, we resolve them.
///
/// Preconditions:
/// 1. The conflict clause must be a conflict (all literals uniformly false in I[Γ])
/// 2. The justifying clause must be I-all-true
/// 3. The justifying clause's selected literal must unify with the conflict's complement
pub fn sggs_resolution(conflict: &ConstrainedClause, trail: &Trail) -> ResolutionResult {
    let selected = conflict.selected_literal();

    // Precondition 1: The conflict clause must be a conflict in I[Γ]
    // A clause is a conflict if all its literals are uniformly false in I[Γ],
    // meaning they are I-false and not made true by I^p(Γ).
    if !is_conflict_clause(conflict, trail) {
        return ResolutionResult::Inapplicable;
    }

    // Find the complement of the conflict's selected literal
    let complement = selected.negated();

    // Get the disjoint prefix length - justifications must be within dp(Γ)
    let dp_len = trail.disjoint_prefix_length();

    for (idx, justifying_clause) in trail.clauses().iter().enumerate() {
        // Precondition: Justifying clause must be in dp(Γ)
        if idx >= dp_len {
            continue;
        }

        // Skip the conflict clause itself if it's on the trail
        if std::ptr::eq(justifying_clause, conflict) {
            continue;
        }

        let justifying_selected = justifying_clause.selected_literal();

        // Check if justifying_selected matches the complement of the conflict's selected literal.
        // This means the justifying clause's selected literal is the REASON the conflict's
        // selected literal is false in I[Γ].
        if complement.positive != justifying_selected.positive
            || complement.atom.predicate != justifying_selected.atom.predicate
        {
            continue;
        }

        // Precondition 2: Justifying clause must be I-all-true in I[Γ]
        // (all non-selected literals must be I-true under initial interpretation)
        if !is_i_all_true_in_trail(justifying_clause, trail) {
            continue;
        }

        if let UnifyResult::Success(sigma) = unify_literals(&complement, justifying_selected) {
            // Precondition: Constraint entailment A |= Bσ
            // The conflict's constraint must entail the justification's constraint after substitution
            if !constraint_entails(&conflict.constraint, &justifying_clause.constraint, &sigma) {
                continue;
            }

            // Build the resolvent:
            // - Remove the selected literal from conflict
            // - Remove the selected literal from justifying clause
            // - Merge remaining literals and apply substitution

            let mut resolvent_lits = Vec::new();

            // Add non-selected literals from conflict (applying substitution)
            for (idx, lit) in conflict.clause.literals.iter().enumerate() {
                if idx != conflict.selected {
                    resolvent_lits.push(lit.apply_subst(&sigma));
                }
            }

            // Add non-selected literals from justifying clause (applying substitution)
            for (idx, lit) in justifying_clause.clause.literals.iter().enumerate() {
                if idx != justifying_clause.selected {
                    let applied = lit.apply_subst(&sigma);
                    // Avoid duplicates
                    if !resolvent_lits.contains(&applied) {
                        resolvent_lits.push(applied);
                    }
                }
            }

            // Check if resolvent is empty
            if resolvent_lits.is_empty() {
                return ResolutionResult::EmptyClause;
            }

            // Find the selected literal in the resolvent (first I-false literal)
            let init_interp = trail.initial_interpretation();
            let mut new_selected = 0;
            for (idx, lit) in resolvent_lits.iter().enumerate() {
                if init_interp.is_false(lit) {
                    new_selected = idx;
                    break;
                }
            }

            // Use conflict's constraint (since it entails justification's constraint)
            // Per SGGSdpFOL Def. 26: the resolvent keeps A as its constraint
            let resolvent_constraint = conflict.constraint.clone();

            return ResolutionResult::Resolvent(ConstrainedClause::with_constraint(
                Clause::new(resolvent_lits),
                resolvent_constraint,
                new_selected,
            ));
        }
    }

    ResolutionResult::Inapplicable
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::Constraint;
    use crate::sggs::{ConstrainedClause, InitialInterpretation, Trail};
    use crate::syntax::{Clause, Literal, Term};

    fn unit(lit: Literal) -> ConstrainedClause {
        ConstrainedClause::with_constraint(Clause::new(vec![lit]), Constraint::True, 0)
    }

    #[test]
    fn test_resolution_resolvent_definition_2() {
        // Source: SGGSdpFOL.pdf, Definition 2 (SGGS-Resolution).
        // Resolve A | C[L] with B | D[M], where M is I-all-true and precedes.
        // Conflict clause definition (paper6.txt): "A clause is a conflict clause if all its
        // literals are uniformly false in I[Γ]." Under I⁻, any positive literal is uniformly
        // false unless made true by I^p(Γ), so P(a) ∨ Q(a) is a conflict clause here.
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        let left = unit(Literal::neg("P", vec![Term::constant("a")]));
        trail.push(left.clone()); // I-all-true clause in dp(Γ)

        let conflict_clause = ConstrainedClause::with_constraint(
            Clause::new(vec![
                Literal::pos("P", vec![Term::constant("a")]),
                Literal::pos("Q", vec![Term::constant("a")]),
            ]),
            Constraint::True,
            0,
        );
        trail.push(conflict_clause.clone());

        match sggs_resolution(&conflict_clause, &trail) {
            ResolutionResult::Resolvent(resolvent) => {
                assert_eq!(
                    resolvent.clause.literals,
                    vec![Literal::pos("Q", vec![Term::constant("a")])]
                );
            }
            ResolutionResult::EmptyClause => panic!("Expected non-empty resolvent"),
            ResolutionResult::Inapplicable => panic!("Resolution should be applicable"),
        }
    }

    #[test]
    fn test_resolution_empty_clause() {
        // Source: SGGSdpFOL.pdf, Definition 2 (SGGS-Resolution).
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        let left = unit(Literal::neg("P", vec![Term::constant("a")]));
        trail.push(left);

        let conflict_clause = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
            Constraint::True,
            0,
        );
        trail.push(conflict_clause.clone());

        match sggs_resolution(&conflict_clause, &trail) {
            ResolutionResult::EmptyClause => {}
            ResolutionResult::Resolvent(_) => panic!("Expected empty clause"),
            ResolutionResult::Inapplicable => panic!("Resolution should be applicable"),
        }
    }
}
