//! Unification algorithm: Robinson's algorithm for computing MGU.

use super::Substitution;
use crate::syntax::{Literal, Term, Var};

/// Result of a unification attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnifyResult {
    /// Unification succeeded with the given most general unifier.
    Success(Substitution),
    /// Unification failed.
    Failure(UnifyError),
}

impl UnifyResult {
    pub fn is_success(&self) -> bool {
        matches!(self, UnifyResult::Success(_))
    }

    pub fn is_failure(&self) -> bool {
        matches!(self, UnifyResult::Failure(_))
    }
}

/// Reasons why unification can fail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnifyError {
    /// Occurs check failed: variable would occur in its own binding.
    OccursCheck { var: Var, term: Term },
    /// Function symbols don't match.
    SymbolClash { expected: String, found: String },
    /// Arity mismatch for function application.
    ArityMismatch {
        symbol: String,
        expected: usize,
        found: usize,
    },
}

/// Compute the most general unifier of two terms.
///
/// Uses Robinson's unification algorithm with occurs check.
pub fn unify(t1: &Term, t2: &Term) -> UnifyResult {
    unify_with_subst(t1, t2, Substitution::empty())
}

/// Internal helper: unify two terms given an existing substitution.
fn unify_with_subst(t1: &Term, t2: &Term, subst: Substitution) -> UnifyResult {
    // Apply current substitution to both terms
    let t1_applied = subst.apply_to_term(t1);
    let t2_applied = subst.apply_to_term(t2);

    match (&t1_applied, &t2_applied) {
        // If both are identical, unification succeeds
        (a, b) if a == b => UnifyResult::Success(subst),

        // Variable on the left
        (Term::Var(var), term) => unify_var(var, term, subst),

        // Variable on the right
        (term, Term::Var(var)) => unify_var(var, term, subst),

        // Both are function applications
        (Term::App(fn1, args1), Term::App(fn2, args2)) => {
            // Check symbol match
            if fn1.name != fn2.name {
                return UnifyResult::Failure(UnifyError::SymbolClash {
                    expected: fn1.name.clone(),
                    found: fn2.name.clone(),
                });
            }

            // Check arity match
            if args1.len() != args2.len() {
                return UnifyResult::Failure(UnifyError::ArityMismatch {
                    symbol: fn1.name.clone(),
                    expected: args1.len(),
                    found: args2.len(),
                });
            }

            // Check result sort match
            if fn1.result_sort != fn2.result_sort {
                return UnifyResult::Failure(UnifyError::SymbolClash {
                    expected: fn1.result_sort.clone().unwrap_or_default(),
                    found: fn2.result_sort.clone().unwrap_or_default(),
                });
            }

            // Unify arguments pairwise
            let pairs: Vec<(Term, Term)> =
                args1.iter().cloned().zip(args2.iter().cloned()).collect();
            unify_many_with_subst(&pairs, subst)
        }
    }
}

/// Unify a variable with a term.
fn unify_var(var: &Var, term: &Term, subst: Substitution) -> UnifyResult {
    // Occurs check: variable cannot occur in the term it's being unified with
    if term.occurs(var) {
        return UnifyResult::Failure(UnifyError::OccursCheck {
            var: var.clone(),
            term: term.clone(),
        });
    }

    // Sort check: if variable has a sort, the term must have a compatible sort
    if let Some(var_sort) = var.sort() {
        match term {
            Term::Var(other_var) => {
                if let Some(other_sort) = other_var.sort() {
                    if var_sort != other_sort {
                        return UnifyResult::Failure(UnifyError::SymbolClash {
                            expected: var_sort.to_string(),
                            found: other_sort.to_string(),
                        });
                    }
                }
            }
            Term::App(fn_sym, _) => {
                if let Some(result_sort) = &fn_sym.result_sort {
                    if var_sort != result_sort {
                        return UnifyResult::Failure(UnifyError::SymbolClash {
                            expected: var_sort.to_string(),
                            found: result_sort.clone(),
                        });
                    }
                }
            }
        }
    }

    // Create new binding and compose with existing substitution to maintain idempotence.
    // The composition new_binding ∘ subst ensures that all existing bindings
    // are updated to use the new binding's target, creating a closed substitution.
    let new_binding = Substitution::singleton(var.clone(), term.clone());
    let composed = new_binding.compose(&subst);
    UnifyResult::Success(composed)
}

/// Internal helper for unify_many with existing substitution.
fn unify_many_with_subst(pairs: &[(Term, Term)], mut subst: Substitution) -> UnifyResult {
    for (t1, t2) in pairs {
        match unify_with_subst(t1, t2, subst) {
            UnifyResult::Success(s) => subst = s,
            UnifyResult::Failure(e) => return UnifyResult::Failure(e),
        }
    }
    UnifyResult::Success(subst)
}

/// Compute the MGU of two literals (atoms must match, ignoring sign).
///
/// For resolution, we often unify complementary literals.
/// This function unifies the atoms of two literals.
pub fn unify_literals(l1: &Literal, l2: &Literal) -> UnifyResult {
    let atom1 = &l1.atom;
    let atom2 = &l2.atom;

    // Check predicate name matches
    if atom1.predicate != atom2.predicate {
        return UnifyResult::Failure(UnifyError::SymbolClash {
            expected: atom1.predicate.clone(),
            found: atom2.predicate.clone(),
        });
    }

    // Check arity matches
    if atom1.args.len() != atom2.args.len() {
        return UnifyResult::Failure(UnifyError::ArityMismatch {
            symbol: atom1.predicate.clone(),
            expected: atom1.args.len(),
            found: atom2.args.len(),
        });
    }

    // Unify arguments pairwise
    let pairs: Vec<(Term, Term)> = atom1
        .args
        .iter()
        .cloned()
        .zip(atom2.args.iter().cloned())
        .collect();
    unify_many(&pairs)
}

/// Simultaneous unification of multiple term pairs.
///
/// Finds a substitution σ such that σ(t1ᵢ) = σ(t2ᵢ) for all pairs.
pub fn unify_many(pairs: &[(Term, Term)]) -> UnifyResult {
    unify_many_with_subst(pairs, Substitution::empty())
}
