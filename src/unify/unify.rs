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
    todo!("unify implementation")
}

/// Compute the MGU of two literals (atoms must match, ignoring sign).
///
/// For resolution, we often unify complementary literals.
/// This function unifies the atoms of two literals.
pub fn unify_literals(l1: &Literal, l2: &Literal) -> UnifyResult {
    todo!("unify_literals implementation")
}

/// Simultaneous unification of multiple term pairs.
///
/// Finds a substitution σ such that σ(t1ᵢ) = σ(t2ᵢ) for all pairs.
pub fn unify_many(pairs: &[(Term, Term)]) -> UnifyResult {
    todo!("unify_many implementation")
}
