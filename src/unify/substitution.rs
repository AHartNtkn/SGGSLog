//! Substitution: mapping variables to terms.

use crate::syntax::{Term, Var};
use std::collections::{HashMap, HashSet};

/// A substitution mapping variables to terms.
///
/// Substitutions are fundamental to unification and SGGS.
/// A substitution σ = {X₁ → t₁, ..., Xₙ → tₙ} maps variables to terms.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Substitution {
    bindings: HashMap<Var, Term>,
}

impl Substitution {
    /// Create an empty substitution (identity).
    pub fn empty() -> Self {
        todo!("empty implementation")
    }

    /// Create a substitution with a single binding.
    pub fn singleton(var: Var, term: Term) -> Self {
        todo!("singleton implementation")
    }

    /// Add a binding to this substitution.
    pub fn bind(&mut self, var: Var, term: Term) {
        todo!("bind implementation")
    }

    /// Look up a variable in this substitution.
    pub fn lookup(&self, var: &Var) -> Option<&Term> {
        todo!("lookup implementation")
    }

    /// Compose two substitutions: (self ∘ other)(x) = self(other(x))
    pub fn compose(&self, other: &Substitution) -> Substitution {
        todo!("compose implementation")
    }

    /// Apply this substitution to a term.
    pub fn apply_to_term(&self, term: &Term) -> Term {
        todo!("apply_to_term implementation")
    }

    /// Get the domain of this substitution (variables that are mapped).
    pub fn domain(&self) -> HashSet<&Var> {
        todo!("domain implementation")
    }

    /// Check if this substitution is a variable renaming.
    /// A renaming maps variables to variables bijectively.
    pub fn is_renaming(&self) -> bool {
        todo!("is_renaming implementation")
    }
}
