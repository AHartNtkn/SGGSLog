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
        Substitution {
            bindings: HashMap::new(),
        }
    }

    /// Create a substitution with a single binding.
    pub fn singleton(var: Var, term: Term) -> Self {
        let mut bindings = HashMap::new();
        bindings.insert(var, term);
        Substitution { bindings }
    }

    /// Add a binding to this substitution.
    pub fn bind(&mut self, var: Var, term: Term) {
        self.bindings.insert(var, term);
    }

    /// Look up a variable in this substitution.
    pub fn lookup(&self, var: &Var) -> Option<&Term> {
        self.bindings.get(var)
    }

    /// Compose two substitutions: (self ∘ other)(x) = self(other(x))
    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut result = Substitution::empty();

        // First, apply self to all bindings in other
        for (var, term) in &other.bindings {
            result.bind(var.clone(), self.apply_to_term(term));
        }

        // Then add bindings from self that aren't in other's domain
        for (var, term) in &self.bindings {
            if !other.bindings.contains_key(var) {
                result.bind(var.clone(), term.clone());
            }
        }

        result
    }

    /// Apply this substitution to a term.
    pub fn apply_to_term(&self, term: &Term) -> Term {
        match term {
            Term::Var(var) => match self.bindings.get(var) {
                Some(t) => t.clone(),
                None => term.clone(),
            },
            Term::App(fn_sym, args) => {
                let new_args: Vec<Term> = args.iter().map(|arg| self.apply_to_term(arg)).collect();
                Term::App(fn_sym.clone(), new_args)
            }
        }
    }

    /// Get the domain of this substitution (variables that are mapped).
    pub fn domain(&self) -> HashSet<&Var> {
        self.bindings.keys().collect()
    }

    /// Iterate over the bindings in this substitution.
    pub fn bindings(&self) -> impl Iterator<Item = (&Var, &Term)> {
        self.bindings.iter()
    }

    /// Check if this substitution is empty (has no bindings).
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Check if this substitution is a variable renaming.
    /// A renaming maps variables to variables bijectively.
    pub fn is_renaming(&self) -> bool {
        let mut target_vars: HashSet<&Var> = HashSet::new();

        for (from_var, term) in &self.bindings {
            // Must map to a variable
            let to_var = match term {
                Term::Var(v) => v,
                _ => return false,
            };

            // Must preserve sorts
            if from_var.sort() != to_var.sort() {
                return false;
            }

            // Must be injective (no two vars map to the same var)
            if !target_vars.insert(to_var) {
                return false;
            }
        }

        true
    }
}
