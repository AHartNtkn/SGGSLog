//! Queries: conjunctions of literals in first-order logic.

use std::collections::HashSet;

use super::{Clause, Literal, Var};

/// A conjunctive query (goal).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Query {
    pub literals: Vec<Literal>,
}

impl Query {
    pub fn new(literals: Vec<Literal>) -> Self {
        Query { literals }
    }

    /// Collect variables appearing in the query.
    pub fn variables(&self) -> HashSet<Var> {
        let mut vars = HashSet::new();
        for lit in &self.literals {
            vars.extend(lit.variables());
        }
        vars
    }

    /// Check if the query is ground.
    pub fn is_ground(&self) -> bool {
        self.literals.iter().all(|l| l.is_ground())
    }

    /// Convert the negation of the query into a clause.
    /// ¬(L1 ∧ ... ∧ Ln) ≡ ¬L1 ∨ ... ∨ ¬Ln
    pub fn negated_as_clause(&self) -> Clause {
        Clause::new(self.literals.iter().map(|l| l.negated()).collect())
    }
}
