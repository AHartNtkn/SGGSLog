//! Query answering for SGGSLog.

use std::collections::HashSet;

use crate::syntax::{Clause, Literal, Var};
use crate::theory::Theory;
use crate::unify::Substitution;
use super::DerivationConfig;

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

/// Result of answering a query (model-based).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryResult {
    /// One or more answers (substitutions) were found.
    Answers(Vec<Substitution>),
    /// No answers exist in the constructed model.
    NoAnswers,
    /// Resource limit reached before completion.
    ResourceLimit,
}

/// Answer a query against a theory using SGGS model construction.
///
/// Semantics: build (or approximate) a model with SGGS, then return substitutions
/// that make the query true in that model.
pub fn answer_query(
    _theory: &Theory,
    _query: &Query,
    _config: DerivationConfig,
) -> QueryResult {
    todo!("answer_query implementation")
}
