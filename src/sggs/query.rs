//! Query answering for SGGSLog.

use std::collections::HashSet;

use super::DerivationConfig;
use crate::syntax::Signature;
use crate::syntax::{Clause, Literal, Var};
use crate::theory::Theory;
use crate::unify::Substitution;

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
    /// A single answer (substitution) was found.
    Answer(Substitution),
    /// No answers exist for this query (first result).
    NoAnswers,
    /// No more answers remain (query exhausted).
    Exhausted,
    /// Resource limit reached before completion.
    ResourceLimit,
}

/// Policy for projecting internal symbols from user-visible answers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProjectionPolicy {
    /// Only allow symbols from the user signature to appear in answers.
    OnlyUserSymbols,
    /// Allow internal symbols (e.g., Skolem/Tseitin) in answers.
    AllowInternal,
}

/// Streaming query evaluation state.
#[derive(Debug, Clone)]
pub struct QueryStream {
    theory: Theory,
    query: Query,
    config: DerivationConfig,
    user_signature: Option<Signature>,
    policy: ProjectionPolicy,
    seen_answer: bool,
    exhausted: bool,
}

impl QueryStream {
    pub fn new(
        theory: Theory,
        query: Query,
        config: DerivationConfig,
        user_signature: Option<Signature>,
        policy: ProjectionPolicy,
    ) -> Self {
        QueryStream {
            theory,
            query,
            config,
            user_signature,
            policy,
            seen_answer: false,
            exhausted: false,
        }
    }

    /// Retrieve the next answer in the stream.
    pub fn next(&mut self) -> QueryResult {
        if self.exhausted {
            return QueryResult::Exhausted;
        }
        todo!("QueryStream::next implementation")
    }
}

/// Answer a query against a theory using SGGS model construction.
///
/// Semantics: build (or approximate) a model with SGGS, then return substitutions
/// that make the query true in that model.
pub fn answer_query(theory: &Theory, query: &Query, config: DerivationConfig) -> QueryStream {
    QueryStream::new(
        theory.clone(),
        query.clone(),
        config,
        None,
        ProjectionPolicy::OnlyUserSymbols,
    )
}

/// Answer a query and project substitutions to a user signature.
pub fn answer_query_projected(
    theory: &Theory,
    query: &Query,
    config: DerivationConfig,
    user_signature: &Signature,
    policy: ProjectionPolicy,
) -> QueryStream {
    QueryStream::new(
        theory.clone(),
        query.clone(),
        config,
        Some(user_signature.clone()),
        policy,
    )
}
