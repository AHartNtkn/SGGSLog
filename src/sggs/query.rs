//! Query answering for SGGSLog.

use super::DerivationConfig;
use crate::syntax::{Clause, Query, UserSignature, Var};
use crate::theory::Theory;
use crate::unify::Substitution;

/// Result of answering a query (model-based).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QueryResult {
    /// A single answer (substitution) was found.
    Answer(Substitution),
    /// No more answers remain (query exhausted).
    Exhausted,
    /// Timeout reached before completion.
    Timeout,
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
    user_signature: Option<UserSignature>,
    policy: ProjectionPolicy,
    seen_answer: bool,
    exhausted: bool,
}

impl QueryStream {
    pub fn new(
        theory: Theory,
        query: Query,
        config: DerivationConfig,
        user_signature: Option<UserSignature>,
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
    user_signature: &UserSignature,
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
