//! Session: end-to-end API for loading theories and answering queries.

use crate::normalize::{clausify_statement, clausify_statements};
use crate::parser::{parse_file, Directive, Statement};
use crate::sggs::{
    answer_query, answer_query_projected, DerivationConfig, ProjectionPolicy, Query, QueryResult,
    QueryStream,
};
use crate::syntax::{Literal, Signature};
use crate::theory::Theory;

/// Result of executing a statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExecResult {
    ClauseAdded,
    QueryResult(QueryResult),
    DirectiveApplied(DirectiveResult),
}

/// Result of applying a directive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DirectiveResult {
    Loaded { path: String, clauses: usize },
    Set { key: String, value: String },
}

/// Session error.
#[derive(Debug, Clone)]
pub struct SessionError {
    pub message: String,
}

impl std::fmt::Display for SessionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for SessionError {}

/// A session holds the current theory and solver configuration.
pub struct Session {
    theory: Theory,
    config: DerivationConfig,
    user_signature: Signature,
    projection_policy: ProjectionPolicy,
    active_query: Option<QueryStream>,
}

impl Session {
    /// Create a new empty session.
    pub fn new() -> Self {
        todo!("Session::new implementation")
    }

    /// Create a session with the given configuration.
    pub fn with_config(_config: DerivationConfig) -> Self {
        todo!("Session::with_config implementation")
    }

    /// Execute a parsed statement.
    pub fn execute_statement(&mut self, _stmt: Statement) -> Result<ExecResult, SessionError> {
        todo!("Session::execute_statement implementation")
    }

    /// Execute a query (list of literals).
    pub fn execute_query(&mut self, _lits: Vec<Literal>) -> QueryResult {
        todo!("Session::execute_query implementation")
    }

    /// Load a file and add all its clauses to the theory.
    pub fn load_file(&mut self, _path: &str) -> Result<DirectiveResult, SessionError> {
        todo!("Session::load_file implementation")
    }

    /// Apply a directive.
    pub fn apply_directive(
        &mut self,
        _directive: Directive,
    ) -> Result<DirectiveResult, SessionError> {
        todo!("Session::apply_directive implementation")
    }

    /// Update the configuration from a key/value pair.
    pub fn set_option(
        &mut self,
        _key: &str,
        _value: &str,
    ) -> Result<DirectiveResult, SessionError> {
        todo!("Session::set_option implementation")
    }

    /// Access the current theory.
    pub fn theory(&self) -> &Theory {
        &self.theory
    }

    /// Access the current configuration.
    pub fn config(&self) -> &DerivationConfig {
        &self.config
    }

    /// Signature of user-provided symbols (pre-normalization).
    pub fn user_signature(&self) -> &Signature {
        &self.user_signature
    }

    /// Projection policy for user-visible answers.
    pub fn projection_policy(&self) -> ProjectionPolicy {
        self.projection_policy
    }
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}
