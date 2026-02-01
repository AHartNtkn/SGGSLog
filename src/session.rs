//! Session: end-to-end API for loading theories and answering queries.

use crate::normalize::{clausify_statement, clausify_statements};
use crate::parser::{parse_file, Directive, ProjectionSetting, Setting, Statement};
use crate::sggs::{
    answer_query_projected, DerivationConfig, ProjectionPolicy, Query, QueryResult, QueryStream,
};
use crate::syntax::{Literal, UserSignature};
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
    Set(Setting),
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
    user_signature: UserSignature,
    projection_policy: ProjectionPolicy,
    active_query: Option<QueryStream>,
}

/// Default timeout for derivations (5 seconds).
const DEFAULT_TIMEOUT_MS: u64 = 5000;

impl Session {
    /// Create a new empty session.
    pub fn new() -> Self {
        Session {
            theory: Theory::new(),
            config: DerivationConfig {
                timeout_ms: Some(DEFAULT_TIMEOUT_MS),
                ..DerivationConfig::default()
            },
            user_signature: UserSignature::empty(),
            projection_policy: ProjectionPolicy::OnlyUserSymbols,
            active_query: None,
        }
    }

    /// Create a session with the given configuration.
    pub fn with_config(config: DerivationConfig) -> Self {
        Session {
            theory: Theory::new(),
            config,
            user_signature: UserSignature::empty(),
            projection_policy: ProjectionPolicy::OnlyUserSymbols,
            active_query: None,
        }
    }

    /// Execute a parsed statement.
    pub fn execute_statement(&mut self, stmt: Statement) -> Result<ExecResult, SessionError> {
        match stmt {
            Statement::Clause(clause) => {
                // Track user signature from the clause before adding
                self.user_signature.extend_from_clause(&clause);
                self.theory.add_clause(clause);
                Ok(ExecResult::ClauseAdded)
            }
            Statement::Formula(formula) => {
                // Track user signature from the formula before clausifying
                self.user_signature.extend_from_formula(&formula);
                let clauses =
                    clausify_statement(&Statement::Formula(formula)).map_err(|e| SessionError {
                        message: e.to_string(),
                    })?;
                for clause in clauses {
                    self.theory.add_clause(clause);
                }
                Ok(ExecResult::ClauseAdded)
            }
            Statement::Query(query) => {
                let result = self.execute_query(query.literals.clone());
                Ok(ExecResult::QueryResult(result))
            }
            Statement::Directive(directive) => {
                match directive {
                    Directive::Next => {
                        // Get next answer from active query
                        let result = self.next_answer()?;
                        Ok(ExecResult::QueryResult(result))
                    }
                    _ => {
                        let result = self.apply_directive(directive)?;
                        Ok(ExecResult::DirectiveApplied(result))
                    }
                }
            }
        }
    }

    /// Execute a query (list of literals).
    pub fn execute_query(&mut self, lits: Vec<Literal>) -> QueryResult {
        let query = Query::new(lits);
        let stream = answer_query_projected(
            &self.theory,
            &query,
            self.config.clone(),
            &self.user_signature,
            self.projection_policy,
        );
        self.active_query = Some(stream);
        // Call next_answer on the stored stream
        self.active_query.as_mut().unwrap().next_answer()
    }

    /// Load a file and add all its clauses to the theory.
    pub fn load_file(&mut self, path: &str) -> Result<DirectiveResult, SessionError> {
        let contents = std::fs::read_to_string(path).map_err(|e| SessionError {
            message: format!("Failed to read file '{}': {}", path, e),
        })?;
        let stmts = parse_file(&contents).map_err(|e| SessionError {
            message: format!("Parse error: {}", e),
        })?;

        // Validate that file contains only clauses/formulas, not queries/directives
        for stmt in &stmts {
            match stmt {
                Statement::Query(_) => {
                    return Err(SessionError {
                        message: "Cannot load file containing queries".to_string(),
                    });
                }
                Statement::Directive(_) => {
                    return Err(SessionError {
                        message: "Cannot load file containing directives".to_string(),
                    });
                }
                _ => {}
            }
        }

        // Track user signatures and clausify
        for stmt in &stmts {
            match stmt {
                Statement::Clause(clause) => {
                    self.user_signature.extend_from_clause(clause);
                }
                Statement::Formula(formula) => {
                    self.user_signature.extend_from_formula(formula);
                }
                _ => {}
            }
        }

        let clauses = clausify_statements(&stmts).map_err(|e| SessionError {
            message: e.to_string(),
        })?;
        let clause_count = clauses.len();
        for clause in clauses {
            self.theory.add_clause(clause);
        }

        Ok(DirectiveResult::Loaded {
            path: path.to_string(),
            clauses: clause_count,
        })
    }

    /// Apply a directive.
    pub fn apply_directive(
        &mut self,
        directive: Directive,
    ) -> Result<DirectiveResult, SessionError> {
        match directive {
            Directive::Load(path) => self.load_file(&path),
            Directive::Set(setting) => self.apply_setting(setting),
            Directive::Next => {
                // Return the next answer from the active query
                if let Some(ref mut stream) = self.active_query {
                    let _result = stream.next_answer();
                    // Return as a DirectiveResult - we'll need to wrap it
                    // For now, we return an error since DirectiveResult doesn't handle query results
                    Err(SessionError {
                        message: "Use execute_statement with Query for query results".to_string(),
                    })
                } else {
                    Err(SessionError {
                        message: "No active query".to_string(),
                    })
                }
            }
            Directive::Quit => {
                // Quit is typically handled by the REPL, not the session
                Err(SessionError {
                    message: "Quit directive should be handled by REPL".to_string(),
                })
            }
        }
    }

    /// Get the next answer from the active query stream.
    pub fn next_answer(&mut self) -> Result<QueryResult, SessionError> {
        if let Some(ref mut stream) = self.active_query {
            Ok(stream.next_answer())
        } else {
            Err(SessionError {
                message: "No active query".to_string(),
            })
        }
    }

    /// Update the configuration from a key/value pair.
    pub fn apply_setting(&mut self, setting: Setting) -> Result<DirectiveResult, SessionError> {
        match &setting {
            Setting::TimeoutMs(ms) => {
                self.config.timeout_ms = Some(*ms);
            }
            Setting::Projection(proj_setting) => {
                self.projection_policy = match proj_setting {
                    ProjectionSetting::OnlyUserSymbols => ProjectionPolicy::OnlyUserSymbols,
                    ProjectionSetting::AllowInternal => ProjectionPolicy::AllowInternal,
                };
            }
            Setting::Unknown { key, value } => {
                // Handle known settings that might be in Unknown form
                use crate::sggs::InitialInterpretation;
                if key == "initial_interpretation" || key == "interpretation" {
                    let interp = match value.as_str() {
                        "positive" | "+" => InitialInterpretation::AllPositive,
                        "negative" | "-" => InitialInterpretation::AllNegative,
                        _ => {
                            return Err(SessionError {
                                message: format!("Unknown initial interpretation: {}", value),
                            });
                        }
                    };
                    self.config.initial_interp = interp;
                } else {
                    return Err(SessionError {
                        message: format!("Unknown setting: {} = {}", key, value),
                    });
                }
            }
        }
        Ok(DirectiveResult::Set(setting))
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
    pub fn user_signature(&self) -> &UserSignature {
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
