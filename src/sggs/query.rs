//! Query answering for SGGSLog.

use super::{derive, DerivationConfig, DerivationResult};
use crate::syntax::{Atom, Literal, Query, Term, UserSignature, Var};
use crate::theory::Theory;
use crate::unify::{unify_literals, Substitution, UnifyResult};
use std::collections::HashSet;

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
    #[allow(dead_code)]
    query: Query,
    #[allow(dead_code)]
    user_signature: Option<UserSignature>,
    #[allow(dead_code)]
    policy: ProjectionPolicy,
    /// Pre-computed answers from the derivation
    answers: Vec<Substitution>,
    /// Index of next answer to return
    next_idx: usize,
    /// Whether derivation timed out
    timed_out: bool,
}

impl QueryStream {
    pub fn new(
        theory: Theory,
        query: Query,
        config: DerivationConfig,
        user_signature: Option<UserSignature>,
        policy: ProjectionPolicy,
    ) -> Self {
        // Run the derivation to get a model
        let derivation_result = derive(&theory, config);

        let (answers, timed_out) = match derivation_result {
            DerivationResult::Timeout => (Vec::new(), true),
            DerivationResult::Unsatisfiable => {
                // Theory is unsatisfiable - no model exists
                (Vec::new(), false)
            }
            DerivationResult::Satisfiable(model) => {
                // Extract answers from the model (ground atoms and non-ground patterns)
                let answers = extract_answers(
                    &query,
                    &model.true_atoms,
                    &model.true_patterns,
                    user_signature.as_ref(),
                    policy,
                );
                (answers, false)
            }
        };

        QueryStream {
            query,
            user_signature,
            policy,
            answers,
            next_idx: 0,
            timed_out,
        }
    }

    /// Retrieve the next answer in the stream.
    pub fn next_answer(&mut self) -> QueryResult {
        if self.next_idx < self.answers.len() {
            let ans = self.answers[self.next_idx].clone();
            self.next_idx += 1;
            QueryResult::Answer(ans)
        } else if self.timed_out && self.next_idx == 0 {
            self.timed_out = false; // Only report timeout once
            QueryResult::Timeout
        } else {
            QueryResult::Exhausted
        }
    }
}

/// Extract answers by finding substitutions that make the query true in the model.
fn extract_answers(
    query: &Query,
    true_atoms: &HashSet<Atom>,
    true_patterns: &[Literal],
    user_signature: Option<&UserSignature>,
    policy: ProjectionPolicy,
) -> Vec<Substitution> {
    let query_vars: HashSet<Var> = query.variables();

    // For a single-literal query, find all matching atoms and patterns
    if query.literals.len() == 1 {
        let query_lit = &query.literals[0];

        // Handle negative queries
        if !query_lit.positive {
            return extract_negative_answers(
                query_lit,
                &query_vars,
                true_atoms,
                true_patterns,
                user_signature,
                policy,
            );
        }

        let mut answers = Vec::new();
        let mut seen_answers: HashSet<Vec<(Var, Term)>> = HashSet::new();

        // Check ground atoms
        for atom in true_atoms {
            let model_lit = Literal {
                positive: true,
                atom: atom.clone(),
            };

            if let UnifyResult::Success(sigma) = unify_literals(query_lit, &model_lit) {
                let projected = project_substitution(&sigma, &query_vars, user_signature, policy);

                // Only include answer if all query variables are bound to projectable terms
                // If a query variable is bound but filtered out, skip this answer
                let orig_bound_vars: HashSet<_> = sigma
                    .bindings()
                    .filter(|(v, _)| query_vars.contains(*v))
                    .map(|(v, _)| v.clone())
                    .collect();
                let proj_bound_vars: HashSet<_> =
                    projected.bindings().map(|(v, _)| v.clone()).collect();

                // If we lost bindings due to projection, skip this answer
                if proj_bound_vars.len() < orig_bound_vars.len() {
                    continue;
                }

                let canonical = canonical_form(&projected);
                if !seen_answers.contains(&canonical) {
                    seen_answers.insert(canonical);
                    answers.push(projected);
                }
            }
        }

        // Check non-ground patterns (these represent all instances)
        for pattern in true_patterns {
            if !pattern.positive {
                continue;
            }

            // Rename pattern variables to avoid clashes with query variables
            let renamed = rename_away_from(pattern, &query_vars);

            if let UnifyResult::Success(sigma) = unify_literals(query_lit, &renamed) {
                let projected = project_substitution(&sigma, &query_vars, user_signature, policy);

                // Only include answer if all query variables are bound to projectable terms
                let orig_bound_vars: HashSet<_> = sigma
                    .bindings()
                    .filter(|(v, _)| query_vars.contains(*v))
                    .map(|(v, _)| v.clone())
                    .collect();
                let proj_bound_vars: HashSet<_> =
                    projected.bindings().map(|(v, _)| v.clone()).collect();

                if proj_bound_vars.len() < orig_bound_vars.len() {
                    continue;
                }

                let canonical = canonical_form(&projected);
                if !seen_answers.contains(&canonical) {
                    seen_answers.insert(canonical);
                    answers.push(projected);
                }
            }
        }
        return answers;
    }

    // For multi-literal queries, find substitutions that satisfy all literals
    let mut answers = Vec::new();
    find_multi_literal_answers(
        &query.literals,
        true_atoms,
        Substitution::empty(),
        &query_vars,
        user_signature,
        policy,
        &mut answers,
        &mut HashSet::new(),
    );
    answers
}

/// Extract answers for a single negative literal query.
///
/// A negative literal ¬p(t) is true if p(t) is NOT in the model.
/// For ground queries, we check if the atom is absent.
/// For queries with variables, we enumerate over the user signature.
fn extract_negative_answers(
    query_lit: &Literal,
    query_vars: &HashSet<Var>,
    true_atoms: &HashSet<Atom>,
    true_patterns: &[Literal],
    user_signature: Option<&UserSignature>,
    policy: ProjectionPolicy,
) -> Vec<Substitution> {
    let mut answers = Vec::new();
    let mut seen_answers: HashSet<Vec<(Var, Term)>> = HashSet::new();

    // If the query is ground, simply check if the atom is absent from the model
    if query_lit.is_ground() {
        // Check if atom is in true_atoms
        if !true_atoms.contains(&query_lit.atom) {
            // Also check if any pattern covers this atom
            let covered_by_pattern = true_patterns.iter().any(|pattern| {
                if !pattern.positive || pattern.atom.predicate != query_lit.atom.predicate {
                    return false;
                }
                // Check if the query atom is an instance of the pattern
                let query_as_pos = Literal {
                    positive: true,
                    atom: query_lit.atom.clone(),
                };
                matches!(
                    unify_literals(&query_as_pos, pattern),
                    UnifyResult::Success(_)
                )
            });

            if !covered_by_pattern {
                // Atom is absent from model - query is satisfied
                answers.push(Substitution::empty());
            }
        }
        return answers;
    }

    // Non-ground negative query - enumerate over user signature constants
    if let Some(sig) = user_signature {
        let constants: Vec<Term> = sig
            .signature()
            .functions
            .iter()
            .filter(|fn_sig| fn_sig.arity == 0)
            .map(|fn_sig| Term::constant(&fn_sig.name))
            .collect();

        // Generate all possible ground instances using constants
        let vars: Vec<Var> = query_vars.iter().cloned().collect();
        let candidates = generate_ground_instances(&vars, &constants);

        for subst in candidates {
            let grounded_lit = query_lit.apply_subst(&subst);

            // Check if this ground negative literal is true (atom NOT in model)
            if !true_atoms.contains(&grounded_lit.atom) {
                // Also check patterns
                let covered_by_pattern = true_patterns.iter().any(|pattern| {
                    if !pattern.positive || pattern.atom.predicate != grounded_lit.atom.predicate {
                        return false;
                    }
                    let grounded_as_pos = Literal {
                        positive: true,
                        atom: grounded_lit.atom.clone(),
                    };
                    matches!(
                        unify_literals(&grounded_as_pos, pattern),
                        UnifyResult::Success(_)
                    )
                });

                if !covered_by_pattern {
                    let projected =
                        project_substitution(&subst, query_vars, user_signature, policy);
                    let canonical = canonical_form(&projected);
                    if !seen_answers.contains(&canonical) {
                        seen_answers.insert(canonical);
                        answers.push(projected);
                    }
                }
            }
        }
    }

    answers
}

/// Generate all ground instances by binding variables to constants.
fn generate_ground_instances(vars: &[Var], constants: &[Term]) -> Vec<Substitution> {
    if vars.is_empty() {
        return vec![Substitution::empty()];
    }
    if constants.is_empty() {
        return vec![];
    }

    let mut results = Vec::new();
    let first_var = &vars[0];
    let rest_vars = &vars[1..];

    for constant in constants {
        let sub_results = generate_ground_instances(rest_vars, constants);
        for mut sub in sub_results {
            sub.bind(first_var.clone(), constant.clone());
            results.push(sub);
        }
    }

    results
}

/// Recursively find substitutions that satisfy all query literals.
fn find_multi_literal_answers(
    remaining: &[Literal],
    true_atoms: &HashSet<Atom>,
    current_subst: Substitution,
    query_vars: &HashSet<Var>,
    user_signature: Option<&UserSignature>,
    policy: ProjectionPolicy,
    answers: &mut Vec<Substitution>,
    seen: &mut HashSet<Vec<(Var, Term)>>,
) {
    if remaining.is_empty() {
        // All literals satisfied - this is an answer
        let projected = project_substitution(&current_subst, query_vars, user_signature, policy);
        let canonical: Vec<(Var, Term)> = {
            let mut pairs: Vec<_> = projected.bindings().collect();
            pairs.sort_by(|a, b| a.0.name().cmp(b.0.name()));
            pairs
                .into_iter()
                .map(|(v, t)| (v.clone(), t.clone()))
                .collect()
        };
        if !seen.contains(&canonical) {
            seen.insert(canonical);
            answers.push(projected);
        }
        return;
    }

    let query_lit = &remaining[0];
    let rest = &remaining[1..];

    // Apply current substitution to query literal
    let instantiated = query_lit.apply_subst(&current_subst);

    if !instantiated.positive {
        // Negative literal - check if the atom is NOT in the model
        if !true_atoms.contains(&instantiated.atom) {
            find_multi_literal_answers(
                rest,
                true_atoms,
                current_subst,
                query_vars,
                user_signature,
                policy,
                answers,
                seen,
            );
        }
        return;
    }

    // Positive literal - find matching atoms
    for atom in true_atoms {
        let model_lit = Literal {
            positive: true,
            atom: atom.clone(),
        };

        if let UnifyResult::Success(sigma) = unify_literals(&instantiated, &model_lit) {
            // Compose substitutions
            let combined = current_subst.compose(&sigma);
            find_multi_literal_answers(
                rest,
                true_atoms,
                combined,
                query_vars,
                user_signature,
                policy,
                answers,
                seen,
            );
        }
    }
}

/// Project a substitution to only the specified variables, respecting projection policy.
fn project_substitution(
    subst: &Substitution,
    vars: &HashSet<Var>,
    user_signature: Option<&UserSignature>,
    policy: ProjectionPolicy,
) -> Substitution {
    let mut projected = Substitution::empty();

    for (v, t) in subst.bindings() {
        if vars.contains(v) {
            // Check if term uses only allowed symbols
            match policy {
                ProjectionPolicy::AllowInternal => {
                    projected.bind(v.clone(), t.clone());
                }
                ProjectionPolicy::OnlyUserSymbols => {
                    if let Some(sig) = user_signature {
                        if term_uses_only_user_symbols(t, sig) {
                            projected.bind(v.clone(), t.clone());
                        }
                        // If term uses internal symbols, we don't include this binding
                    } else {
                        // No user signature - include all answers
                        projected.bind(v.clone(), t.clone());
                    }
                }
            }
        }
    }

    projected
}

/// Check if a term only uses symbols from the user signature.
///
/// A term uses only user symbols if every function symbol (including constants)
/// appearing in the term is explicitly in the user signature.
fn term_uses_only_user_symbols(term: &Term, sig: &UserSignature) -> bool {
    match term {
        Term::Var(_) => true,
        Term::App(sym, args) => {
            // Check if this function symbol is explicitly in the user signature
            if !sig.contains_function(&sym.name, sym.arity) {
                return false;
            }
            // Recursively check arguments
            args.iter().all(|arg| term_uses_only_user_symbols(arg, sig))
        }
    }
}

/// Convert a substitution to a canonical form for deduplication.
fn canonical_form(subst: &Substitution) -> Vec<(Var, Term)> {
    let mut pairs: Vec<_> = subst.bindings().collect();
    pairs.sort_by(|a, b| a.0.name().cmp(b.0.name()));
    pairs
        .into_iter()
        .map(|(v, t)| (v.clone(), t.clone()))
        .collect()
}

/// Rename variables in a literal to avoid clashing with the given variable set.
fn rename_away_from(lit: &Literal, avoid: &HashSet<Var>) -> Literal {
    let lit_vars = lit.variables();
    let mut renaming = Substitution::empty();
    let mut counter = 0;

    for v in lit_vars {
        if avoid.contains(&v) {
            // Find a fresh variable name
            loop {
                let fresh_name = format!("_r{}", counter);
                counter += 1;
                let fresh_var = Var::new(&fresh_name);
                if !avoid.contains(&fresh_var)
                    && !renaming.domain().iter().any(|rv| rv.name() == fresh_name)
                {
                    renaming.bind(v.clone(), Term::Var(fresh_var));
                    break;
                }
            }
        }
    }

    lit.apply_subst(&renaming)
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
