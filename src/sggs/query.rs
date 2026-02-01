//! Query answering for SGGSLog.

use super::{DerivationConfig, DerivationResult, DerivationState};
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
///
/// Answers are generated lazily as derivation progresses, allowing
/// infinite answer sets to be enumerated incrementally.
pub struct QueryStream {
    query: Query,
    user_signature: Option<UserSignature>,
    policy: ProjectionPolicy,
    /// The derivation state (None if derivation is complete)
    derivation: Option<DerivationState>,
    /// Answers already seen (for deduplication)
    seen_answers: HashSet<Vec<(Var, Term)>>,
    /// Pending answers found but not yet returned
    pending_answers: Vec<Substitution>,
    /// Final result if derivation completed
    final_result: Option<DerivationResult>,
    /// Number of derivation steps taken
    steps_taken: usize,
    /// Minimum steps before extracting answers (allows conflict detection)
    min_steps: usize,
}

impl QueryStream {
    pub fn new(
        theory: Theory,
        query: Query,
        config: DerivationConfig,
        user_signature: Option<UserSignature>,
        policy: ProjectionPolicy,
    ) -> Self {
        // Run at least 2*|theory| steps before extracting answers
        // This gives time for all clauses to be extended and conflicts to be detected
        let min_steps = 2 * theory.clauses().len().max(1);
        let derivation = DerivationState::new(theory, config);

        QueryStream {
            query,
            user_signature,
            policy,
            derivation: Some(derivation),
            seen_answers: HashSet::new(),
            pending_answers: Vec::new(),
            final_result: None,
            steps_taken: 0,
            min_steps,
        }
    }

    /// Retrieve the next answer in the stream.
    ///
    /// This runs derivation incrementally until a new answer is found,
    /// the derivation completes, or a timeout is reached.
    pub fn next_answer(&mut self) -> QueryResult {
        // Return pending answer if available
        if let Some(ans) = self.pending_answers.pop() {
            return QueryResult::Answer(ans);
        }

        // If derivation is done, check final result
        if self.derivation.is_none() {
            return match &self.final_result {
                Some(DerivationResult::Timeout) => QueryResult::Timeout,
                _ => QueryResult::Exhausted,
            };
        }

        // Run derivation steps until we find a new answer or complete
        loop {
            // Only extract answers after minimum warmup steps
            // This gives time for conflicts to be detected in unsatisfiable theories
            if self.steps_taken >= self.min_steps {
                self.extract_new_answers();

                // Return if we found any
                if let Some(ans) = self.pending_answers.pop() {
                    return QueryResult::Answer(ans);
                }
            }

            // Try to advance derivation
            let derivation = self.derivation.as_mut().unwrap();
            match derivation.step() {
                Some(_step) => {
                    self.steps_taken += 1;
                    // Derivation made progress, loop to check for new answers
                    continue;
                }
                None => {
                    // Derivation cannot proceed - check result
                    self.final_result = derivation.result().cloned();
                    self.derivation = None;

                    // One final extraction from the complete trail
                    // (already done above, but result tells us outcome)
                    return match &self.final_result {
                        Some(DerivationResult::Timeout) => QueryResult::Timeout,
                        Some(DerivationResult::Unsatisfiable) => QueryResult::Exhausted,
                        Some(DerivationResult::Satisfiable(_)) => QueryResult::Exhausted,
                        None => QueryResult::Exhausted,
                    };
                }
            }
        }
    }

    /// Extract new answers from the current trail state.
    fn extract_new_answers(&mut self) {
        let Some(derivation) = &self.derivation else {
            return;
        };

        let trail = derivation.trail();

        // Don't extract answers if there's a conflict on the trail.
        // Conflicts indicate potential unsatisfiability - we should wait until
        // the conflict is resolved before returning any answers.
        if trail.find_conflict().is_some() {
            return;
        }

        let init_interp = trail.initial_interpretation();
        let query_vars: HashSet<Var> = self.query.variables();

        // For single-literal positive queries, match against I-false selected literals
        // (those are the ones made true by the trail)
        if self.query.literals.len() == 1 && self.query.literals[0].positive {
            let query_lit = &self.query.literals[0];

            for clause in trail.clauses() {
                let selected = clause.selected_literal();

                // I-false selected literals contribute to the model
                if !init_interp.is_false(selected) || !selected.positive {
                    continue;
                }

                // Must have same predicate
                if selected.atom.predicate != query_lit.atom.predicate {
                    continue;
                }

                // Try to unify
                if let UnifyResult::Success(sigma) = unify_literals(query_lit, selected) {
                    let projected = project_substitution(
                        &sigma,
                        &query_vars,
                        self.user_signature.as_ref(),
                        self.policy,
                    );

                    // Check projection didn't lose required bindings
                    let orig_bound: HashSet<_> = sigma
                        .bindings()
                        .filter(|(v, _)| query_vars.contains(*v))
                        .map(|(v, _)| v.clone())
                        .collect();
                    let proj_bound: HashSet<_> =
                        projected.bindings().map(|(v, _)| v.clone()).collect();

                    if proj_bound.len() < orig_bound.len() {
                        continue;
                    }

                    let canonical = canonical_form(&projected);
                    if self.seen_answers.insert(canonical) {
                        self.pending_answers.push(projected);
                    }
                }
            }
        }
        // TODO: Handle negative queries and multi-literal queries incrementally
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

