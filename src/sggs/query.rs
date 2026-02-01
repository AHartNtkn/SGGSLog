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
                    // Derivation complete - check result
                    self.final_result = derivation.result().cloned();

                    // For satisfiable theories, do one final extraction before clearing derivation
                    if matches!(self.final_result, Some(DerivationResult::Satisfiable(_))) {
                        self.extract_new_answers();
                    }

                    self.derivation = None;

                    // Return pending answer if we found one
                    if let Some(ans) = self.pending_answers.pop() {
                        return QueryResult::Answer(ans);
                    }

                    // Otherwise return based on final result
                    return match &self.final_result {
                        Some(DerivationResult::Timeout) => QueryResult::Timeout,
                        _ => QueryResult::Exhausted,
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

        // Build the set of true atoms and patterns from the trail.
        // I-false selected positive literals are made true by the trail.
        let mut true_atoms: HashSet<Atom> = HashSet::new();
        let mut true_patterns: Vec<Literal> = Vec::new();

        for clause in trail.clauses() {
            let selected = clause.selected_literal();
            // I-false selected positive literals contribute to the model
            if init_interp.is_false(selected) && selected.positive {
                if selected.is_ground() {
                    true_atoms.insert(selected.atom.clone());
                } else {
                    true_patterns.push(selected.clone());
                }
            }
        }

        // Handle single-literal queries
        if self.query.literals.len() == 1 {
            let query_lit = self.query.literals[0].clone();

            if query_lit.positive {
                // Positive query - match against true atoms/patterns
                self.extract_positive_single_literal(&query_lit, &true_atoms, &true_patterns, &query_vars);
            } else {
                // Negative query - check for absence from model
                self.extract_negative_single_literal(&query_lit, &true_atoms, &true_patterns, &query_vars);
            }
            return;
        }

        // Handle multi-literal (conjunctive) queries
        self.extract_multi_literal(&true_atoms, &query_vars);
    }

    /// Extract answers for a single positive literal query.
    fn extract_positive_single_literal(
        &mut self,
        query_lit: &Literal,
        true_atoms: &HashSet<Atom>,
        true_patterns: &[Literal],
        query_vars: &HashSet<Var>,
    ) {
        // Check ground atoms
        for atom in true_atoms {
            if atom.predicate != query_lit.atom.predicate {
                continue;
            }

            let model_lit = Literal {
                positive: true,
                atom: atom.clone(),
            };

            if let UnifyResult::Success(sigma) = unify_literals(query_lit, &model_lit) {
                self.add_answer_if_new(&sigma, query_vars);
            }
        }

        // Check non-ground patterns
        for pattern in true_patterns {
            if !pattern.positive || pattern.atom.predicate != query_lit.atom.predicate {
                continue;
            }

            // Rename pattern variables to avoid clashes with query variables
            let renamed = rename_away_from(pattern, query_vars);

            if let UnifyResult::Success(sigma) = unify_literals(query_lit, &renamed) {
                self.add_answer_if_new(&sigma, query_vars);
            }
        }
    }

    /// Extract answers for a single negative literal query.
    fn extract_negative_single_literal(
        &mut self,
        query_lit: &Literal,
        true_atoms: &HashSet<Atom>,
        true_patterns: &[Literal],
        query_vars: &HashSet<Var>,
    ) {
        // If the query is ground, check if the atom is absent from the model
        if query_lit.is_ground() {
            // Check if atom is in true_atoms
            if !true_atoms.contains(&query_lit.atom) {
                // Also check if any pattern covers this atom
                let covered_by_pattern = true_patterns.iter().any(|pattern| {
                    if !pattern.positive || pattern.atom.predicate != query_lit.atom.predicate {
                        return false;
                    }
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
                    self.add_answer_if_new(&Substitution::empty(), query_vars);
                }
            }
            return;
        }

        // Non-ground negative query - enumerate over user signature constants
        if let Some(sig) = &self.user_signature {
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
                        self.add_answer_if_new(&subst, query_vars);
                    }
                }
            }
        }
    }

    /// Extract answers for multi-literal (conjunctive) queries.
    fn extract_multi_literal(&mut self, true_atoms: &HashSet<Atom>, query_vars: &HashSet<Var>) {
        let mut new_answers = Vec::new();
        let mut seen_in_search: HashSet<Vec<(Var, Term)>> = HashSet::new();

        self.find_multi_literal_answers_incremental(
            &self.query.literals.clone(),
            true_atoms,
            Substitution::empty(),
            query_vars,
            &mut new_answers,
            &mut seen_in_search,
        );

        for ans in new_answers {
            let canonical = canonical_form(&ans);
            if self.seen_answers.insert(canonical) {
                self.pending_answers.push(ans);
            }
        }
    }

    /// Recursively find substitutions that satisfy all query literals.
    fn find_multi_literal_answers_incremental(
        &self,
        remaining: &[Literal],
        true_atoms: &HashSet<Atom>,
        current_subst: Substitution,
        query_vars: &HashSet<Var>,
        answers: &mut Vec<Substitution>,
        seen: &mut HashSet<Vec<(Var, Term)>>,
    ) {
        if remaining.is_empty() {
            // All literals satisfied - this is an answer
            let projected = project_substitution(
                &current_subst,
                query_vars,
                self.user_signature.as_ref(),
                self.policy,
            );
            let canonical = canonical_form(&projected);
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
                self.find_multi_literal_answers_incremental(
                    rest,
                    true_atoms,
                    current_subst,
                    query_vars,
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
                self.find_multi_literal_answers_incremental(
                    rest,
                    true_atoms,
                    combined,
                    query_vars,
                    answers,
                    seen,
                );
            }
        }
    }

    /// Add an answer if it's new (not seen before).
    fn add_answer_if_new(&mut self, sigma: &Substitution, query_vars: &HashSet<Var>) {
        let projected = project_substitution(
            sigma,
            query_vars,
            self.user_signature.as_ref(),
            self.policy,
        );

        // Check projection didn't lose required bindings
        let orig_bound: HashSet<_> = sigma
            .bindings()
            .filter(|(v, _)| query_vars.contains(*v))
            .map(|(v, _)| v.clone())
            .collect();
        let proj_bound: HashSet<_> = projected.bindings().map(|(v, _)| v.clone()).collect();

        if proj_bound.len() < orig_bound.len() {
            return;
        }

        let canonical = canonical_form(&projected);
        if self.seen_answers.insert(canonical) {
            self.pending_answers.push(projected);
        }
    }
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

