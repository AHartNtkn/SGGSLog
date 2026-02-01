//! Query answering for SGGSLog.

use super::{DerivationConfig, DerivationResult, DerivationState};
use crate::syntax::{Atom, Literal, Query, Term, UserSignature, Var};
use crate::theory::Theory;
use crate::unify::{unify_literals, Substitution, UnifyResult};
use std::collections::{HashSet, VecDeque};

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

/// Snapshot statistics for a query stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QueryStats {
    pub pending_answers: usize,
    pub seen_answers: usize,
    pub steps_taken: usize,
    pub derivation_done: bool,
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
    /// Final result if derivation completed
    final_result: Option<DerivationResult>,
    /// Number of derivation steps taken
    steps_taken: usize,
    /// Cursor for incremental extraction: index of next clause to check
    extraction_cursor: usize,
    /// Pending candidate literals to try matching (for cursor-based extraction)
    pending_candidates: VecDeque<Literal>,
    /// Number of derivation steps since last extraction.
    /// We require at least `theory_size` steps before first extraction to ensure
    /// all theory clauses have a chance to be extended and conflicts detected.
    steps_since_extraction: usize,
    /// Number of clauses in the theory (used to determine warmup period).
    theory_size: usize,
}

impl QueryStream {
    pub fn new(
        theory: Theory,
        query: Query,
        config: DerivationConfig,
        user_signature: Option<UserSignature>,
        policy: ProjectionPolicy,
    ) -> Self {
        let theory_size = theory.clauses().len();
        let derivation = DerivationState::new(theory, config);
        // Start cursor at initial trail length - only extract from clauses added
        // AFTER derivation starts, ensuring conflict detection runs first
        let initial_trail_len = derivation.trail().clauses().len();

        QueryStream {
            query,
            user_signature,
            policy,
            derivation: Some(derivation),
            seen_answers: HashSet::new(),
            final_result: None,
            steps_taken: 0,
            extraction_cursor: initial_trail_len,
            pending_candidates: VecDeque::new(),
            steps_since_extraction: 0,
            theory_size,
        }
    }

    /// Retrieve the next answer in the stream.
    ///
    /// This runs derivation incrementally until a new answer is found,
    /// the derivation completes, or a timeout is reached.
    ///
    /// Each call resets the timeout budget, allowing per-request timeouts.
    pub fn next_answer(&mut self) -> QueryResult {
        // Reset timeout at start of each request
        if let Some(derivation) = &mut self.derivation {
            derivation.reset_timeout();
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
            // Require at least `theory_size` steps (minimum 1) before extracting.
            // This ensures all theory clauses have a chance to be extended and
            // any conflicts detected before returning answers.
            // Justification: each extension step processes one theory clause,
            // so after N steps all N clauses have been tried.
            let min_steps = self.theory_size.max(1);
            if self.steps_since_extraction >= min_steps {
                if let Some(ans) = self.try_extract_one_answer() {
                    self.steps_since_extraction = 0;
                    return QueryResult::Answer(ans);
                }
            }

            // Try to advance derivation
            let derivation = self.derivation.as_mut().unwrap();
            match derivation.step() {
                Some(_step) => {
                    self.steps_taken += 1;
                    self.steps_since_extraction += 1;
                    // Derivation made progress, loop to check for new answers
                    continue;
                }
                None => {
                    // Derivation at rest - check result
                    self.final_result = derivation.result().cloned();

                    // For satisfiable theories, try extraction
                    if matches!(self.final_result, Some(DerivationResult::Satisfiable(_))) {
                        if let Some(ans) = self.try_extract_one_answer() {
                            self.steps_since_extraction = 0;
                            return QueryResult::Answer(ans);
                        }
                    }

                    // Check if derivation is truly complete
                    if self.final_result.is_some() {
                        self.derivation = None;
                        return match &self.final_result {
                            Some(DerivationResult::Timeout) => QueryResult::Timeout,
                            _ => QueryResult::Exhausted,
                        };
                    }

                    // Derivation returned None but no final result - keep trying
                    // (this can happen for incremental derivations)
                    continue;
                }
            }
        }
    }

    /// Return current statistics about the query stream.
    pub fn stats(&self) -> QueryStats {
        QueryStats {
            pending_answers: 0, // No longer buffered
            seen_answers: self.seen_answers.len(),
            steps_taken: self.steps_taken,
            derivation_done: self.derivation.is_none(),
        }
    }

    /// Try to extract one new answer from the current trail state.
    ///
    /// Uses a cursor and pending_candidates to track progress incrementally.
    fn try_extract_one_answer(&mut self) -> Option<Substitution> {
        let query_vars: HashSet<Var> = self.query.variables();

        // For positive single-literal queries, try pending candidates first
        if self.query.literals.len() == 1 && self.query.literals[0].positive {
            let query_lit = self.query.literals[0].clone();

            // Try pending candidates one at a time (FIFO order)
            while let Some(trail_lit) = self.pending_candidates.pop_front() {
                if let Some(ans) =
                    self.try_match_single_literal(&query_lit, &trail_lit, &query_vars)
                {
                    return Some(ans);
                }
            }
        }

        // Collect data from the derivation/trail
        let (has_conflict, true_atoms, true_patterns, new_candidates) = {
            let derivation = self.derivation.as_ref()?;
            let trail = derivation.trail();

            // Check for conflict
            if trail.find_conflict().is_some() {
                return None;
            }

            let init_interp = trail.initial_interpretation();
            let clauses = trail.clauses();

            // Build model state from trail
            let mut atoms = HashSet::new();
            let mut patterns = Vec::new();
            for clause in clauses {
                let selected = clause.selected_literal();
                if init_interp.is_false(selected) && selected.positive {
                    if selected.is_ground() {
                        atoms.insert(selected.atom.clone());
                    } else {
                        patterns.push(selected.clone());
                    }
                }
            }

            // Collect candidate literals from cursor position onwards (FIFO order)
            let mut cands = VecDeque::new();
            while self.extraction_cursor < clauses.len() {
                let clause = &clauses[self.extraction_cursor];
                self.extraction_cursor += 1;

                let selected = clause.selected_literal();
                if init_interp.is_false(selected) && selected.positive {
                    cands.push_back(selected.clone());
                }
            }

            (false, atoms, patterns, cands)
        };

        if has_conflict {
            return None;
        }

        // Handle single-literal queries
        if self.query.literals.len() == 1 {
            let query_lit = self.query.literals[0].clone();

            if query_lit.positive {
                // Positive query - try new candidates one at a time (FIFO order)
                let mut candidates = new_candidates;
                while let Some(trail_lit) = candidates.pop_front() {
                    if let Some(ans) =
                        self.try_match_single_literal(&query_lit, &trail_lit, &query_vars)
                    {
                        // Save remaining candidates for next call
                        self.pending_candidates = candidates;
                        return Some(ans);
                    }
                }
                return None;
            } else {
                // Negative query - check for absence from model
                return self.try_extract_negative_answer(
                    &query_lit,
                    &true_atoms,
                    &true_patterns,
                    &query_vars,
                );
            }
        }

        // For multi-literal queries
        self.extract_multi_literal_one(&true_atoms, &query_vars)
    }

    /// Try to extract an answer for a negative query.
    fn try_extract_negative_answer(
        &mut self,
        query_lit: &Literal,
        true_atoms: &HashSet<Atom>,
        true_patterns: &[Literal],
        query_vars: &HashSet<Var>,
    ) -> Option<Substitution> {
        // If the query is ground, check if the atom is absent from the model
        if query_lit.is_ground() {
            if !true_atoms.contains(&query_lit.atom) {
                // Check if any pattern covers this atom
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
                    return self.add_answer_if_new_ret(&Substitution::empty(), query_vars);
                }
            }
            return None;
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

            let vars: Vec<Var> = query_vars.iter().cloned().collect();
            let candidates = generate_ground_instances(&vars, &constants);

            for subst in candidates {
                let grounded_lit = query_lit.apply_subst(&subst);

                if !true_atoms.contains(&grounded_lit.atom) {
                    let covered_by_pattern = true_patterns.iter().any(|pattern| {
                        if !pattern.positive
                            || pattern.atom.predicate != grounded_lit.atom.predicate
                        {
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
                        if let Some(ans) = self.add_answer_if_new_ret(&subst, query_vars) {
                            return Some(ans);
                        }
                    }
                }
            }
        }
        None
    }

    /// Try to match a single query literal against a trail literal.
    fn try_match_single_literal(
        &mut self,
        query_lit: &Literal,
        trail_lit: &Literal,
        query_vars: &HashSet<Var>,
    ) -> Option<Substitution> {
        if query_lit.positive {
            // Positive query - match against the trail literal
            if trail_lit.atom.predicate != query_lit.atom.predicate {
                return None;
            }

            // Rename trail literal variables to avoid clashes
            let renamed = rename_away_from(trail_lit, query_vars);

            if let UnifyResult::Success(sigma) = unify_literals(query_lit, &renamed) {
                return self.add_answer_if_new_ret(&sigma, query_vars);
            }
        } else {
            // Negative query - this is more complex, handled separately
            // For now, negative queries don't use cursor-based extraction
        }
        None
    }

    /// Add an answer if it's new, returning it if added.
    fn add_answer_if_new_ret(
        &mut self,
        sigma: &Substitution,
        query_vars: &HashSet<Var>,
    ) -> Option<Substitution> {
        let projected =
            project_substitution(sigma, query_vars, self.user_signature.as_ref(), self.policy);

        // Check projection didn't lose required bindings
        let orig_bound: HashSet<_> = sigma
            .bindings()
            .filter(|(v, _)| query_vars.contains(*v))
            .map(|(v, _)| v.clone())
            .collect();
        let proj_bound: HashSet<_> = projected.bindings().map(|(v, _)| v.clone()).collect();

        if proj_bound.len() < orig_bound.len() {
            return None;
        }

        let canonical = canonical_form(&projected);
        if self.seen_answers.insert(canonical) {
            Some(projected)
        } else {
            None
        }
    }

    /// Extract one answer for multi-literal queries.
    fn extract_multi_literal_one(
        &mut self,
        true_atoms: &HashSet<Atom>,
        query_vars: &HashSet<Var>,
    ) -> Option<Substitution> {
        // Find answers recursively
        let mut answers = Vec::new();
        let mut seen_in_search: HashSet<Vec<(Var, Term)>> = HashSet::new();

        self.find_multi_literal_answers_incremental(
            &self.query.literals.clone(),
            true_atoms,
            Substitution::empty(),
            query_vars,
            &mut answers,
            &mut seen_in_search,
        );

        // Return first new answer
        for ans in answers {
            let canonical = canonical_form(&ans);
            if self.seen_answers.insert(canonical) {
                return Some(ans);
            }
        }
        None
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
                    rest, true_atoms, combined, query_vars, answers, seen,
                );
            }
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
