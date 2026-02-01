//! SGGS derivation loop.

use super::{
    is_disposable, is_factoring_applicable, sggs_deletion, sggs_extension, sggs_factoring,
    sggs_left_split, sggs_move, sggs_resolution, sggs_splitting, ConstrainedClause,
    ExtensionResult, InitialInterpretation, ResolutionResult, Trail,
};
use crate::syntax::{Atom, Literal};
use crate::theory::Theory;
use crate::unify::{unify_literals, UnifyResult};
use std::collections::HashSet;
use std::time::Instant;

/// Result of SGGS derivation.
#[derive(Debug, Clone)]
pub enum DerivationResult {
    /// Found refutation (theory is unsatisfiable)
    Unsatisfiable,
    /// Found model (theory is satisfiable)
    Satisfiable(Model),
    /// Timeout reached
    Timeout,
}

/// A model witnessing satisfiability.
#[derive(Debug, Clone)]
pub struct Model {
    /// The ground atoms that are true in this model
    pub true_atoms: HashSet<Atom>,
    /// Non-ground literals from the trail (patterns that match via unification)
    pub true_patterns: Vec<Literal>,
}

/// A single derivation step.
#[derive(Debug, Clone)]
pub struct DerivationStep {
    pub rule: InferenceRule,
    pub trail_len_before: usize,
    pub trail_len_after: usize,
}

/// Mutable derivation state for step-by-step execution.
pub struct DerivationState {
    theory: Theory,
    trail: Trail,
    config: DerivationConfig,
    done: Option<DerivationResult>,
    start_time: Option<Instant>,
}

/// Configuration for SGGS derivation.
#[derive(Debug, Clone, Default)]
pub struct DerivationConfig {
    /// Timeout in milliseconds (None for unlimited)
    pub timeout_ms: Option<u64>,
    /// The initial interpretation to use
    pub initial_interp: InitialInterpretation,
}

/// Run SGGS derivation on a theory.
///
/// This is the main entry point for theorem proving. It attempts to
/// either find a refutation (proving unsatisfiability) or construct
/// a model (proving satisfiability).
pub fn derive(theory: &Theory, config: DerivationConfig) -> DerivationResult {
    let (result, _) = derive_with_trace(theory, config);
    result
}

/// Run SGGS derivation and return a trace of applied inference rules.
pub fn derive_with_trace(
    theory: &Theory,
    config: DerivationConfig,
) -> (DerivationResult, Vec<DerivationStep>) {
    // Check for immediate timeout
    if let Some(0) = config.timeout_ms {
        return (DerivationResult::Timeout, Vec::new());
    }

    let mut state = DerivationState::new(theory.clone(), config);
    let mut trace = Vec::new();

    loop {
        // Check for completion
        if let Some(result) = state.done.take() {
            return (result, trace);
        }

        // Try to perform a step
        match state.step() {
            Some(step) => {
                trace.push(step);
            }
            None => {
                // No more steps possible - derive result from trail state
                let result = if state.trail.find_conflict().is_some() {
                    // There's a conflict we couldn't resolve
                    DerivationResult::Unsatisfiable
                } else if has_complementary_ground_literals(&state.trail) {
                    // Semantic conflict: complementary ground literals selected
                    // (e.g., both p and ¬p are selected somewhere on the trail)
                    DerivationResult::Unsatisfiable
                } else if state.trail.is_complete(&state.theory) {
                    // Trail is complete - we have a model
                    DerivationResult::Satisfiable(extract_model(&state.trail))
                } else {
                    // Neither complete nor conflicting - check if theory is empty
                    if state.theory.clauses().is_empty() {
                        DerivationResult::Satisfiable(extract_model(&state.trail))
                    } else {
                        // Stuck - treat as timeout
                        DerivationResult::Timeout
                    }
                };
                return (result, trace);
            }
        }
    }
}

/// Check if the trail has complementary ground literals selected.
///
/// For propositional (ground, 0-ary) logic, when we have both p and ¬p selected
/// somewhere on the trail, that's a semantic conflict even if they're not in
/// prefix order. This happens when splitting can't work (ground predicates have
/// no variables to split on).
fn has_complementary_ground_literals(trail: &Trail) -> bool {
    let clauses = trail.clauses();

    for (i, clause_i) in clauses.iter().enumerate() {
        let lit_i = clause_i.selected_literal();

        // Only check ground literals
        if !lit_i.is_ground() {
            continue;
        }

        for clause_j in clauses.iter().skip(i + 1) {
            let lit_j = clause_j.selected_literal();

            // Only check ground literals
            if !lit_j.is_ground() {
                continue;
            }

            // Check if they have the same predicate but opposite polarity
            if lit_i.atom.predicate == lit_j.atom.predicate && lit_i.positive != lit_j.positive {
                // Also check that arguments match (for ground literals with args)
                if lit_i.atom.args == lit_j.atom.args {
                    return true;
                }
            }
        }
    }

    false
}

/// Extract a model from a complete trail.
fn extract_model(trail: &Trail) -> Model {
    let mut true_atoms = HashSet::new();
    let mut true_patterns = Vec::new();
    let init_interp = trail.initial_interpretation();

    for clause in trail.clauses() {
        let selected = clause.selected_literal();
        // I-false selected literals contribute to the model (they are made true by the trail)
        if init_interp.is_false(selected) && clause.constraint.is_satisfiable() && selected.positive
        {
            if selected.is_ground() {
                // Ground positive literal - add to atoms
                true_atoms.insert(selected.atom.clone());
            } else {
                // Non-ground positive literal - add as a pattern
                true_patterns.push(selected.clone());
            }
        }
    }

    Model {
        true_atoms,
        true_patterns,
    }
}

/// Inference rules used in SGGS derivations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InferenceRule {
    Extension,
    Resolution,
    Splitting,
    LeftSplit,
    Factoring,
    Move,
    Deletion,
    None,
}

/// Choose the next inference rule according to a fair, sensible strategy (Def. 32).
///
/// Priority order (from SGGS papers):
/// 1. Deletion - remove disposable clauses first (cleanup)
/// 2. Factoring - if applicable on conflict, do it before move
/// 3. Move - relocate conflict clauses
/// 4. Resolution - resolve conflicts with justifications
/// 5. LeftSplit - split clauses when factoring doesn't apply
/// 6. Splitting - split to restore disjoint prefix
/// 7. Extension - add new clauses from theory
pub fn next_inference(trail: &Trail, theory: &Theory) -> InferenceRule {
    let applicable = applicable_inferences(trail, theory);

    // Priority order
    for rule in [
        InferenceRule::Deletion,
        InferenceRule::Factoring,
        InferenceRule::Move,
        InferenceRule::Resolution,
        InferenceRule::LeftSplit,
        InferenceRule::Splitting,
        InferenceRule::Extension,
    ] {
        if applicable.contains(&rule) {
            return rule;
        }
    }

    InferenceRule::None
}

/// Return all inferences applicable to the current state (order not specified).
pub fn applicable_inferences(trail: &Trail, theory: &Theory) -> Vec<InferenceRule> {
    let mut result = Vec::new();

    // Check for deletion (disposable clauses)
    if is_deletion_applicable(trail) {
        result.push(InferenceRule::Deletion);
    }

    // Check for conflict-related rules
    if let Some(conflict_idx) = find_conflict_clause(trail) {
        let conflict = &trail.clauses()[conflict_idx];

        // Check for factoring
        if is_factoring_applicable(conflict) {
            result.push(InferenceRule::Factoring);
        }

        // Check for move (only if factoring doesn't apply on this clause)
        if is_move_applicable(conflict, trail, conflict_idx) {
            result.push(InferenceRule::Move);
        }

        // Check for left-split (only if factoring doesn't apply)
        if !is_factoring_applicable(conflict) && is_left_split_applicable(trail, conflict_idx) {
            result.push(InferenceRule::LeftSplit);
        }

        // Check for resolution
        if is_resolution_applicable(conflict, trail) {
            result.push(InferenceRule::Resolution);
        }
    }

    // Check for splitting (disjoint prefix broken)
    if is_splitting_applicable(trail) {
        result.push(InferenceRule::Splitting);
    }

    // Check for extension
    if is_extension_applicable(trail, theory) {
        result.push(InferenceRule::Extension);
    }

    result
}

/// Check if deletion is applicable (any disposable clauses).
fn is_deletion_applicable(trail: &Trail) -> bool {
    for clause in trail.clauses() {
        if is_disposable(clause, trail) {
            return true;
        }
    }
    false
}

/// Find a conflict clause in the trail.
/// A conflict clause is one where the selected literal is blocked by earlier clauses
/// (its complement is uniformly true in the prefix interpretation).
fn find_conflict_clause(trail: &Trail) -> Option<usize> {
    // Use the Trail's own find_conflict method which correctly uses prefix interpretation
    trail.find_conflict()
}

/// Check if move is applicable for a conflict clause.
///
/// Move is only applicable if ALL I-true literals have justifications in the prefix.
/// Otherwise, after moving the clause, Resolution won't be able to resolve it
/// (Resolution requires all justifications to be in dp(Γ)).
fn is_move_applicable(conflict: &ConstrainedClause, trail: &Trail, conflict_idx: usize) -> bool {
    // Move applies to I-all-true conflict clauses
    let init_interp = trail.initial_interpretation();

    // All literals must be I-true (I-all-true clause)
    let is_i_all_true = conflict
        .clause
        .literals
        .iter()
        .all(|lit| init_interp.is_true(lit));

    if !is_i_all_true {
        return false;
    }

    // ALL I-true literals must have justifications (earlier clauses that make them false)
    // This ensures Resolution will be applicable after Move
    for lit in &conflict.clause.literals {
        if !init_interp.is_true(lit) {
            continue;
        }

        let complement = lit.negated();
        let mut has_justification = false;

        for idx in 0..conflict_idx {
            let clause = &trail.clauses()[idx];
            let clause_selected = clause.selected_literal();

            // Check if clause's selected literal matches the complement
            if clause_selected.positive == complement.positive
                && clause_selected.atom.predicate == complement.atom.predicate
            {
                if let UnifyResult::Success(_) = unify_literals(clause_selected, &complement) {
                    // Check if this clause's selected is I-false (contributes to model)
                    if init_interp.is_false(clause_selected) && clause.constraint.is_satisfiable() {
                        has_justification = true;
                        break;
                    }
                }
            }
        }

        if !has_justification {
            return false;
        }
    }

    true
}

/// Check if left-split is applicable.
fn is_left_split_applicable(trail: &Trail, conflict_idx: usize) -> bool {
    let conflict = &trail.clauses()[conflict_idx];
    let dp_len = trail.disjoint_prefix_length();

    // Look for a clause in dp(Γ) whose selected literal intersects with conflict's selected
    for idx in 0..dp_len.min(conflict_idx) {
        let clause = &trail.clauses()[idx];
        if sggs_left_split(clause, conflict).is_some() {
            return true;
        }
    }
    false
}

/// Check if resolution is applicable for a conflict clause.
/// Resolution requires justifications to be in dp(Γ).
fn is_resolution_applicable(conflict: &ConstrainedClause, trail: &Trail) -> bool {
    // First check if resolution would succeed at all
    match sggs_resolution(conflict, trail) {
        ResolutionResult::Resolvent(_) | ResolutionResult::EmptyClause => {
            // Additionally check that the justification is in dp(Γ)
            let dp_len = trail.disjoint_prefix_length();
            let selected = conflict.selected_literal();
            let complement = selected.negated();
            let init_interp = trail.initial_interpretation();

            // Find the justification clause (must have I-TRUE selected literal)
            for idx in 0..dp_len {
                let clause = &trail.clauses()[idx];
                let clause_selected = clause.selected_literal();

                if clause_selected.positive == complement.positive
                    && clause_selected.atom.predicate == complement.atom.predicate
                {
                    if let UnifyResult::Success(_) = unify_literals(clause_selected, &complement) {
                        // Justifying clause should be I-all-true (selected is I-TRUE)
                        if init_interp.is_true(clause_selected)
                            && clause.constraint.is_satisfiable()
                        {
                            return true;
                        }
                    }
                }
            }
            false
        }
        ResolutionResult::Inapplicable => false,
    }
}

/// Check if splitting is applicable (disjoint prefix is broken AND non-trivial split exists).
fn is_splitting_applicable(trail: &Trail) -> bool {
    let dp_len = trail.disjoint_prefix_length();
    if dp_len >= trail.len() {
        return false;
    }

    // Check if any non-trivial split is actually possible.
    // A split is trivial if sggs_splitting returns None (no constraints added).
    let breaker_idx = dp_len;
    let breaker = &trail.clauses()[breaker_idx];

    for idx in 0..breaker_idx {
        let earlier = &trail.clauses()[idx];
        if sggs_splitting(earlier, breaker).is_some() {
            return true;
        }
    }

    false
}

/// Check if extension is applicable.
fn is_extension_applicable(trail: &Trail, theory: &Theory) -> bool {
    // Extension is applicable if:
    // 1. Trail equals its disjoint prefix
    // 2. No conflict clause exists
    // 3. There's a clause in theory that can extend the trail
    let dp_len = trail.disjoint_prefix_length();
    if dp_len != trail.len() {
        return false;
    }

    if trail.find_conflict().is_some() {
        return false;
    }

    matches!(
        sggs_extension(trail, theory),
        ExtensionResult::Extended(_)
            | ExtensionResult::Conflict(_)
            | ExtensionResult::Critical { .. }
    )
}

impl DerivationState {
    /// Initialize derivation state from a theory and configuration.
    pub fn new(theory: Theory, config: DerivationConfig) -> Self {
        let trail = Trail::new(config.initial_interp.clone());
        let start_time = config.timeout_ms.map(|_| Instant::now());

        DerivationState {
            theory,
            trail,
            config,
            done: None,
            start_time,
        }
    }

    /// Initialize derivation state from an explicit trail.
    pub fn from_trail(theory: Theory, trail: Trail, config: DerivationConfig) -> Self {
        let start_time = config.timeout_ms.map(|_| Instant::now());

        DerivationState {
            theory,
            trail,
            config,
            done: None,
            start_time,
        }
    }

    /// Check if timeout has been reached.
    fn is_timed_out(&self) -> bool {
        if let (Some(timeout_ms), Some(start)) = (self.config.timeout_ms, self.start_time) {
            let elapsed = start.elapsed().as_millis() as u64;
            return elapsed >= timeout_ms;
        }
        false
    }

    /// Perform one inference step.
    ///
    /// Returns `Some(step)` if an inference was applied, `None` if the derivation
    /// is complete (check `result()` for the outcome).
    pub fn step(&mut self) -> Option<DerivationStep> {
        // If already done, return None immediately
        if self.done.is_some() {
            return None;
        }

        // Check for timeout
        if self.is_timed_out() {
            self.done = Some(DerivationResult::Timeout);
            return None;
        }

        let trail_len_before = self.trail.len();
        let rule = next_inference(&self.trail, &self.theory);

        match rule {
            InferenceRule::None => {
                // No inference applicable - determine result
                if self.trail.find_conflict().is_some() {
                    // There's a conflict we couldn't resolve
                    self.done = Some(DerivationResult::Unsatisfiable);
                } else if has_complementary_ground_literals(&self.trail) {
                    // Semantic conflict: complementary ground literals selected
                    self.done = Some(DerivationResult::Unsatisfiable);
                } else if self.trail.is_complete(&self.theory) {
                    // Trail is complete - we have a model
                    self.done = Some(DerivationResult::Satisfiable(extract_model(&self.trail)));
                } else if self.theory.clauses().is_empty() {
                    // Empty theory is satisfiable
                    self.done = Some(DerivationResult::Satisfiable(extract_model(&self.trail)));
                }
                // If none of the above, done remains None (stuck/timeout)
                None
            }

            InferenceRule::Deletion => {
                sggs_deletion(&mut self.trail);
                Some(DerivationStep {
                    rule,
                    trail_len_before,
                    trail_len_after: self.trail.len(),
                })
            }

            InferenceRule::Factoring => {
                if let Some(conflict_idx) = find_conflict_clause(&self.trail) {
                    let conflict = self.trail.clauses()[conflict_idx].clone();

                    // Find which literal to factor with
                    let selected = conflict.selected_literal();
                    for (idx, lit) in conflict.clause.literals.iter().enumerate() {
                        if idx == conflict.selected {
                            continue;
                        }
                        if lit.positive == selected.positive
                            && lit.atom.predicate == selected.atom.predicate
                        {
                            if let Some(factored) = sggs_factoring(&conflict, idx) {
                                // Replace the conflict clause with the factored version
                                self.trail.remove_clause(conflict_idx);
                                self.trail.insert_clause(conflict_idx, factored);

                                return Some(DerivationStep {
                                    rule,
                                    trail_len_before,
                                    trail_len_after: self.trail.len(),
                                });
                            }
                        }
                    }
                }
                None
            }

            InferenceRule::Move => {
                if let Some(conflict_idx) = find_conflict_clause(&self.trail) {
                    if sggs_move(&mut self.trail, conflict_idx).is_ok() {
                        return Some(DerivationStep {
                            rule,
                            trail_len_before,
                            trail_len_after: self.trail.len(),
                        });
                    }
                }
                None
            }

            InferenceRule::Resolution => {
                if let Some(conflict_idx) = find_conflict_clause(&self.trail) {
                    let conflict = self.trail.clauses()[conflict_idx].clone();

                    match sggs_resolution(&conflict, &self.trail) {
                        ResolutionResult::EmptyClause => {
                            self.done = Some(DerivationResult::Unsatisfiable);
                            return Some(DerivationStep {
                                rule,
                                trail_len_before,
                                trail_len_after: self.trail.len(),
                            });
                        }
                        ResolutionResult::Resolvent(resolvent) => {
                            // Remove clauses assigned to the conflict
                            self.prune_assigned_clauses(conflict_idx);

                            // Replace conflict with resolvent
                            if conflict_idx < self.trail.len() {
                                self.trail.remove_clause(conflict_idx);
                            }
                            self.trail.push(resolvent);

                            return Some(DerivationStep {
                                rule,
                                trail_len_before,
                                trail_len_after: self.trail.len(),
                            });
                        }
                        ResolutionResult::Inapplicable => {}
                    }
                }
                None
            }

            InferenceRule::LeftSplit => {
                if let Some(conflict_idx) = find_conflict_clause(&self.trail) {
                    let conflict = &self.trail.clauses()[conflict_idx];
                    let dp_len = self.trail.disjoint_prefix_length();

                    for idx in 0..dp_len.min(conflict_idx) {
                        let clause = self.trail.clauses()[idx].clone();
                        if let Some(split_result) = sggs_left_split(&clause, conflict) {
                            // Replace the clause with split parts
                            self.trail.remove_clause(idx);
                            for (i, part) in split_result.parts.into_iter().enumerate() {
                                self.trail.insert_clause(idx + i, part);
                            }

                            return Some(DerivationStep {
                                rule,
                                trail_len_before,
                                trail_len_after: self.trail.len(),
                            });
                        }
                    }
                }
                None
            }

            InferenceRule::Splitting => {
                let dp_len = self.trail.disjoint_prefix_length();
                if dp_len < self.trail.len() {
                    // Find the clause that breaks disjointness
                    let breaker_idx = dp_len;
                    let breaker = self.trail.clauses()[breaker_idx].clone();

                    // Find which earlier clause it intersects with
                    for idx in 0..breaker_idx {
                        let earlier = self.trail.clauses()[idx].clone();
                        if let Some(split_result) = sggs_splitting(&earlier, &breaker) {
                            // Replace the earlier clause with split parts
                            self.trail.remove_clause(idx);
                            for (i, part) in split_result.parts.into_iter().enumerate() {
                                self.trail.insert_clause(idx + i, part);
                            }

                            return Some(DerivationStep {
                                rule,
                                trail_len_before,
                                trail_len_after: self.trail.len(),
                            });
                        }
                    }

                    // Splitting was applicable but failed (no variables to split).
                    // For ground propositional logic, this means semantic conflict.
                    if has_complementary_ground_literals(&self.trail) {
                        self.done = Some(DerivationResult::Unsatisfiable);
                    }
                }
                None
            }

            InferenceRule::Extension => {
                match sggs_extension(&self.trail, &self.theory) {
                    ExtensionResult::Extended(clause) => {
                        self.trail.push(clause);
                        Some(DerivationStep {
                            rule,
                            trail_len_before,
                            trail_len_after: self.trail.len(),
                        })
                    }
                    ExtensionResult::Conflict(clause) => {
                        // Empty clause conflict means immediate unsatisfiability
                        if clause.clause.is_empty() {
                            self.done = Some(DerivationResult::Unsatisfiable);
                            return Some(DerivationStep {
                                rule,
                                trail_len_before,
                                trail_len_after: self.trail.len(),
                            });
                        }
                        self.trail.push(clause);
                        Some(DerivationStep {
                            rule,
                            trail_len_before,
                            trail_len_after: self.trail.len(),
                        })
                    }
                    ExtensionResult::Critical {
                        replace_index,
                        clause,
                    } => {
                        self.trail.remove_clause(replace_index);
                        self.trail.insert_clause(replace_index, clause);
                        Some(DerivationStep {
                            rule,
                            trail_len_before,
                            trail_len_after: self.trail.len(),
                        })
                    }
                    ExtensionResult::NoExtension => None,
                }
            }
        }
    }

    /// Prune clauses that are assigned to the conflict clause being resolved.
    fn prune_assigned_clauses(&mut self, conflict_idx: usize) {
        let conflict = &self.trail.clauses()[conflict_idx];
        let conflict_selected = conflict.selected_literal().clone();

        // Find clauses whose selected literal depends on the conflict's selected
        let mut to_remove = Vec::new();
        for (idx, clause) in self.trail.clauses().iter().enumerate() {
            if idx == conflict_idx {
                continue;
            }
            let selected = clause.selected_literal();
            // Check if selected is the complement of conflict's selected
            if selected.is_complementary(&conflict_selected) {
                if let UnifyResult::Success(_) =
                    unify_literals(selected, &conflict_selected.negated())
                {
                    to_remove.push(idx);
                }
            }
        }

        // Remove in reverse order to preserve indices
        for idx in to_remove.into_iter().rev() {
            if idx != conflict_idx {
                self.trail.remove_clause(idx);
            }
        }
    }

    /// Current trail.
    pub fn trail(&self) -> &Trail {
        &self.trail
    }

    /// Current result, if derivation is finished.
    pub fn result(&self) -> Option<&DerivationResult> {
        self.done.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::{AtomicConstraint, Constraint};
    use crate::sggs::ConstrainedClause;
    use crate::syntax::{Clause, Literal, Term};

    #[test]
    fn next_inference_only_deletion_applicable() {
        // A clause with unsatisfiable constraint is disposable; with no other clauses,
        // deletion is the only applicable inference.
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
            Constraint::False,
            0,
        ));
        let theory = Theory::new();
        assert_eq!(next_inference(&trail, &theory), InferenceRule::Deletion);
    }

    #[test]
    fn next_inference_only_factoring_applicable() {
        // SGGS-factoring applies to I-all-true conflict clauses when another
        // same-sign literal assigned to the same clause unifies with the selected literal.
        // Source: bonacina2016.pdf, Definition 27 (SGGS-factoring).
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        // Side premise in dp(Γ): selected I-false literal P(a)
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
            Constraint::True,
            0,
        ));
        // I-all-true conflict clause with two identical literals assigned to the same premise.
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![
                Literal::neg("P", vec![Term::constant("a")]),
                Literal::neg("P", vec![Term::constant("a")]),
            ]),
            Constraint::True,
            0,
        ));
        let theory = Theory::new();
        let applicable = applicable_inferences(&trail, &theory);
        assert!(
            applicable.contains(&InferenceRule::Factoring),
            "factoring should be applicable"
        );
        assert!(
            applicable.contains(&next_inference(&trail, &theory)),
            "next_inference must return an applicable rule"
        );
    }

    #[test]
    fn derivation_state_step_reports_rule() {
        // Source: bonacina2016.pdf, Definition 27 (SGGS-factoring).
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
            Constraint::True,
            0,
        ));
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![
                Literal::neg("P", vec![Term::constant("a")]),
                Literal::neg("P", vec![Term::constant("a")]),
            ]),
            Constraint::True,
            0,
        ));
        let theory = Theory::new();
        let mut state = DerivationState::from_trail(theory, trail, DerivationConfig::default());
        let applicable = applicable_inferences(state.trail(), &Theory::new());
        let step = state.step().expect("expected a step");
        assert!(
            applicable.contains(&step.rule),
            "step rule must be applicable"
        );
    }

    #[test]
    fn derivation_state_step_reports_splitting() {
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::var("X")])]),
            Constraint::True,
            0,
        ));
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
            Constraint::True,
            0,
        ));
        let theory = Theory::new();
        let mut state = DerivationState::from_trail(theory, trail, DerivationConfig::default());
        let step = state.step().expect("expected a step");
        assert!(
            matches!(
                step.rule,
                InferenceRule::Splitting | InferenceRule::Deletion
            ),
            "intersection should trigger splitting or deletion"
        );
    }

    #[test]
    fn derive_with_trace_respects_timeout_zero() {
        let theory = Theory::new();
        let config = DerivationConfig {
            timeout_ms: Some(0),
            initial_interp: InitialInterpretation::AllNegative,
        };
        let (result, trace) = derive_with_trace(&theory, config);
        assert!(matches!(result, DerivationResult::Timeout));
        assert!(trace.is_empty(), "no steps allowed when timeout_ms=0");
    }

    #[test]
    fn derive_respects_timeout_zero() {
        let theory = Theory::new();
        let config = DerivationConfig {
            timeout_ms: Some(0),
            initial_interp: InitialInterpretation::AllNegative,
        };
        let result = derive(&theory, config);
        assert!(matches!(result, DerivationResult::Timeout));
    }

    #[test]
    fn derive_with_trace_step_chain_is_consistent() {
        let theory = Theory::new();
        let (result, trace) = derive_with_trace(&theory, DerivationConfig::default());
        if matches!(result, DerivationResult::Timeout) {
            return;
        }
        for pair in trace.windows(2) {
            let prev = &pair[0];
            let next = &pair[1];
            assert_eq!(
                prev.trail_len_after, next.trail_len_before,
                "trace steps must chain trail lengths"
            );
        }
    }

    #[test]
    fn derivation_step_reports_trail_lengths_consistently() {
        // Use a clause with unsatisfiable constraint to trigger deletion
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
            Constraint::False, // Unsatisfiable constraint makes clause disposable
            0,
        ));
        let theory = Theory::new();
        let mut state = DerivationState::from_trail(theory, trail, DerivationConfig::default());
        let len_before = state.trail().len();
        let step = state.step().expect("expected a step");
        assert_eq!(step.trail_len_before, len_before);
        assert_eq!(step.trail_len_after, state.trail().len());
    }

    #[test]
    fn applicable_inferences_includes_left_split() {
        // Left-split applies when an I-all-true clause is assigned to a dp(Γ) clause
        // with strict subset condition ¬Gr(B⊲M) ⊂ pcgi(A⊲L,Γ), and no factoring (†).
        // Source: bonacina2016.pdf, Definition 24 (Left splitting); SGGSdpFOL Fig. 2.
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        // A ⊲ C[L] in dp(Γ) with L = P(x) (I-false under I⁻)
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
            Constraint::True,
            0,
        ));
        // I-all-true conflict clause B ⊲ D[M] with M = ¬P(a) assigned to C
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
            Constraint::True,
            0,
        ));
        let theory = Theory::new();
        let rules = applicable_inferences(&trail, &theory);
        assert!(
            rules.contains(&InferenceRule::LeftSplit),
            "left-split should be applicable on intersecting clauses"
        );
    }

    #[test]
    fn applicable_inferences_excludes_left_split_when_factoring_applies() {
        // If condition (†) holds (another literal unifies with the selected one),
        // factoring should be applicable and left-split should not.
        // Source: SGGSdpFOL.pdf, Fig. 2 (condition †).
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        // Side premise in dp(Γ): selected P(a)
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
            Constraint::True,
            0,
        ));
        // I-all-true conflict clause with two identical literals († holds)
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![
                Literal::neg("P", vec![Term::constant("a")]),
                Literal::neg("P", vec![Term::constant("a")]),
            ]),
            Constraint::True,
            0,
        ));

        let theory = Theory::new();
        let rules = applicable_inferences(&trail, &theory);
        assert!(
            rules.contains(&InferenceRule::Factoring),
            "factoring should be applicable when (†) holds"
        );
        assert!(
            !rules.contains(&InferenceRule::LeftSplit),
            "left-split should not apply when factoring is applicable"
        );
    }

    #[test]
    fn applicable_inferences_excludes_resolution_without_assignment() {
        // A conflict clause with no assigned I-all-true justification should not trigger resolution.
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(ConstrainedClause::new(
            Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
            0,
        ));
        let theory = Theory::new();
        let rules = applicable_inferences(&trail, &theory);
        assert!(
            !rules.contains(&InferenceRule::Resolution),
            "resolution requires an assigned justification in dp(Γ)"
        );
    }

    #[test]
    fn applicable_inferences_excludes_resolution_without_dp_justification() {
        // Resolution must use justifications from the disjoint prefix.
        // Construct a conflict clause whose only dependence is on a selected literal outside dp(Γ).
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        // dp(Γ) contains only P(a) because P(X) intersects it.
        trail.push(ConstrainedClause::new(
            Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
            0,
        ));
        trail.push(ConstrainedClause::new(
            Clause::new(vec![Literal::pos("P", vec![Term::var("X")])]),
            0,
        ));
        // Conflict clause ¬P(b) depends on P(X), not on P(a).
        trail.push(ConstrainedClause::new(
            Clause::new(vec![Literal::neg("P", vec![Term::constant("b")])]),
            0,
        ));

        let theory = Theory::new();
        let rules = applicable_inferences(&trail, &theory);
        assert!(
            !rules.contains(&InferenceRule::Resolution),
            "resolution should not apply when justifications are outside dp(Γ)"
        );
    }

    #[test]
    fn applicable_inferences_excludes_resolution_without_entailment() {
        // SGGS-resolution (Def. 26) requires A |= Bϑ; if not, resolution is inapplicable.
        let x = Term::var("X");
        let a = Term::constant("a");
        let b = Term::constant("b");
        let b_constraint = Constraint::Atomic(AtomicConstraint::Identical(x.clone(), a.clone()));
        let a_constraint = Constraint::Or(
            Box::new(Constraint::Atomic(AtomicConstraint::Identical(
                x.clone(),
                a.clone(),
            ))),
            Box::new(Constraint::Atomic(AtomicConstraint::Identical(
                x.clone(),
                b.clone(),
            ))),
        );

        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        // I-all-true clause in dp(Γ) with selected ¬P(X), constrained to X = a.
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::neg("P", vec![x.clone()])]),
            b_constraint.clone(),
            0,
        ));
        // Conflict clause with selected P(X), but constraint allows X = a or X = b.
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![x.clone()])]),
            a_constraint,
            0,
        ));

        let theory = Theory::new();
        let rules = applicable_inferences(&trail, &theory);
        assert!(
            !rules.contains(&InferenceRule::Resolution),
            "resolution requires A |= Bϑ; broader A must not resolve against tighter B"
        );
    }

    #[test]
    fn resolution_prunes_assigned_clauses() {
        // SGGS-resolution removes clauses with literals assigned to the resolved conflict clause.
        // Source: SGGSdpFOL.pdf, Fig. 2 (resolve rule, Γ' pruning).
        let a = Term::constant("a");
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        // Justification in dp(Γ): ¬Q(a)
        trail.push(ConstrainedClause::new(
            Clause::new(vec![Literal::neg("Q", vec![a.clone()])]),
            0,
        ));
        // Conflict clause: Q(a) ∨ R(a), selected Q(a)
        trail.push(ConstrainedClause::new(
            Clause::new(vec![
                Literal::pos("Q", vec![a.clone()]),
                Literal::pos("R", vec![a.clone()]),
            ]),
            0,
        ));
        // Clause whose selected literal depends on Q(a) in the conflict clause
        trail.push(ConstrainedClause::new(
            Clause::new(vec![Literal::neg("Q", vec![a.clone()])]),
            0,
        ));

        let theory = Theory::new();
        let mut state = DerivationState::from_trail(theory, trail, DerivationConfig::default());
        let step = state.step().expect("expected a step");
        assert_eq!(step.rule, InferenceRule::Resolution);

        // After resolution, any clause assigned to the conflict clause should be removed.
        assert!(
            !state
                .trail()
                .clauses()
                .iter()
                .skip(1)
                .any(|c| c.selected_literal() == &Literal::neg("Q", vec![a.clone()])),
            "assigned clauses should be pruned after resolution"
        );
    }

    #[test]
    fn applicable_inferences_includes_move_for_i_all_true_conflict() {
        // Under I⁻, negative literals are I-true; ¬P(a) is I-all-true and conflicts with P(a).
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(ConstrainedClause::new(
            Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
            0,
        ));
        trail.push(ConstrainedClause::new(
            Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
            0,
        ));
        let theory = Theory::new();
        let rules = applicable_inferences(&trail, &theory);
        assert!(
            rules.contains(&InferenceRule::Move),
            "move should be applicable for an I-all-true conflict clause"
        );
    }

    #[test]
    fn derive_with_trace_respects_timeout() {
        let theory = Theory::new();
        let config = DerivationConfig {
            timeout_ms: Some(0),
            initial_interp: InitialInterpretation::AllNegative,
        };
        let (result, trace) = derive_with_trace(&theory, config);
        assert!(
            matches!(result, DerivationResult::Timeout),
            "timeout_ms=0 should immediately hit timeout"
        );
        assert!(trace.is_empty(), "trace should be empty with timeout_ms=0");
    }

    #[test]
    fn derivation_state_step_returns_none_when_done() {
        // Source: spec.md (timeout_ms=0 times out immediately).
        let theory = Theory::new();
        let config = DerivationConfig {
            timeout_ms: Some(0),
            initial_interp: InitialInterpretation::AllNegative,
        };
        let mut state = DerivationState::new(theory, config);
        let step = state.step();
        assert!(step.is_none(), "step must return None when done");
        assert!(
            matches!(state.result(), Some(DerivationResult::Timeout)),
            "done state should be timeout"
        );
        assert!(state.step().is_none(), "step must stay None once done");
    }
}
