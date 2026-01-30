//! SGGS derivation loop.

use super::{InitialInterpretation, Trail};
use crate::syntax::Atom;
use crate::theory::Theory;
use std::collections::HashSet;

/// Result of SGGS derivation.
#[derive(Debug)]
pub enum DerivationResult {
    /// Found refutation (theory is unsatisfiable)
    Unsatisfiable,
    /// Found model (theory is satisfiable)
    Satisfiable(Model),
    /// Resource limit reached
    ResourceLimit,
}

/// A model witnessing satisfiability.
#[derive(Debug)]
pub struct Model {
    /// The atoms that are true in this model
    pub true_atoms: HashSet<Atom>,
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
}

/// Configuration for SGGS derivation.
#[derive(Debug, Clone)]
pub struct DerivationConfig {
    /// Maximum number of derivation steps (None for unlimited)
    pub max_steps: Option<usize>,
    /// The initial interpretation to use
    pub initial_interp: InitialInterpretation,
}

impl Default for DerivationConfig {
    fn default() -> Self {
        DerivationConfig {
            max_steps: None,
            initial_interp: InitialInterpretation::default(),
        }
    }
}

/// Run SGGS derivation on a theory.
///
/// This is the main entry point for theorem proving. It attempts to
/// either find a refutation (proving unsatisfiability) or construct
/// a model (proving satisfiability).
pub fn derive(_theory: &Theory, _config: DerivationConfig) -> DerivationResult {
    todo!("derive implementation")
}

/// Run SGGS derivation and return a trace of applied inference rules.
pub fn derive_with_trace(
    _theory: &Theory,
    _config: DerivationConfig,
) -> (DerivationResult, Vec<DerivationStep>) {
    todo!("derive_with_trace implementation")
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
pub fn next_inference(_trail: &Trail, _theory: &Theory) -> InferenceRule {
    todo!("next_inference implementation")
}

/// Return all inferences applicable to the current state (order not specified).
pub fn applicable_inferences(_trail: &Trail, _theory: &Theory) -> Vec<InferenceRule> {
    todo!("applicable_inferences implementation")
}

impl DerivationState {
    /// Initialize derivation state from a theory and configuration.
    pub fn new(_theory: Theory, _config: DerivationConfig) -> Self {
        todo!("DerivationState::new implementation")
    }

    /// Initialize derivation state from an explicit trail.
    pub fn from_trail(_theory: Theory, _trail: Trail, _config: DerivationConfig) -> Self {
        todo!("DerivationState::from_trail implementation")
    }

    /// Perform one inference step.
    pub fn step(&mut self) -> Option<DerivationStep> {
        todo!("DerivationState::step implementation")
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
    use crate::constraint::Constraint;
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
        assert_eq!(next_inference(&trail, &theory), InferenceRule::Factoring);
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
        let step = state.step().expect("expected a step");
        assert_eq!(step.rule, InferenceRule::Factoring);
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
    fn derive_with_trace_respects_max_steps_zero() {
        let theory = Theory::new();
        let config = DerivationConfig {
            max_steps: Some(0),
            initial_interp: InitialInterpretation::AllNegative,
        };
        let (result, trace) = derive_with_trace(&theory, config);
        assert!(matches!(result, DerivationResult::ResourceLimit));
        assert!(trace.is_empty(), "no steps allowed when max_steps=0");
    }

    #[test]
    fn derive_with_trace_length_limited() {
        let theory = Theory::new();
        let config = DerivationConfig {
            max_steps: Some(1),
            initial_interp: InitialInterpretation::AllNegative,
        };
        let (_result, trace) = derive_with_trace(&theory, config);
        assert!(trace.len() <= 1, "trace must respect max_steps");
    }

    #[test]
    fn derivation_step_reports_trail_lengths_consistently() {
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
            Constraint::True,
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
    fn resolution_steps_do_not_increase_trail_length() {
        let theory = Theory::new();
        let config = DerivationConfig {
            max_steps: Some(10),
            initial_interp: InitialInterpretation::AllNegative,
        };
        let (_result, trace) = derive_with_trace(&theory, config);
        for step in trace {
            if step.rule == InferenceRule::Resolution {
                assert!(
                    step.trail_len_after <= step.trail_len_before,
                    "resolution should not increase trail length"
                );
            }
        }
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
    fn derive_with_trace_respects_max_steps() {
        let theory = Theory::new();
        let config = DerivationConfig {
            max_steps: Some(0),
            initial_interp: InitialInterpretation::AllNegative,
        };
        let (result, trace) = derive_with_trace(&theory, config);
        assert!(
            matches!(result, DerivationResult::ResourceLimit),
            "max_steps=0 should immediately hit resource limit"
        );
        assert!(trace.is_empty(), "trace should be empty with max_steps=0");
    }
}
