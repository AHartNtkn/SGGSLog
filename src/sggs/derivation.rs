//! SGGS derivation loop.

use std::collections::HashSet;
use crate::syntax::Atom;
use crate::theory::Theory;
use super::{InitialInterpretation, Trail};

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
