//! SGGS (Semantically Guided Goal-Sensitive Reasoning) inference system.

mod interpretation;
mod trail;
mod constrained;
mod extension;
mod resolution;
mod splitting;
mod deletion;
mod move_op;
mod derivation;

pub use interpretation::InitialInterpretation;
pub use trail::{Trail, TrailInterpretation};
pub use constrained::ConstrainedClause;
pub use extension::{sggs_extension, ExtensionResult};
pub use resolution::{sggs_resolution, ResolutionResult};
pub use splitting::{sggs_splitting, SplitResult};
pub use deletion::{sggs_deletion, is_disposable};
pub use move_op::{sggs_move, MoveError};
pub use derivation::{derive, DerivationResult, DerivationConfig, Model};
