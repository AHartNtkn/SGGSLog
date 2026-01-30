//! SGGS (Semantically Guided Goal-Sensitive Reasoning) inference system.

mod interpretation;
mod trail;
mod constrained;
mod extension;
mod resolution;
mod splitting;
mod left_split;
mod deletion;
mod factoring;
mod move_op;
mod assignment;
mod derivation;

pub use interpretation::InitialInterpretation;
pub use trail::{Trail, TrailInterpretation};
pub use constrained::ConstrainedClause;
pub use extension::{sggs_extension, ExtensionResult};
pub use resolution::{sggs_resolution, ResolutionResult};
pub use splitting::{sggs_splitting, SplitResult};
pub use left_split::sggs_left_split;
pub use deletion::{sggs_deletion, is_disposable};
pub use factoring::sggs_factoring;
pub use move_op::{sggs_move, MoveError};
pub use assignment::{Assignments, compute_assignments};
pub use derivation::{derive, DerivationResult, DerivationConfig, Model};
