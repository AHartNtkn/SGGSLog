//! SGGS (Semantically Guided Goal-Sensitive Reasoning) inference system.

mod assignment;
mod constrained;
mod deletion;
mod derivation;
mod extension;
mod factoring;
mod interpretation;
mod left_split;
mod move_op;
mod query;
mod resolution;
mod splitting;
mod trail;

pub use crate::syntax::Query;
pub use assignment::{compute_assignments, Assignments};
pub use constrained::ConstrainedClause;
pub use deletion::{is_disposable, sggs_deletion};
pub use derivation::{
    applicable_inferences, derive, derive_with_trace, next_inference, DerivationConfig,
    DerivationResult, DerivationState, DerivationStep, InferenceRule, Model,
};
pub use extension::{sggs_extension, ExtensionResult};
pub use factoring::sggs_factoring;
pub use interpretation::{InitialInterpretation, TruthValue};
pub use left_split::sggs_left_split;
pub use move_op::{sggs_move, MoveError};
pub use query::{answer_query, answer_query_projected, ProjectionPolicy, QueryResult, QueryStream};
pub use resolution::{sggs_resolution, ResolutionResult};
pub use splitting::{sggs_splitting, sggs_splitting_on, SplitResult};
pub use trail::{PartialInterpretation, Trail, TrailError, TrailInterpretation};
