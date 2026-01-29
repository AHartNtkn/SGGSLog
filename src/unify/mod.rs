//! Unification: computing most general unifiers for first-order terms.

mod substitution;
mod unify;

pub use substitution::Substitution;
pub use unify::{unify, unify_literals, unify_many, UnifyResult, UnifyError};
