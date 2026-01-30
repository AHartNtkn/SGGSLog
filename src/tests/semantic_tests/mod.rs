//! Semantic tests for SGGS implementation.
//!
//! These tests verify essential semantic properties, not just surface behavior.
//! They are designed to fail until the implementation is correct, testing
//! subtle invariants that a buggy implementation would violate.
//!
//! # References
//!
//! ## SGGS Papers
//! - [BP16a] Bonacina, M.P., Plaisted, D.A. "Semantically-Guided Goal-Sensitive
//!   Reasoning: Model Representation." J Autom Reasoning 56, 113–141 (2016).
//!   https://doi.org/10.1007/s10817-015-9334-4
//!
//! - [BP17] Bonacina, M.P., Plaisted, D.A. "Semantically-Guided Goal-Sensitive
//!   Reasoning: Inference System and Completeness." J Autom Reasoning 59(2),
//!   165–218 (2017). https://doi.org/10.1007/s10817-016-9384-2
//!
//! - [BW20] Bonacina, M.P., Winkler, S. "SGGS Decision Procedures." IJCAR 2020,
//!   LNCS 12166, pp. 356-374. https://doi.org/10.1007/978-3-030-51074-9_20
//!
use std::collections::HashMap;

use crate::constraint::Constraint;
use crate::sggs::ConstrainedClause;
use crate::syntax::{Atom, Clause, Literal, Term, Var};
use crate::unify::{unify, unify_literals, unify_many, Substitution, UnifyResult};

/// Helper to create a Theory from a vec of clauses.
fn theory_from_clauses(clauses: Vec<Clause>) -> crate::theory::Theory {
    let mut theory = crate::theory::Theory::new();
    for c in clauses {
        theory.add_clause(c);
    }
    theory
}

/// Helper to build a unit constrained clause with a True constraint.
fn unit(lit: Literal) -> ConstrainedClause {
    ConstrainedClause::with_constraint(Clause::new(vec![lit]), Constraint::True, 0)
}

mod assignment_semantics;
mod clause_semantics;
mod completeness_semantics;
mod conflict_solving_semantics;
mod constraint_semantics;
mod extension_semantics;
mod fairness_semantics;
mod fragment_semantics;
mod move_semantics;
mod partial_interpretation_semantics;
mod proptests;
mod query_semantics;
mod resolution_semantics;
mod session_semantics;
mod splitting_semantics;
mod substitution_semantics;
mod trail_semantics;
mod unification_semantics;
