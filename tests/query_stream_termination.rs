//! Regression tests for QueryStream termination on unsatisfiable theories.
//!
//! These tests guard against the infinite loop bug where QueryStream would
//! loop forever when the underlying derivation found Unsatisfiable.

use sggslog::sggs::{answer_query, DerivationConfig, QueryResult};
use sggslog::syntax::{Clause, Literal, Query, Term};
use sggslog::theory::Theory;

/// QueryStream must return Exhausted (not loop forever) on unsatisfiable theory.
///
/// This test guards against the bug where:
/// 1. Resolution finds EmptyClause and sets done = Unsatisfiable
/// 2. step() returns Some(step) instead of None
/// 3. QueryStream loops forever because it only checks result() when step() returns None
#[test]
fn query_stream_terminates_on_unsatisfiable_theory() {
    let mut theory = Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    theory.add_clause(Clause::new(vec![Literal::neg(
        "p",
        vec![Term::constant("a")],
    )]));

    let query = Query::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
    let mut stream = answer_query(&theory, &query, DerivationConfig::default());

    // This would hang forever if the bug is present
    let result = stream.next_answer();

    assert!(
        matches!(result, QueryResult::Exhausted),
        "Expected Exhausted on unsatisfiable theory, got {:?}",
        result
    );
}

/// Propositional unsatisfiable theory must also terminate.
#[test]
fn query_stream_terminates_on_propositional_contradiction() {
    let mut theory = Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos("p", vec![])]));
    theory.add_clause(Clause::new(vec![Literal::neg("p", vec![])]));

    let query = Query::new(vec![Literal::pos("p", vec![])]);
    let mut stream = answer_query(&theory, &query, DerivationConfig::default());

    let result = stream.next_answer();

    assert!(
        matches!(result, QueryResult::Exhausted),
        "Expected Exhausted on p ∧ ¬p, got {:?}",
        result
    );
}

/// Multiple calls to next_answer should all return Exhausted once done.
#[test]
fn query_stream_stays_exhausted() {
    let mut theory = Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    theory.add_clause(Clause::new(vec![Literal::neg(
        "p",
        vec![Term::constant("a")],
    )]));

    let query = Query::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
    let mut stream = answer_query(&theory, &query, DerivationConfig::default());

    // First call
    let r1 = stream.next_answer();
    assert!(matches!(r1, QueryResult::Exhausted));

    // Subsequent calls should also return Exhausted, not hang
    let r2 = stream.next_answer();
    assert!(matches!(r2, QueryResult::Exhausted));

    let r3 = stream.next_answer();
    assert!(matches!(r3, QueryResult::Exhausted));
}
