//! Regression tests for the infinite Resolution loop bug (now fixed).
//!
//! The bug: For unsatisfiable theory {p(a), ¬p(a)}, QueryStream would loop
//! infinitely because DerivationState::step() didn't return None after setting
//! done = Unsatisfiable.
//!
//! Fix: step() now checks if self.done.is_some() at the start and returns None
//! immediately, allowing callers to detect completion correctly.

use sggslog::sggs::{
    derive, DerivationConfig, DerivationResult, DerivationState, InitialInterpretation,
};
use sggslog::syntax::{Clause, Literal, Term};
use sggslog::theory::Theory;

/// Helper to run derivation with a step limit.
fn derive_with_limit(theory: &Theory, max_steps: usize) -> (Option<DerivationResult>, usize) {
    let config = DerivationConfig::default();
    let mut state = DerivationState::new(theory.clone(), config);
    for i in 0..max_steps {
        let step_result = state.step();
        // Check if result was set (either by step returning None or by resolution)
        if let Some(result) = state.result() {
            return (Some(result.clone()), i);
        }
        if step_result.is_none() {
            // Derivation finished without explicit result (saturated)
            return (state.result().cloned(), i);
        }
    }
    (None, max_steps) // Did not finish
}

/// Minimal reproduction: Two unit clauses that resolve to empty clause.
///
/// Theory: {p(a), ¬p(a)}
///
/// Expected derivation:
/// 1. Extension adds p(a) to trail
/// 2. Extension adds ¬p(a) to trail (conflict)
/// 3. Resolution produces empty clause
/// 4. Return Unsatisfiable
///
/// Actual behavior: Infinite Resolution loop after step 2.
#[test]
fn two_complementary_units_with_constant_should_be_unsatisfiable() {
    let mut theory = Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    theory.add_clause(Clause::new(vec![Literal::neg(
        "p",
        vec![Term::constant("a")],
    )]));

    let (result, steps) = derive_with_limit(&theory, 20);

    match result {
        Some(DerivationResult::Unsatisfiable) => {}
        Some(DerivationResult::Satisfiable(_)) => {
            panic!("BUG: Got Satisfiable but theory is unsatisfiable - two complementary unit clauses")
        }
        Some(DerivationResult::Timeout) => {
            panic!("BUG: Got Timeout unexpectedly")
        }
        None => {
            panic!(
                "BUG: Derivation stuck after {} steps - likely infinite Resolution loop",
                steps
            )
        }
    }
}

/// Compare with the propositional case: {p, ¬p}
/// This is known to work from harder_unsatisfiable_bug.rs (simple_unsatisfiable_terminates).
#[test]
fn two_propositional_complementary_units_should_be_unsatisfiable() {
    let mut theory = Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos("p", vec![])]));
    theory.add_clause(Clause::new(vec![Literal::neg("p", vec![])]));

    let config = DerivationConfig {
        timeout_ms: Some(1000),
        initial_interp: InitialInterpretation::AllNegative,
    };
    let result = derive(&theory, config);

    assert!(
        matches!(result, DerivationResult::Unsatisfiable),
        "p ∧ ¬p should be unsatisfiable, got {:?}",
        result
    );
}

/// Verify XOR theory is correctly identified as satisfiable.
///
/// Theory: {p(a) ∨ q(b), ¬p(a) ∨ ¬q(b)}
///
/// This is XOR (exactly one of p(a), q(b) must be true) - SATISFIABLE.
/// Models: {p(a)=T, q(b)=F} or {p(a)=F, q(b)=T}
#[test]
fn xor_theory_is_satisfiable() {
    let mut theory = Theory::new();
    theory.add_clause(Clause::new(vec![
        Literal::pos("p", vec![Term::constant("a")]),
        Literal::pos("q", vec![Term::constant("b")]),
    ]));
    theory.add_clause(Clause::new(vec![
        Literal::neg("p", vec![Term::constant("a")]),
        Literal::neg("q", vec![Term::constant("b")]),
    ]));

    let (result, _steps) = derive_with_limit(&theory, 50);

    match result {
        Some(DerivationResult::Satisfiable(_)) => {}
        Some(DerivationResult::Unsatisfiable) => {
            panic!("Got Unsatisfiable but XOR theory is satisfiable")
        }
        Some(DerivationResult::Timeout) => {
            panic!("Got Timeout unexpectedly")
        }
        None => {
            panic!("Derivation did not complete")
        }
    }
}

/// Verify that a satisfiable theory does NOT trigger the bug.
///
/// Theory: {p(a), q(b)}
///
/// This is satisfiable - no complementary literals.
#[test]
fn satisfiable_theory_should_saturate() {
    let mut theory = Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    theory.add_clause(Clause::new(vec![Literal::pos(
        "q",
        vec![Term::constant("b")],
    )]));

    let (result, steps) = derive_with_limit(&theory, 20);

    match result {
        Some(DerivationResult::Satisfiable(_)) => {}
        Some(DerivationResult::Unsatisfiable) => {
            panic!("BUG: Got Unsatisfiable but theory is satisfiable")
        }
        Some(DerivationResult::Timeout) => {
            panic!("BUG: Got Timeout unexpectedly")
        }
        None => {
            panic!("Derivation didn't terminate after {} steps", steps)
        }
    }
}

/// Debug test: Trace step-by-step derivation to see where Resolution goes wrong.
#[test]
fn trace_resolution_steps_for_complementary_units() {
    let mut theory = Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    theory.add_clause(Clause::new(vec![Literal::neg(
        "p",
        vec![Term::constant("a")],
    )]));

    let config = DerivationConfig::default();
    let mut state = DerivationState::new(theory, config);
    let mut log = Vec::new();

    for i in 0..10 {
        let trail_before = format!("{:?}", state.trail());
        let step_result = state.step();
        let trail_after = format!("{:?}", state.trail());
        let result_status = state.result();

        log.push(format!(
            "Step {}: step()={:?}, result()={:?}\n  Before: {}\n  After: {}",
            i, step_result, result_status, trail_before, trail_after
        ));

        if let Some(result) = result_status {
            match result {
                DerivationResult::Unsatisfiable => {
                    println!("Derivation trace:\n{}", log.join("\n"));
                    return; // Success - found unsatisfiable
                }
                DerivationResult::Satisfiable(_) => {
                    println!("Derivation trace:\n{}", log.join("\n"));
                    panic!("BUG: Satisfiable on unsatisfiable theory");
                }
                DerivationResult::Timeout => {
                    println!("Derivation trace:\n{}", log.join("\n"));
                    panic!("BUG: Timeout on simple theory");
                }
            }
        }
    }

    println!("Derivation trace (first 10 steps):\n{}", log.join("\n"));
    panic!("BUG: Did not reach Unsatisfiable in 10 steps - stuck in loop");
}
