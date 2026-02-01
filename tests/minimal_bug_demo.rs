//! Minimal demonstration of the QueryStream infinite loop bug.
//!
//! # Summary
//!
//! The bug causes `QueryStream::next_answer()` to loop infinitely when the theory
//! is unsatisfiable (e.g., {p(a), ¬p(a)}).
//!
//! # Root Cause Chain
//!
//! 1. **DerivationState::step() behavior after EmptyClause**:
//!    - When Resolution produces EmptyClause, it sets `self.done = Some(Unsatisfiable)`
//!    - But it still returns `Some(DerivationStep)` rather than `None`
//!    - On subsequent calls to `step()`, there's no early exit when `done` is already set
//!    - `next_inference()` is called, finds Resolution is still applicable (conflict exists)
//!    - `sggs_resolution()` is called again and returns EmptyClause again
//!    - This sets `done` again (no-op, already set) and returns `Some(step)`
//!    - Result: `step()` returns `Some(Resolution)` infinitely
//!
//! 2. **QueryStream::next_answer() loop logic**:
//!    - The loop only checks `derivation.result()` when `step()` returns `None`
//!    - When `step()` returns `Some(_)`, it just increments `steps_taken` and continues
//!    - Because `step()` never returns `None` (see bug 1), result is never checked
//!    - Result: Infinite loop
//!
//! # Fix Options
//!
//! Option A: Make `step()` return `None` when `self.done.is_some()` at the start
//! Option B: Make `next_answer()` check `result()` after each step, not just when `step()` returns `None`
//! Either option fixes the bug; doing both is more robust.

use sggslog::sggs::{DerivationConfig, DerivationState};
use sggslog::syntax::{Clause, Literal, Term};
use sggslog::theory::Theory;

/// Create the minimal unsatisfiable theory: {p(a), ¬p(a)}
fn make_unsat_theory() -> Theory {
    let mut theory = Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    theory.add_clause(Clause::new(vec![Literal::neg(
        "p",
        vec![Term::constant("a")],
    )]));
    theory
}

/// Demonstrates BUG 1: step() doesn't return None when done is already set.
///
/// Expected: After setting Unsatisfiable, step() should return None.
/// Actual: step() returns Some(Resolution) repeatedly.
#[test]
fn bug1_step_doesnt_return_none_when_done() {
    let theory = make_unsat_theory();
    let config = DerivationConfig::default();
    let mut state = DerivationState::new(theory, config);

    // Run until Unsatisfiable is set
    let mut found_unsatisfiable = false;
    for _ in 0..10 {
        let step_result = state.step();
        if state.result().is_some() {
            found_unsatisfiable = true;
            println!("Unsatisfiable found");
            println!("step() returned: {:?}", step_result.as_ref().map(|s| &s.rule));

            // BUG: step() returned Some(_) when result was already set
            if step_result.is_some() {
                println!("BUG 1 DEMONSTRATED: step() returned Some when done=Unsatisfiable");
            }

            // Now call step() again after done is set
            let next_step = state.step();
            println!(
                "step() after done is set: {:?}",
                next_step.as_ref().map(|s| &s.rule)
            );

            // BUG: step() should return None, but returns Some(Resolution)
            assert!(
                next_step.is_none(),
                "BUG: step() should return None when done is already set, got {:?}",
                next_step
            );

            break;
        }
    }

    assert!(found_unsatisfiable, "Test setup failed");
}

/// Demonstrates BUG 2: QueryStream-style loop doesn't check result after step.
///
/// This simulates the exact logic in QueryStream::next_answer().
#[test]
fn bug2_querystream_loop_doesnt_check_result() {
    let theory = make_unsat_theory();
    let config = DerivationConfig::default();
    let mut state = DerivationState::new(theory, config);

    // Simulate QueryStream logic
    let mut steps = 0;
    let max_steps = 20;

    loop {
        match state.step() {
            Some(_) => {
                steps += 1;

                // BUG: QueryStream continues here without checking result!
                // The correct code would check:
                if state.result().is_some() {
                    println!(
                        "BUG 2 DEMONSTRATED: result={:?} but loop continues (step {})",
                        state.result(),
                        steps
                    );
                    // If this assertion fails, QueryStream would loop forever
                    assert!(
                        steps <= 5,
                        "BUG: Loop should have exited when result was set"
                    );
                    break;
                }
            }
            None => {
                // Only here does QueryStream check result
                println!("step() returned None, checking result...");
                break;
            }
        }

        if steps >= max_steps {
            panic!("STUCK: Loop ran {} times without exiting", max_steps);
        }
    }
}

/// Demonstrates the combined effect: Resolution keeps producing EmptyClause.
#[test]
fn combined_resolution_keeps_running() {
    let theory = make_unsat_theory();
    let config = DerivationConfig::default();
    let mut state = DerivationState::new(theory, config);

    let mut resolution_count = 0;

    for i in 0..10 {
        let step = state.step();
        let result = state.result();

        println!("Step {}: {:?}, result={:?}", i, step.as_ref().map(|s| &s.rule), result);

        if let Some(ref s) = step {
            if matches!(s.rule, sggslog::sggs::InferenceRule::Resolution) {
                resolution_count += 1;
            }
        }

        if resolution_count >= 3 {
            println!(
                "\nBUG DEMONSTRATED: Resolution was applied {} times",
                resolution_count
            );
            println!("Expected: Resolution produces EmptyClause once, then step() returns None");
            println!("Actual: Resolution keeps producing EmptyClause, step() keeps returning Some");
            break;
        }
    }
}
