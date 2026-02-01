//! Trace QueryStream behavior for unsatisfiable theory.

use sggslog::sggs::{DerivationConfig, DerivationState};
use sggslog::syntax::{Clause, Literal, Query, Term};
use sggslog::theory::Theory;

/// Trace what DerivationState does after it sets Unsatisfiable
#[test]
fn trace_derivation_after_unsatisfiable() {
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

    println!("\n=== Tracing derivation behavior ===\n");

    for i in 0..10 {
        let step_result = state.step();
        let result = state.result();

        println!(
            "Step {}: step()={:?}, result()={:?}",
            i,
            step_result.as_ref().map(|s| &s.rule),
            result
        );

        // After Unsatisfiable is found, does step() return None?
        if result.is_some() {
            println!("\n=== Result found! ===");

            // Try calling step() a few more times
            for j in 0..3 {
                let extra_step = state.step();
                let extra_result = state.result();
                println!(
                    "Extra step {}: step()={:?}, result()={:?}",
                    j,
                    extra_step.as_ref().map(|s| &s.rule),
                    extra_result
                );
            }
            return;
        }

        if step_result.is_none() {
            println!("\n=== step() returned None ===");
            return;
        }
    }

    println!("\n=== Did not find result in 10 steps ===");
}

/// Simulate what QueryStream does with the step() calls
#[test]
fn simulate_query_stream_loop() {
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
    let mut steps_taken = 0;
    let min_steps = 4; // 2 * 2 clauses

    println!("\n=== Simulating QueryStream loop ===");
    println!("min_steps = {}", min_steps);

    for i in 0..20 {
        println!("\n--- Iteration {} ---", i);
        println!("steps_taken = {}", steps_taken);

        // This is what QueryStream does
        if steps_taken >= min_steps {
            println!("Would extract answers now");
            // Check for conflict before extracting
            let has_conflict = state.trail().find_conflict().is_some();
            println!("Trail has conflict: {}", has_conflict);
        }

        // Try to advance derivation
        let step_result = state.step();
        println!("step() returned: {:?}", step_result.as_ref().map(|s| &s.rule));
        println!("result() is: {:?}", state.result());

        match step_result {
            Some(_step) => {
                steps_taken += 1;
                // QueryStream just continues here!
                // It does NOT check state.result()!
                println!("QueryStream continues (doesn't check result)");

                // What we SHOULD do:
                if state.result().is_some() {
                    println!("BUG: Result is set but QueryStream continues!");
                }
            }
            None => {
                println!("step() returned None - QueryStream will check result");
                println!("Final result: {:?}", state.result());
                return;
            }
        }
    }

    println!("\n=== STUCK: Did not complete in 20 iterations ===");
}
