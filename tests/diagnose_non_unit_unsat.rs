//! Diagnostic tests for non-unit unsatisfiable theory bug.
//!
//! Theory: {{p(a)∨q(b), ¬p(a)∨¬q(b)}}
//! This should be unsatisfiable but returns Satisfiable.

use sggslog::sggs::{DerivationConfig, DerivationState, InitialInterpretation};
use sggslog::syntax::{Clause, Literal, Term};
use sggslog::theory::Theory;

fn make_non_unit_unsat_theory() -> Theory {
    let mut theory = Theory::new();
    // Clause 1: p(a) ∨ q(b)
    theory.add_clause(Clause::new(vec![
        Literal::pos("p", vec![Term::constant("a")]),
        Literal::pos("q", vec![Term::constant("b")]),
    ]));
    // Clause 2: ¬p(a) ∨ ¬q(b)
    theory.add_clause(Clause::new(vec![
        Literal::neg("p", vec![Term::constant("a")]),
        Literal::neg("q", vec![Term::constant("b")]),
    ]));
    theory
}

/// Detailed step-by-step trace of the derivation
#[test]
fn trace_non_unit_unsat_derivation() {
    let theory = make_non_unit_unsat_theory();
    println!("\n=== Theory ===");
    for (i, clause) in theory.clauses().iter().enumerate() {
        println!("  Clause {}: {:?}", i, clause);
    }

    let config = DerivationConfig {
        timeout_ms: None,
        initial_interp: InitialInterpretation::AllNegative,
    };
    let mut state = DerivationState::new(theory, config);

    for step_num in 0..30 {
        println!("\n=== Step {} ===", step_num);

        // Print trail before
        println!("Trail before ({} clauses):", state.trail().len());
        for (i, cc) in state.trail().clauses().iter().enumerate() {
            let selected_lit = cc.selected_literal();
            println!(
                "  [{}] {:?} | selected: {} = {:?} | constraint: {:?}",
                i, cc.clause, cc.selected, selected_lit, cc.constraint
            );
        }

        // Execute step
        let step_result = state.step();

        match &step_result {
            Some(step) => {
                println!("Step result: {:?}", step.rule);
                println!(
                    "  trail_len: {} -> {}",
                    step.trail_len_before, step.trail_len_after
                );
            }
            None => {
                println!("Step result: None (derivation complete)");
            }
        }

        // Check for result
        if let Some(result) = state.result() {
            println!("\n=== DERIVATION RESULT: {:?} ===", result);

            // Print final trail
            println!("\nFinal trail ({} clauses):", state.trail().len());
            for (i, cc) in state.trail().clauses().iter().enumerate() {
                let selected_lit = cc.selected_literal();
                println!("  [{}] {:?} | selected: {:?}", i, cc.clause, selected_lit,);
            }
            return;
        }

        if step_result.is_none() {
            println!("\n=== DERIVATION COMPLETE (no result set) ===");
            return;
        }
    }

    println!("\n=== STOPPED AFTER 30 STEPS ===");
}

/// Test what happens with just one clause - should saturate
#[test]
fn single_clause_saturates() {
    let mut theory = Theory::new();
    theory.add_clause(Clause::new(vec![
        Literal::pos("p", vec![Term::constant("a")]),
        Literal::pos("q", vec![Term::constant("b")]),
    ]));

    let config = DerivationConfig::default();
    let mut state = DerivationState::new(theory, config);

    for step_num in 0..10 {
        let step = state.step();
        println!(
            "Step {}: {:?}, result: {:?}",
            step_num,
            step,
            state.result()
        );
        if step.is_none() || state.result().is_some() {
            break;
        }
    }

    println!("Final result: {:?}", state.result());
    println!("Trail: {:?}", state.trail());
}

/// Test similar unsatisfiable theory that SHOULD work: propositional case
#[test]
fn propositional_non_unit_unsat() {
    let mut theory = Theory::new();
    // p ∨ q
    theory.add_clause(Clause::new(vec![
        Literal::pos("p", vec![]),
        Literal::pos("q", vec![]),
    ]));
    // ¬p ∨ ¬q
    theory.add_clause(Clause::new(vec![
        Literal::neg("p", vec![]),
        Literal::neg("q", vec![]),
    ]));

    println!("\n=== Propositional case: (p∨q) ∧ (¬p∨¬q) ===");

    let config = DerivationConfig {
        timeout_ms: Some(5000),
        initial_interp: InitialInterpretation::AllNegative,
    };
    let mut state = DerivationState::new(theory, config);

    for step_num in 0..30 {
        println!("\n--- Step {} ---", step_num);
        println!("Trail ({} clauses):", state.trail().len());
        for (i, cc) in state.trail().clauses().iter().enumerate() {
            println!("  [{}] {:?} | sel: {:?}", i, cc.clause, cc.selected_literal());
        }

        let step = state.step();
        println!("Step: {:?}", step);

        if let Some(result) = state.result() {
            println!("\n=== Result: {:?} ===", result);
            return;
        }
        if step.is_none() {
            break;
        }
    }

    println!("\nFinal trail: {:?}", state.trail());
    println!("Final result: {:?}", state.result());
}

/// Test the simplest 4-clause unsatisfiable theory
/// This is the "harder_unsatisfiable" case from the other test file
#[test]
fn four_clause_propositional_unsat() {
    let mut theory = Theory::new();
    // (p∨q) ∧ (¬p∨q) ∧ (p∨¬q) ∧ (¬p∨¬q)
    theory.add_clause(Clause::new(vec![
        Literal::pos("p", vec![]),
        Literal::pos("q", vec![]),
    ]));
    theory.add_clause(Clause::new(vec![
        Literal::neg("p", vec![]),
        Literal::pos("q", vec![]),
    ]));
    theory.add_clause(Clause::new(vec![
        Literal::pos("p", vec![]),
        Literal::neg("q", vec![]),
    ]));
    theory.add_clause(Clause::new(vec![
        Literal::neg("p", vec![]),
        Literal::neg("q", vec![]),
    ]));

    println!("\n=== 4-clause: (p∨q)∧(¬p∨q)∧(p∨¬q)∧(¬p∨¬q) ===");

    let config = DerivationConfig {
        timeout_ms: Some(5000),
        initial_interp: InitialInterpretation::AllNegative,
    };
    let mut state = DerivationState::new(theory, config);

    for step_num in 0..50 {
        let step = state.step();
        if step_num % 5 == 0 || state.result().is_some() {
            println!("Step {}: {:?}, trail_len={}", step_num, step, state.trail().len());
        }

        if let Some(result) = state.result() {
            println!("\n=== Result: {:?} (at step {}) ===", result, step_num);
            return;
        }
        if step.is_none() {
            break;
        }
    }

    println!("\nFinal result: {:?}", state.result());
}
