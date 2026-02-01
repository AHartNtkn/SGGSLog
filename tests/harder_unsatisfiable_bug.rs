//! Tests for diagnosing and preventing the harder_unsatisfiable infinite loop bug.
//!
//! # The Bug
//!
//! `derive()` loops infinitely on `(p∨q) ∧ (¬p∨q) ∧ (p∨¬q) ∧ (¬p∨¬q)`.
//! This theory is unsatisfiable and should derive the empty clause.
//!
//! # Root Cause Analysis
//!
//! ## Summary
//!
//! The infinite loop is caused by Extension repeatedly adding the same clause
//! with the same selected literal, then Deletion removing it because it creates
//! a non-disjoint trail. This cycle repeats forever.
//!
//! ## Detailed Mechanism
//!
//! ### Step-by-step trace with theory containing just `(p ∨ q)`:
//!
//! 1. **Initial state**: Empty trail, InitialInterpretation::AllNegative
//!
//! 2. **Extension adds (p∨q) with p selected**:
//!    - Theory clause `(p ∨ q)` has no I-true literals (both p and q are positive,
//!      hence I-false under AllNegative)
//!    - No side premises needed (n=0 case)
//!    - `is_redundant_extension` returns `false` (trail is empty, nothing covered)
//!    - `find_selected_literal` returns index 0 (p)
//!    - Trail becomes: `[(p ∨ q) with p selected]`
//!
//! 3. **Extension adds (p∨q) AGAIN with p selected** (THE BUG):
//!    - Same theory clause `(p ∨ q)` is tried again
//!    - `is_redundant_extension` is called with extended literals `[p, q]`:
//!      - Check if `p` is in partial interpretation → **YES** (p is selected)
//!      - Check if `q` is in partial interpretation → **NO** (q is not selected, different predicate)
//!      - Since NOT all I-false literals are covered, returns `false` → "not redundant"
//!    - `find_selected_literal` is called:
//!      - For `p`: `has_proper_instances` checks if `¬p` is in partial → **NO** → "has proper instances"
//!      - Returns index 0 (p) **AGAIN**
//!    - Trail becomes: `[(p ∨ q) with p], [(p ∨ q) with p]`
//!
//! 4. **Disjoint prefix shrinks**:
//!    - Two clauses have the same selected literal `p`
//!    - `disjoint_prefix_length()` returns 1 (clauses 0 and 1 have overlapping selected literals)
//!
//! 5. **Deletion removes the second clause**:
//!    - Clause at index 1 is outside `dp(Γ)` (disjoint prefix is only length 1)
//!    - Deletion removes it
//!    - Trail becomes: `[(p ∨ q) with p]`
//!
//! 6. **Back to step 3** → infinite loop
//!
//! ## The Two Interacting Bugs
//!
//! ### Bug 1: `is_redundant_extension()` (src/sggs/extension.rs:263-291)
//!
//! The function checks if ALL I-false literals in the extended clause are in the
//! partial interpretation. However, the partial interpretation only contains the
//! SELECTED literals, not all I-false literals. So for clause `(p ∨ q)`:
//!
//! - After first extension, only `p` is selected
//! - `partial.contains_ground(&p)` returns true
//! - `partial.contains_ground(&q)` returns false (q has a different predicate!)
//! - Function concludes "not all covered" → returns false (not redundant)
//!
//! This check is fundamentally flawed: it will NEVER return true for multi-literal
//! clauses because only ONE literal can be selected at a time.
//!
//! ### Bug 2: `find_selected_literal()` / `has_proper_instances()` (src/sggs/extension.rs:294-333)
//!
//! The function checks if the COMPLEMENT of a literal is in the partial interpretation.
//! For positive literal `p`, it checks if `¬p` is in partial.
//!
//! Under AllNegative, the partial interpretation only contains POSITIVE selected literals.
//! So `¬p` (a negative literal) will NEVER be in the partial interpretation.
//!
//! This means `has_proper_instances(p)` always returns true, and `p` is always selected,
//! even if `p` is already selected on the trail.
//!
//! ## Why This Causes an Infinite Loop
//!
//! The combination of these two bugs creates a perfect storm:
//!
//! 1. `is_redundant_extension` fails to recognize that re-adding `(p ∨ q)` with `p`
//!    selected is pointless (the new clause contributes nothing new to the model)
//!
//! 2. `find_selected_literal` keeps choosing `p` because it only checks if the
//!    complement `¬p` is in partial (it never is under AllNegative)
//!
//! 3. The trail grows to `[(p ∨ q), (p ∨ q)]` with both selecting `p`
//!
//! 4. This violates the disjoint prefix invariant (same atom selected twice)
//!
//! 5. Deletion removes the duplicate to restore the invariant
//!
//! 6. Extension adds it right back (steps 1-2 repeat forever)
//!
//! ## Potential Fixes
//!
//! ### Fix A: Prevent duplicate extensions
//!
//! Before extending with a clause, check if the SAME clause with the SAME selected
//! literal is already on the trail. This would block step 3 entirely.
//!
//! ### Fix B: Select a different literal
//!
//! When `p` is already selected on the trail, `find_selected_literal` should prefer
//! `q` instead. The clause `(p ∨ q)` with `q` selected contributes new information
//! (making `q` true in the model).
//!
//! ### Fix C: Fix the redundancy check
//!
//! `is_redundant_extension` should check if the SELECTED literal of the new extension
//! is already uniformly true in the trail interpretation, not whether all I-false
//! literals are in the partial interpretation.

use sggslog::sggs::{
    derive, derive_with_trace, DerivationConfig, DerivationResult, DerivationState,
    InitialInterpretation, InferenceRule,
};
use sggslog::syntax::{Clause, Literal};
use sggslog::theory::Theory;

fn make_harder_unsatisfiable_theory() -> Theory {
    // (p∨q) ∧ (¬p∨q) ∧ (p∨¬q) ∧ (¬p∨¬q)
    let mut theory = Theory::new();
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
    theory
}

/// Test that the simple unsatisfiable case works (p ∧ ¬p)
#[test]
fn simple_unsatisfiable_terminates() {
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

/// Test derivation step-by-step with limited iterations
#[test]
fn harder_unsatisfiable_limited_steps() {
    let theory = make_harder_unsatisfiable_theory();
    let config = DerivationConfig {
        timeout_ms: None,
        initial_interp: InitialInterpretation::AllNegative,
    };

    let mut state = DerivationState::new(theory.clone(), config);
    let max_steps = 20; // Reduced for detailed output

    let mut step_count = 0;

    for _ in 0..max_steps {
        println!("\n=== Before step {} ===", step_count + 1);
        println!("Trail length: {}", state.trail().len());
        println!("Trail clauses:");
        for (i, clause) in state.trail().clauses().iter().enumerate() {
            let selected = clause.selected_literal();
            println!(
                "  [{}] selected[{}]={:?} constraint={:?} clause={:?}",
                i,
                clause.selected,
                selected,
                clause.constraint,
                clause.clause.literals
            );
        }
        println!("Disjoint prefix length: {}", state.trail().disjoint_prefix_length());
        println!("Conflict: {:?}", state.trail().find_conflict());

        if let Some(result) = state.result() {
            println!("Derivation finished after {} steps: {:?}", step_count, result);
            if matches!(result, DerivationResult::Unsatisfiable) {
                return; // Success!
            } else {
                panic!("Expected Unsatisfiable, got {:?}", result);
            }
        }

        match state.step() {
            Some(step) => {
                step_count += 1;
                println!(
                    "Step {}: {:?}, trail {} -> {}",
                    step_count, step.rule, step.trail_len_before, step.trail_len_after
                );
            }
            None => {
                println!("No more steps after {} steps", step_count);
                // step() returning None may have set the result - check again
                if let Some(result) = state.result() {
                    println!("Derivation finished after {} steps: {:?}", step_count, result);
                    if matches!(result, DerivationResult::Unsatisfiable) {
                        return; // Success!
                    } else {
                        panic!("Expected Unsatisfiable, got {:?}", result);
                    }
                }
                panic!(
                    "Derivation stuck after {} steps without result",
                    step_count
                );
            }
        }
    }

    panic!(
        "Did not terminate within {} steps. This indicates an infinite loop.",
        max_steps
    );
}

/// Check if extension keeps adding the same clauses
#[test]
fn extension_does_not_readd_same_clause() {
    let mut theory = Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos("p", vec![])]));

    let config = DerivationConfig {
        timeout_ms: None,
        initial_interp: InitialInterpretation::AllNegative,
    };

    let mut state = DerivationState::new(theory.clone(), config);
    let mut extension_count = 0;

    for _ in 0..10 {
        if let Some(step) = state.step() {
            if step.rule == InferenceRule::Extension {
                extension_count += 1;
            }
        } else {
            break;
        }
    }

    // A single-clause satisfiable theory should only extend once
    assert!(
        extension_count <= 1,
        "Extension should not re-add the same clause. Got {} extensions",
        extension_count
    );
}

/// Test with just two clauses that should derive q
#[test]
fn two_clause_resolution() {
    // (p∨q) ∧ (¬p∨q) should derive q
    let mut theory = Theory::new();
    theory.add_clause(Clause::new(vec![
        Literal::pos("p", vec![]),
        Literal::pos("q", vec![]),
    ]));
    theory.add_clause(Clause::new(vec![
        Literal::neg("p", vec![]),
        Literal::pos("q", vec![]),
    ]));

    let config = DerivationConfig {
        timeout_ms: Some(1000),
        initial_interp: InitialInterpretation::AllNegative,
    };
    let result = derive(&theory, config);

    // This should be satisfiable with q=true
    assert!(
        matches!(result, DerivationResult::Satisfiable(_)),
        "(p∨q) ∧ (¬p∨q) should be satisfiable, got {:?}",
        result
    );
}

/// Test with three clauses that should still be satisfiable
#[test]
fn three_clause_satisfiable() {
    // (p∨q) ∧ (¬p∨q) ∧ (p∨¬q) - satisfiable with p=true, q=true
    let mut theory = Theory::new();
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

    let config = DerivationConfig {
        timeout_ms: Some(1000),
        initial_interp: InitialInterpretation::AllNegative,
    };
    let result = derive(&theory, config);

    assert!(
        matches!(result, DerivationResult::Satisfiable(_)),
        "Three clauses should be satisfiable, got {:?}",
        result
    );
}

// =============================================================================
// ROOT CAUSE ANALYSIS TESTS
// =============================================================================
//
// The infinite loop bug has TWO interacting causes:
//
// CAUSE 1: is_redundant_extension() uses incomplete coverage check
// -----------------------------------------------------------------
// The function checks if ALL I-false literals in a clause are in the partial
// interpretation. For clause (p∨q):
//   - After first extension, p is selected → p is in partial, q is NOT
//   - is_redundant_extension sees: p covered, q NOT covered → "not redundant"
//   - This allows re-extending with the same clause
//
// CAUSE 2: find_selected_literal() picks the same literal again
// --------------------------------------------------------------
// The function checks has_proper_instances(lit) which tests if ¬lit is in
// the partial interpretation. For p:
//   - ¬p is NOT in partial (partial only contains positive selected literals)
//   - Therefore p "has proper instances" → selected again
// The result: same clause, same selected literal → duplicate on trail
//
// INTERACTION: Extension adds duplicate → Deletion removes it → repeat forever
// =============================================================================

/// Demonstrates the exact bug: trail oscillation between Extension and Deletion
///
/// This test captures the infinite loop pattern:
/// 1. Extension adds (p∨q) with p selected
/// 2. Extension adds (p∨q) AGAIN with p selected (BUG: should not happen)
/// 3. Trail has two clauses with same selected literal → dp(Γ) = 1
/// 4. Deletion removes second clause (outside disjoint prefix)
/// 5. Back to step 2, forever
#[test]
fn bug_demo_extension_adds_duplicate_clause() {
    use sggslog::sggs::Trail;

    // Single clause theory: just (p ∨ q)
    let mut theory = Theory::new();
    theory.add_clause(Clause::new(vec![
        Literal::pos("p", vec![]),
        Literal::pos("q", vec![]),
    ]));

    let config = DerivationConfig {
        timeout_ms: None,
        initial_interp: InitialInterpretation::AllNegative,
    };

    let mut state = DerivationState::new(theory.clone(), config);

    // Step 1: Extension adds (p∨q)
    let step1 = state.step().expect("First step should succeed");
    assert_eq!(step1.rule, InferenceRule::Extension);
    assert_eq!(state.trail().len(), 1);

    let first_selected = state.trail().clauses()[0].selected_literal().clone();
    println!("After step 1: trail has 1 clause, selected = {:?}", first_selected);

    // Step 2: This is where the bug manifests
    // Extension should NOT add the same clause again with the same selected literal
    // But it does, because:
    //   - is_redundant_extension returns false (q is not in partial)
    //   - find_selected_literal returns p again (¬p is not in partial)
    if let Some(step2) = state.step() {
        if step2.rule == InferenceRule::Extension && state.trail().len() == 2 {
            let second_selected = state.trail().clauses()[1].selected_literal().clone();
            println!("After step 2: trail has 2 clauses");
            println!("  [0] selected = {:?}", first_selected);
            println!("  [1] selected = {:?}", second_selected);

            // THE BUG: both clauses have the same selected literal
            if first_selected.positive == second_selected.positive
                && first_selected.atom.predicate == second_selected.atom.predicate
            {
                // Verify the disjoint prefix is less than trail length
                let dp = state.trail().disjoint_prefix_length();
                println!("Disjoint prefix = {}, trail length = 2", dp);
                assert!(
                    dp < 2,
                    "Duplicate selected literals should cause dp(Γ) < len(Γ)"
                );

                // This confirms the bug: extension added a duplicate
                panic!(
                    "BUG CONFIRMED: Extension added (p∨q) twice with same selected literal '{}'.\n\
                     CAUSE 1: is_redundant_extension() returned false because q is not in partial.\n\
                     CAUSE 2: find_selected_literal() chose p again because ¬p is not in partial.\n\
                     EFFECT: Deletion will remove the duplicate, Extension will add it again → infinite loop.",
                    first_selected.atom.predicate
                );
            }
        }
    }

    // If we get here, the bug didn't manifest (either fixed or different behavior)
    println!("No duplicate extension detected - bug may be fixed");
}

/// Shows that partial interpretation only contains selected literals, not all I-false literals
#[test]
fn partial_interpretation_only_contains_selected_literals() {
    use sggslog::constraint::Constraint;
    use sggslog::sggs::{ConstrainedClause, Trail};

    let mut trail = Trail::new(InitialInterpretation::AllNegative);

    // Add (p ∨ q) with p selected (index 0)
    let clause = Clause::new(vec![
        Literal::pos("p", vec![]),
        Literal::pos("q", vec![]),
    ]);
    let cc = ConstrainedClause::with_constraint(clause, Constraint::True, 0);
    trail.push(cc);

    let partial = trail.partial_interpretation();

    // p is selected, should be in partial
    let p = Literal::pos("p", vec![]);
    let p_in_partial = partial.contains_ground(&p);
    println!("p in partial: {}", p_in_partial);
    assert!(p_in_partial, "Selected literal p should be in partial interpretation");

    // q is NOT selected (it's a non-selected literal), should NOT be in partial
    let q = Literal::pos("q", vec![]);
    let q_in_partial = partial.contains_ground(&q);
    println!("q in partial: {}", q_in_partial);
    assert!(
        !q_in_partial,
        "Non-selected literal q should NOT be in partial interpretation"
    );

    // This is correct behavior! The partial interpretation only contains
    // proper constrained ground instances of SELECTED literals.
    // The bug is that is_redundant_extension checks if ALL I-false literals
    // are in partial, but only the SELECTED one can possibly be there.
}
