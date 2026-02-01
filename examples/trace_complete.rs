// Trace is_complete check for satisfiable_datalog
use sggslog::sggs::{DerivationConfig, DerivationState};
use sggslog::syntax::{Clause, Literal, Term};
use sggslog::theory::Theory;

fn main() {
    let a = Term::constant("a");
    let b = Term::constant("b");
    let c = Term::constant("c");

    let mut theory = Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos("edge", vec![a.clone(), b.clone()])]));
    theory.add_clause(Clause::new(vec![Literal::pos("edge", vec![b.clone(), c.clone()])]));
    theory.add_clause(Clause::new(vec![
        Literal::neg("edge", vec![Term::var("X"), Term::var("Y")]),
        Literal::pos("path", vec![Term::var("X"), Term::var("Y")]),
    ]));
    theory.add_clause(Clause::new(vec![
        Literal::neg("path", vec![Term::var("X"), Term::var("Y")]),
        Literal::neg("edge", vec![Term::var("Y"), Term::var("Z")]),
        Literal::pos("path", vec![Term::var("X"), Term::var("Z")]),
    ]));

    let config = DerivationConfig::default();
    let mut state = DerivationState::new(theory.clone(), config);

    // Run until no more steps
    for _ in 0..10 {
        if state.step().is_none() {
            break;
        }
    }

    println!("=== Trail after derivation ===");
    for (idx, cc) in state.trail().clauses().iter().enumerate() {
        println!("  [{}] {:?}", idx, cc.clause);
        println!("      selected: {:?}", cc.selected_literal());
    }

    println!("\n=== Checking is_complete ===");
    let interp = state.trail().interpretation();

    for (i, clause) in theory.clauses().iter().enumerate() {
        println!("\nTheory clause [{}]: {:?}", i, clause);
        let mut satisfied = false;
        for lit in &clause.literals {
            let unif_true = interp.is_uniformly_true(lit);
            println!("  Literal {:?}: uniformly_true={}", lit, unif_true);
            if unif_true {
                satisfied = true;
            }
        }
        println!("  Clause satisfied: {}", satisfied);
    }

    println!("\n=== is_complete result: {} ===", state.trail().is_complete(&theory));
}
