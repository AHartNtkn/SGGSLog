// Trace extension for satisfiable_datalog
use sggslog::sggs::{DerivationConfig, DerivationState, InitialInterpretation};
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
    
    println!("Theory clauses:");
    for (i, c) in theory.clauses().iter().enumerate() {
        println!("  [{}] {:?}", i, c);
    }
    println!();
    
    let config = DerivationConfig::default();
    let mut state = DerivationState::new(theory.clone(), config);
    
    // Run a few steps
    for _ in 0..4 {
        state.step();
    }
    
    // Check which theory clauses are satisfied
    println!("\n=== Checking theory clause satisfaction ===");
    let interp = state.trail().interpretation();
    
    for (i, clause) in theory.clauses().iter().enumerate() {
        println!("\nTheory clause [{}]: {:?}", i, clause);
        
        let mut satisfied = false;
        for lit in &clause.literals {
            let unif_true = interp.is_uniformly_true(lit);
            let unif_false = interp.is_uniformly_false(lit);
            println!("  Literal {:?}: uniformly_true={}, uniformly_false={}", lit, unif_true, unif_false);
            if unif_true {
                satisfied = true;
            }
        }
        println!("  Clause satisfied: {}", satisfied);
    }
    
    println!("\n=== Trail completeness check ===");
    println!("is_complete: {}", state.trail().is_complete(&theory));
}
