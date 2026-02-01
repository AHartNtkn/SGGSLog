// Trace derivation for satisfiable_datalog
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
    let mut state = DerivationState::new(theory, config);
    
    println!("=== Tracing Derivation ===\n");
    
    for i in 0..30 {
        println!("--- Step {} ---", i);
        
        // Show trail state before step
        println!("Trail ({} clauses):", state.trail().len());
        for (idx, cc) in state.trail().clauses().iter().enumerate() {
            let sel = cc.selected_literal();
            let init_interp = state.trail().initial_interpretation();
            let is_false = init_interp.is_false(sel);
            println!("  [{}] {:?} (sel: {:?}, I-false: {})", 
                     idx, &cc.clause, sel, is_false);
        }
        
        let step = state.step();
        println!("Step result: {:?}", step);
        
        if let Some(result) = state.result() {
            println!("\nDerivation complete: {:?}", result);
            break;
        }
        
        if step.is_none() {
            println!("\nNo more steps available");
            break;
        }
        
        println!();
    }
}
