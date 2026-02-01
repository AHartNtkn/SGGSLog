// Debug test for satisfiable_datalog
use sggslog::sggs::{derive, DerivationConfig, DerivationResult};
use sggslog::syntax::{Atom, Clause, Literal, Term};
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
    
    println!("Theory:");
    for clause in theory.clauses() {
        println!("  {:?}", clause);
    }
    
    let config = DerivationConfig::default();
    let result = derive(&theory, config);
    
    match result {
        DerivationResult::Satisfiable(model) => {
            println!("\nModel true_atoms:");
            for atom in &model.true_atoms {
                println!("  {:?}", atom);
            }
            println!("\nModel true_patterns:");
            for lit in &model.true_patterns {
                println!("  {:?}", lit);
            }
            
            let target = Atom::new("path", vec![a.clone(), c.clone()]);
            println!("\nLooking for: {:?}", target);
            println!("Found: {}", model.true_atoms.contains(&target));
        }
        DerivationResult::Timeout => {
            println!("Timeout!");
        }
        DerivationResult::Unsatisfiable => {
            println!("Unsatisfiable!");
        }
    }
}
