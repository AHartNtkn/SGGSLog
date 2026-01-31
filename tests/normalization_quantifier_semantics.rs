use sggslog::normalize::{clausify_formula, clausify_statements};
use sggslog::parser::{parse_file, Statement};
use sggslog::syntax::{Clause, Literal, Term};

fn single_formula(src: &str) -> sggslog::syntax::Formula {
    let stmts = parse_file(src).expect("parse_file failed");
    assert_eq!(stmts.len(), 1, "expected one statement");
    match &stmts[0] {
        Statement::Formula(f) => f.clone(),
        other => panic!("expected a formula statement, got {:?}", other),
    }
}

fn clausify_all(src: &str) -> Vec<Clause> {
    let formula = single_formula(src);
    let clauses = clausify_formula(&formula).expect("clausify_formula failed");
    assert!(!clauses.is_empty(), "expected at least one clause");
    clauses
}

fn find_clause_with_predicate(clauses: &[Clause], pred: &str) -> Clause {
    clauses
        .iter()
        .find(|c| c.literals.iter().any(|l| l.atom.predicate == pred))
        .cloned()
        .expect("no clause contained expected predicate")
}

fn first_literal_with_predicate<'a>(clause: &'a Clause, pred: &str) -> &'a Literal {
    clause
        .literals
        .iter()
        .find(|l| l.atom.predicate == pred)
        .expect("expected literal with predicate")
}

#[test]
fn test_skolemization_respects_shadowing_scope() {
    // Shadowed variable: inner ∃X is distinct from outer ∀X; skolem depends on the universal.
    let clauses = clausify_all("∀X ∃X (p X)");
    let clause = find_clause_with_predicate(&clauses, "p");
    let lit = first_literal_with_predicate(&clause, "p");
    match &lit.atom.args[0] {
        Term::App(sym, args) if sym.arity == 0 && args.is_empty() => {}
        _ => panic!("expected Skolem constant: inner ∃X is not in scope of any universal"),
    }
    let vars = clause.variables().len();
    assert_eq!(vars, 0, "outer ∀X is unused after shadowing");
}

#[test]
fn test_skolem_constant_shared_across_conjunction() {
    // ∃X (p X ∧ q X) should introduce one Skolem constant shared across clauses.
    let stmts = parse_file("∃X (p X ∧ q X)").expect("parse_file failed");
    let clauses = clausify_statements(&stmts).expect("clausify_statements failed");
    let p_clause = find_clause_with_predicate(&clauses, "p");
    let q_clause = find_clause_with_predicate(&clauses, "q");

    let p_lit = first_literal_with_predicate(&p_clause, "p");
    let q_lit = first_literal_with_predicate(&q_clause, "q");

    let p_sk = match &p_lit.atom.args[0] {
        Term::App(sym, args) if sym.arity == 0 && args.is_empty() => sym.name.clone(),
        _ => panic!("expected Skolem constant"),
    };
    let q_sk = match &q_lit.atom.args[0] {
        Term::App(sym, args) if sym.arity == 0 && args.is_empty() => sym.name.clone(),
        _ => panic!("expected Skolem constant"),
    };
    assert_eq!(
        p_sk, q_sk,
        "same existential should yield same Skolem symbol"
    );
}
