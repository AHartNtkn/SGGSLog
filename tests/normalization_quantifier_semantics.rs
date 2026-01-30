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

fn clausify_single(src: &str) -> Clause {
    let formula = single_formula(src);
    let clauses = clausify_formula(&formula).expect("clausify_formula failed");
    assert_eq!(clauses.len(), 1, "expected one clause");
    clauses[0].clone()
}

#[test]
fn test_skolemization_respects_shadowing_scope() {
    // Shadowed variable: inner ∃X is distinct from outer ∀X; skolem depends on the universal.
    let clause = clausify_single("∀X ∃X (p X)");
    assert_eq!(clause.literals.len(), 1);
    let lit = &clause.literals[0];
    match &lit.atom.args[0] {
        Term::App(_, args) => {
            assert_eq!(args.len(), 1, "Skolem function should depend on one universal");
            assert!(matches!(&args[0], Term::Var(_)), "argument should be a variable");
        }
        _ => panic!("expected Skolem function application"),
    }
    assert_eq!(clause.variables().len(), 1, "only the outer universal should remain");
}

#[test]
fn test_skolem_constant_shared_across_conjunction() {
    // ∃X (p X ∧ q X) should introduce one Skolem constant shared across clauses.
    let stmts = parse_file("∃X (p X ∧ q X)").expect("parse_file failed");
    let clauses = clausify_statements(&stmts).expect("clausify_statements failed");
    assert_eq!(clauses.len(), 2);

    let mut skolem_names = Vec::new();
    for c in &clauses {
        assert_eq!(c.literals.len(), 1);
        match &c.literals[0].atom.args[0] {
            Term::Const(cn) => skolem_names.push(cn.name().to_string()),
            Term::App(sym, args) if sym.arity == 0 && args.is_empty() => {
                skolem_names.push(sym.name.clone())
            }
            _ => panic!("expected Skolem constant"),
        }
    }
    assert_eq!(skolem_names[0], skolem_names[1], "same existential should yield same Skolem symbol");
}
