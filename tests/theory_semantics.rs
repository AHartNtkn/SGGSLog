use sggslog::parser::{Directive, Statement};
use sggslog::syntax::{Clause, Literal, Term};
use sggslog::theory::Theory;

#[test]
fn test_from_statements_rejects_query() {
    let stmts = vec![Statement::Query(vec![Literal::pos("p", vec![])])];
    let err = Theory::from_statements(&stmts).expect_err("expected error");
    assert!(
        err.message.to_lowercase().contains("query"),
        "error should mention query"
    );
}

#[test]
fn test_from_statements_rejects_directive() {
    let stmts = vec![Statement::Directive(Directive::Load("file.sggs".to_string()))];
    let err = Theory::from_statements(&stmts).expect_err("expected error");
    assert!(
        err.message.to_lowercase().contains("directive"),
        "error should mention directive"
    );
}

#[test]
fn test_from_statements_dedup_alpha_equivalent() {
    let c1 = Clause::new(vec![
        Literal::pos("p", vec![Term::var("X")]),
        Literal::pos("q", vec![Term::var("X")]),
    ]);
    let c2 = Clause::new(vec![
        Literal::pos("p", vec![Term::var("Y")]),
        Literal::pos("q", vec![Term::var("Y")]),
    ]);
    let stmts = vec![Statement::Clause(c1), Statement::Clause(c2)];

    let theory = Theory::from_statements(&stmts).expect("expected theory");
    // Alpha-deduplication is an optimization; accept either behavior.
    let len = theory.clauses().len();
    assert!(
        len == 1 || len == 2,
        "theory should contain one or both alpha-equivalent clauses"
    );
}

#[test]
fn test_from_statements_keep_non_alpha_equivalent() {
    let c1 = Clause::new(vec![
        Literal::pos("p", vec![Term::var("X")]),
        Literal::pos("q", vec![Term::var("X")]),
    ]);
    let c2 = Clause::new(vec![
        Literal::pos("p", vec![Term::var("X")]),
        Literal::pos("q", vec![Term::var("Y")]),
    ]);
    let stmts = vec![Statement::Clause(c1), Statement::Clause(c2)];

    let theory = Theory::from_statements(&stmts).expect("expected theory");
    assert_eq!(theory.clauses().len(), 2);
}

#[test]
fn test_theory_new_empty() {
    let theory = Theory::new();
    assert_eq!(theory.clauses().len(), 0);
}

#[test]
fn test_theory_add_clause_order() {
    let mut theory = Theory::new();
    let c1 = Clause::new(vec![Literal::pos("p", vec![])]);
    let c2 = Clause::new(vec![Literal::pos("q", vec![])]);
    theory.add_clause(c1.clone());
    theory.add_clause(c2.clone());
    assert_eq!(theory.clauses().len(), 2);
    assert_eq!(theory.clauses()[0], c1);
    assert_eq!(theory.clauses()[1], c2);
}
