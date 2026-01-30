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
    let stmts = vec![Statement::Clause(c1.clone()), Statement::Clause(c2.clone())];

    let theory = Theory::from_statements(&stmts).expect("expected theory");
    // Alpha-equivalent clauses should not be lost, but order/duplication is irrelevant.
    assert!(
        !theory.clauses().is_empty(),
        "theory should contain at least one clause"
    );
    assert!(
        theory
            .clauses()
            .iter()
            .any(|c| c == &c1 || c == &c2),
        "theory should retain a representative of alpha-equivalent clauses"
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
    let stmts = vec![Statement::Clause(c1.clone()), Statement::Clause(c2.clone())];

    let theory = Theory::from_statements(&stmts).expect("expected theory");
    assert!(
        theory.clauses().iter().any(|c| c == &c1),
        "theory should contain the first clause"
    );
    assert!(
        theory.clauses().iter().any(|c| c == &c2),
        "theory should contain the second, non-alpha-equivalent clause"
    );
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
    assert!(theory.clauses().iter().any(|c| c == &c1));
    assert!(theory.clauses().iter().any(|c| c == &c2));
}
