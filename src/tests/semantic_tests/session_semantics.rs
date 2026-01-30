use super::*;

// =============================================================================
// SESSION / END-TO-END API SEMANTICS
// =============================================================================

use crate::parser::{Statement, Directive};
use crate::session::{ExecResult, Session};
use crate::session::DirectiveResult;
use crate::syntax::{Atom, Formula};
use std::fs;
use std::time::{SystemTime, UNIX_EPOCH};

#[test]
fn session_executes_clause_statement() {
    let mut session = Session::new();
    let clause = Clause::new(vec![Literal::pos("p", vec![])]);
    let stmt = Statement::Clause(clause.clone());

    let result = session.execute_statement(stmt).expect("execute_statement failed");
    assert!(matches!(result, ExecResult::ClauseAdded));
    assert_eq!(session.theory().clauses().len(), 1);
    assert_eq!(session.theory().clauses()[0], clause);
}

#[test]
fn session_executes_formula_statement() {
    let mut session = Session::new();
    let formula = Formula::atom(Atom::prop("p"));
    let stmt = Statement::Formula(formula);

    let result = session.execute_statement(stmt).expect("execute_statement failed");
    assert!(matches!(result, ExecResult::ClauseAdded));
    assert!(session
        .theory()
        .clauses()
        .iter()
        .any(|c| c.literals == vec![Literal::pos("p", vec![])]));
}

#[test]
fn session_executes_query_statement() {
    let mut session = Session::new();
    let stmt = Statement::Query(vec![Literal::pos("p", vec![])]);
    let result = session.execute_statement(stmt).expect("execute_statement failed");
    assert!(matches!(result, ExecResult::QueryResult(_)));
}

#[test]
fn session_applies_set_directive() {
    let mut session = Session::new();
    let stmt = Statement::Directive(Directive::Set("max_steps".to_string(), "10".to_string()));
    let result = session.execute_statement(stmt).expect("execute_statement failed");
    assert!(matches!(result, ExecResult::DirectiveApplied(_)));
    assert_eq!(session.config().max_steps, Some(10));
}

#[test]
fn session_sets_initial_interpretation() {
    let mut session = Session::new();
    let stmt = Statement::Directive(Directive::Set(
        "initial_interp".to_string(),
        "positive".to_string(),
    ));
    let result = session.execute_statement(stmt).expect("execute_statement failed");
    assert!(matches!(result, ExecResult::DirectiveApplied(_)));
    assert!(matches!(
        session.config().initial_interp,
        crate::sggs::InitialInterpretation::AllPositive
    ));
}

#[test]
fn session_execute_query_on_empty_theory() {
    let mut session = Session::new();
    let stmt = Statement::Query(vec![Literal::pos("p", vec![Term::constant("a")])]);
    let result = session.execute_statement(stmt).expect("execute_statement failed");
    assert!(matches!(result, ExecResult::QueryResult(_)));
}

#[test]
fn session_load_file_error_does_not_mutate_theory() {
    let mut session = Session::new();
    let before = session.theory().clauses().len();
    let err = session.load_file("/nonexistent/path.sggs").expect_err("expected error");
    assert!(!err.message.is_empty());
    let after = session.theory().clauses().len();
    assert_eq!(before, after, "theory should be unchanged on load error");
}

#[test]
fn session_load_file_adds_clauses() {
    let mut session = Session::new();
    let before = session.theory().clauses().len();
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time")
        .as_nanos();
    let path = std::env::temp_dir().join(format!("sggslog_test_{}.sggs", unique));
    fs::write(&path, "p\nq\n").expect("write test file");

    let result = session
        .load_file(path.to_str().expect("path string"))
        .expect("load_file failed");
    match result {
        DirectiveResult::Loaded { path: loaded, clauses } => {
            assert!(loaded.contains("sggslog_test_"), "loaded path should be reported");
            assert_eq!(clauses, 2, "load_file should report number of clauses added");
        }
        other => panic!("Expected Loaded directive result, got {:?}", other),
    }
    let after = session.theory().clauses().len();
    assert_eq!(after, before + 2, "load_file should add clauses to theory");

    let _ = fs::remove_file(&path);
}

#[test]
fn session_load_file_normalizes_formulas() {
    let mut session = Session::new();
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time")
        .as_nanos();
    let path = std::env::temp_dir().join(format!("sggslog_norm_{}.sggs", unique));
    fs::write(&path, "p -> q\n").expect("write test file");

    let _ = session
        .load_file(path.to_str().expect("path string"))
        .expect("load_file failed");

    let expected = Clause::new(vec![
        Literal::neg("p", vec![]),
        Literal::pos("q", vec![]),
    ]);
    let expected_set: std::collections::HashSet<_> = expected.literals.into_iter().collect();
    let found = session.theory().clauses().iter().any(|c| {
        let got: std::collections::HashSet<_> = c.literals.iter().cloned().collect();
        got == expected_set
    });
    assert!(found, "expected normalized clause ¬p ∨ q");

    let _ = fs::remove_file(&path);
}
