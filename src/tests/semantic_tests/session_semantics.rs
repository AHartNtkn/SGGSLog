use super::*;

// =============================================================================
// SESSION / END-TO-END API SEMANTICS
// =============================================================================

use crate::parser::{Statement, Directive};
use crate::session::{ExecResult, Session};

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
