use super::*;

// =============================================================================
// SESSION / END-TO-END API SEMANTICS
// =============================================================================

use crate::parser::{Directive, Statement};
use crate::session::DirectiveResult;
use crate::session::{ExecResult, Session};
use crate::syntax::{Atom, Formula};
use std::fs;
use std::time::{SystemTime, UNIX_EPOCH};

fn term_uses_only_symbols(
    term: &Term,
    allowed_consts: &std::collections::HashSet<String>,
    allowed_funs: &std::collections::HashSet<String>,
) -> bool {
    match term {
        Term::Var(_) => true,
        Term::Const(c) => allowed_consts.contains(c.name()),
        Term::App(sym, args) => {
            if !allowed_funs.contains(&sym.name) {
                return false;
            }
            args.iter()
                .all(|a| term_uses_only_symbols(a, allowed_consts, allowed_funs))
        }
    }
}

#[test]
fn session_executes_clause_statement() {
    let mut session = Session::new();
    let clause = Clause::new(vec![Literal::pos("p", vec![])]);
    let stmt = Statement::Clause(clause.clone());

    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    assert!(matches!(result, ExecResult::ClauseAdded));
    assert_eq!(session.theory().clauses().len(), 1);
    assert_eq!(session.theory().clauses()[0], clause);
}

#[test]
fn session_executes_formula_statement() {
    let mut session = Session::new();
    let formula = Formula::atom(Atom::prop("p"));
    let stmt = Statement::Formula(formula);

    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
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
    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    assert!(matches!(result, ExecResult::QueryResult(_)));
}

#[test]
fn session_query_dedups_answers_by_execution_time() {
    // User-visible answers must be deduplicated by the time they are returned.
    let mut session = Session::new();
    let fact = Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
    session
        .execute_statement(Statement::Clause(fact.clone()))
        .expect("execute_statement failed");
    session
        .execute_statement(Statement::Clause(fact))
        .expect("execute_statement failed");

    let stmt = Statement::Query(vec![Literal::pos("p", vec![Term::var("X")])]);
    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    let first = match result {
        ExecResult::QueryResult(qr) => qr,
        other => panic!("expected query result, got {:?}", other),
    };
    assert!(matches!(first, crate::sggs::QueryResult::Answer(_)));

    let next = session
        .execute_statement(Statement::Directive(Directive::Next))
        .expect("execute_statement failed");
    let next = match next {
        ExecResult::QueryResult(qr) => qr,
        other => panic!("expected query result, got {:?}", other),
    };
    assert!(
        matches!(next, crate::sggs::QueryResult::Exhausted),
        "duplicate answers must be filtered"
    );
}

#[test]
fn session_dedups_alpha_equivalent_sources_in_answers() {
    // Two alpha-equivalent clauses should not yield duplicate answers.
    let mut session = Session::new();
    session
        .execute_statement(Statement::Clause(Clause::new(vec![Literal::pos(
            "p",
            vec![Term::var("X")],
        )])))
        .expect("execute_statement failed");
    session
        .execute_statement(Statement::Clause(Clause::new(vec![Literal::pos(
            "p",
            vec![Term::var("Y")],
        )])))
        .expect("execute_statement failed");

    let stmt = Statement::Query(vec![Literal::pos("p", vec![Term::constant("a")])]);
    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    let first = match result {
        ExecResult::QueryResult(qr) => qr,
        other => panic!("expected query result, got {:?}", other),
    };
    assert!(matches!(first, crate::sggs::QueryResult::Answer(_)));

    let next = session
        .execute_statement(Statement::Directive(Directive::Next))
        .expect("execute_statement failed");
    let next = match next {
        ExecResult::QueryResult(qr) => qr,
        other => panic!("expected query result, got {:?}", other),
    };
    assert!(
        matches!(next, crate::sggs::QueryResult::Exhausted),
        "alpha-equivalent sources must dedup answers"
    );
}

#[test]
fn session_applies_set_directive() {
    let mut session = Session::new();
    let stmt = Statement::Directive(Directive::Set("max_steps".to_string(), "10".to_string()));
    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
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
    let err = session
        .execute_statement(stmt)
        .expect_err("expected initial_interp to be rejected for end-user API");
    assert!(
        err.message.to_lowercase().contains("initial_interp")
            || err.message.to_lowercase().contains("initial"),
        "error should mention unsupported option"
    );
}

#[test]
fn session_sets_projection_policy() {
    let mut session = Session::new();
    let stmt = Statement::Directive(Directive::Set(
        "projection".to_string(),
        "allow_internal".to_string(),
    ));
    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    assert!(matches!(result, ExecResult::DirectiveApplied(_)));
    assert!(matches!(
        session.projection_policy(),
        crate::sggs::ProjectionPolicy::AllowInternal
    ));
}

#[test]
fn session_default_projection_policy_only_user_symbols() {
    let session = Session::new();
    assert!(matches!(
        session.projection_policy(),
        crate::sggs::ProjectionPolicy::OnlyUserSymbols
    ));
}

#[test]
fn session_execute_query_on_empty_theory() {
    let mut session = Session::new();
    let stmt = Statement::Query(vec![Literal::pos("p", vec![Term::constant("a")])]);
    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    assert!(matches!(result, ExecResult::QueryResult(_)));
}

#[test]
fn session_load_file_error_does_not_mutate_theory() {
    let mut session = Session::new();
    let before = session.theory().clauses().len();
    let err = session
        .load_file("/nonexistent/path.sggs")
        .expect_err("expected error");
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
        DirectiveResult::Loaded {
            path: loaded,
            clauses,
        } => {
            assert!(
                loaded.contains("sggslog_test_"),
                "loaded path should be reported"
            );
            assert_eq!(
                clauses, 2,
                "load_file should report number of clauses added"
            );
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

    let expected = Clause::new(vec![Literal::neg("p", vec![]), Literal::pos("q", vec![])]);
    let expected_set: std::collections::HashSet<_> = expected.literals.into_iter().collect();
    let found = session.theory().clauses().iter().any(|c| {
        let got: std::collections::HashSet<_> = c.literals.iter().cloned().collect();
        got == expected_set
    });
    assert!(found, "expected normalized clause ¬p ∨ q");

    let _ = fs::remove_file(&path);
}

#[test]
fn session_query_does_not_expose_internal_symbols() {
    let mut session = Session::new();
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time")
        .as_nanos();
    let path = std::env::temp_dir().join(format!("sggslog_proj_{}.sggs", unique));
    // Include an existential to allow internal Skolem symbols, but also a user constant "a"
    // so answers can be projected to user-known symbols.
    fs::write(&path, "∃X (p X)\np a\n").expect("write test file");

    let _ = session
        .load_file(path.to_str().expect("path string"))
        .expect("load_file failed");

    let stmt = Statement::Query(vec![Literal::pos("p", vec![Term::var("Y")])]);
    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    let mut answers = Vec::new();
    let mut qr = match result {
        ExecResult::QueryResult(qr) => qr,
        other => panic!("expected query result, got {:?}", other),
    };
    loop {
        match qr {
            crate::sggs::QueryResult::Answer(ans) => answers.push(ans),
            crate::sggs::QueryResult::NoAnswers | crate::sggs::QueryResult::Exhausted => break,
            other => panic!("expected answer or exhaustion, got {:?}", other),
        }
        let next = session
            .execute_statement(Statement::Directive(Directive::Next))
            .expect("execute_statement failed");
        qr = match next {
            ExecResult::QueryResult(qr) => qr,
            other => panic!("expected query result, got {:?}", other),
        };
    }

    // Only symbols from the original input (predicate p and constant a) are allowed.
    let mut allowed_consts = std::collections::HashSet::new();
    allowed_consts.insert("a".to_string());
    // Treat constants as 0-ary functions to accept either encoding.
    let allowed_funs = allowed_consts.clone();

    for s in &answers {
        for v in s.domain() {
            let t = s.lookup(v).expect("bound var");
            assert!(
                term_uses_only_symbols(t, &allowed_consts, &allowed_funs),
                "answer contains non-user symbol: {:?}",
                t
            );
        }
    }
    assert!(
        answers
            .iter()
            .any(|s| { s.lookup(&Var::new("Y")) == Some(&Term::constant("a")) }),
        "expected projected answer with Y=a"
    );
    let _ = fs::remove_file(&path);
}

#[test]
fn session_query_without_projectable_witness_returns_no_answers() {
    let mut session = Session::new();
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time")
        .as_nanos();
    let path = std::env::temp_dir().join(format!("sggslog_noproj_{}.sggs", unique));
    // No user constants; only an existential witness exists.
    fs::write(&path, "∃X (p X)\n").expect("write test file");

    let _ = session
        .load_file(path.to_str().expect("path string"))
        .expect("load_file failed");

    let stmt = Statement::Query(vec![Literal::pos("p", vec![Term::var("Y")])]);
    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    match result {
        ExecResult::QueryResult(crate::sggs::QueryResult::NoAnswers) => {}
        ExecResult::QueryResult(crate::sggs::QueryResult::Answer(ans)) => {
            panic!(
                "expected no answers without projectable witness, got {:?}",
                ans
            );
        }
        other => panic!("expected query result, got {:?}", other),
    }

    let _ = fs::remove_file(&path);
}

#[test]
fn session_query_allows_internal_symbols_when_enabled() {
    let mut session = Session::new();
    let _ = session
        .execute_statement(Statement::Directive(Directive::Set(
            "projection".to_string(),
            "allow_internal".to_string(),
        )))
        .expect("set projection");

    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time")
        .as_nanos();
    let path = std::env::temp_dir().join(format!("sggslog_internal_{}.sggs", unique));
    fs::write(&path, "∃X (p X)\n").expect("write test file");

    let _ = session
        .load_file(path.to_str().expect("path string"))
        .expect("load_file failed");

    let stmt = Statement::Query(vec![Literal::pos("p", vec![Term::var("Y")])]);
    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    let answer = match result {
        ExecResult::QueryResult(crate::sggs::QueryResult::Answer(ans)) => ans,
        other => panic!("expected answer, got {:?}", other),
    };

    // User signature has no constants, so any bound term is internal.
    let sig = session.user_signature();
    let allowed_consts = sig.constants.clone();
    let allowed_funs = sig.functions.clone();
    assert!(
        answer.domain().iter().any(|v| {
            let t = answer.lookup(v).expect("bound var");
            !term_uses_only_symbols(t, &allowed_consts, &allowed_funs)
        }),
        "allow_internal should permit answers with non-user symbols"
    );

    let next = session
        .execute_statement(Statement::Directive(Directive::Next))
        .expect("execute_statement failed");
    let next = match next {
        ExecResult::QueryResult(qr) => qr,
        other => panic!("expected query result, got {:?}", other),
    };
    assert!(matches!(next, crate::sggs::QueryResult::Exhausted));

    let _ = fs::remove_file(&path);
}

#[test]
fn session_tracks_user_signature_from_input() {
    let mut session = Session::new();
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time")
        .as_nanos();
    let path = std::env::temp_dir().join(format!("sggslog_sig_{}.sggs", unique));
    fs::write(&path, "p a\nq (f a)\n∃X (r X)\n").expect("write test file");

    let _ = session
        .load_file(path.to_str().expect("path string"))
        .expect("load_file failed");

    let sig = session.user_signature();
    assert!(sig.predicates.contains("p"));
    assert!(sig.predicates.contains("q"));
    assert!(sig.predicates.contains("r"));
    assert!(sig.functions.contains("f"));
    assert!(sig.constants.contains("a"));

    let _ = fs::remove_file(&path);
}
