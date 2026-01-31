use super::*;

// =============================================================================
// SESSION / END-TO-END API SEMANTICS
// =============================================================================

use crate::parser::{Directive, Statement};
use crate::session::DirectiveResult;
use crate::sggs::{answer_query, Query};
use crate::session::{ExecResult, Session};
use crate::syntax::{Atom, Formula};
use std::fs;
use std::time::{SystemTime, UNIX_EPOCH};

fn term_uses_only_symbols(term: &Term, allowed: &crate::syntax::Signature) -> bool {
    match term {
        Term::Var(_) => true,
        Term::App(sym, args) => {
            if !allowed.contains_function(&sym.name, sym.arity) {
                return false;
            }
            args.iter()
                .all(|a| term_uses_only_symbols(a, allowed))
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
    let stmt = Statement::Query(Query::new(vec![Literal::pos("p", vec![])]));
    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    assert!(matches!(result, ExecResult::QueryResult(_)));
}

#[test]
fn session_query_matches_sggs_query_semantics() {
    let mut session = Session::new();
    session
        .execute_statement(Statement::Clause(Clause::new(vec![
            Literal::pos("p", vec![Term::constant("a")]),
        ])))
        .expect("execute_statement failed");

    let stmt = Statement::Query(Query::new(vec![Literal::pos(
        "p",
        vec![Term::var("X")],
    )]));
    let session_res = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    let session_ans = match session_res {
        ExecResult::QueryResult(crate::sggs::QueryResult::Answer(ans)) => ans,
        other => panic!("expected answer from session, got {:?}", other),
    };

    let query = Query::new(vec![Literal::pos("p", vec![Term::var("X")])]);
    let mut stream =
        answer_query(session.theory(), &query, crate::sggs::DerivationConfig::default());
    let sggs_ans = match stream.next() {
        crate::sggs::QueryResult::Answer(ans) => ans,
        other => panic!("expected answer from answer_query, got {:?}", other),
    };
    assert_eq!(session_ans, sggs_ans);
}

#[test]
fn session_next_without_active_query_errors() {
    let mut session = Session::new();
    let err = session
        .execute_statement(Statement::Directive(Directive::Next))
        .expect_err("expected error when no active query");
    assert!(!err.message.is_empty());
}

#[test]
fn session_new_query_resets_stream() {
    let mut session = Session::new();
    let fact = Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
    session
        .execute_statement(Statement::Clause(fact))
        .expect("execute_statement failed");

    let stmt = Statement::Query(Query::new(vec![Literal::pos(
        "p",
        vec![Term::var("X")],
    )]));
    let first = session
        .execute_statement(stmt.clone())
        .expect("execute_statement failed");
    assert!(matches!(first, ExecResult::QueryResult(crate::sggs::QueryResult::Answer(_))));

    let second = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    assert!(matches!(second, ExecResult::QueryResult(crate::sggs::QueryResult::Answer(_))));
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

    let stmt = Statement::Query(Query::new(vec![Literal::pos(
        "p",
        vec![Term::var("X")],
    )]));
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

    let stmt = Statement::Query(Query::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
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
    let stmt = Statement::Directive(Directive::Set(
        crate::parser::Setting::TimeoutMs(10),
    ));
    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    assert!(matches!(result, ExecResult::DirectiveApplied(_)));
    assert_eq!(session.config().timeout_ms, Some(10));
}

#[test]
fn session_sets_initial_interpretation() {
    let mut session = Session::new();
    let stmt = Statement::Directive(Directive::Set(
        crate::parser::Setting::Unknown {
            key: "initial_interp".to_string(),
            value: "positive".to_string(),
        },
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
        crate::parser::Setting::Projection(crate::parser::ProjectionSetting::AllowInternal),
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
    let stmt = Statement::Query(Query::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
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

    // Normalization should introduce clauses over the original vocabulary (p, q),
    // possibly with auxiliaries, but it must not drop both predicates.
    let sig = session.theory().signature();
    assert!(sig.contains_predicate_name("p"));
    assert!(sig.contains_predicate_name("q"));
    assert!(
        !session.theory().clauses().is_empty(),
        "normalization should produce at least one clause"
    );

    let _ = fs::remove_file(&path);
}

#[test]
fn session_load_file_rejects_queries_and_directives() {
    let mut session = Session::new();
    let before = session.theory().clauses().len();
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time")
        .as_nanos();
    let path = std::env::temp_dir().join(format!("sggslog_bad_{}.sggs", unique));
    fs::write(&path, "p\n?- q\n").expect("write test file");

    let err = session
        .load_file(path.to_str().expect("path string"))
        .expect_err("expected error for query in file");
    assert!(!err.message.is_empty());
    let after = session.theory().clauses().len();
    assert_eq!(before, after, "theory should not change on invalid file");

    let path2 = std::env::temp_dir().join(format!("sggslog_bad_dir_{}.sggs", unique));
    fs::write(&path2, ":set timeout_ms 1\n").expect("write test file");
    let err2 = session
        .load_file(path2.to_str().expect("path string"))
        .expect_err("expected error for directive in file");
    assert!(!err2.message.is_empty());
    let after2 = session.theory().clauses().len();
    assert_eq!(before, after2, "theory should remain unchanged");

    let _ = fs::remove_file(&path);
    let _ = fs::remove_file(&path2);
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

    let stmt = Statement::Query(Query::new(vec![Literal::pos(
        "p",
        vec![Term::var("Y")],
    )]));
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
            crate::sggs::QueryResult::Exhausted => break,
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

    // Only symbols from the original input (predicate p and 0-ary function a) are allowed.
    let mut allowed_sig = crate::syntax::Signature::empty();
    allowed_sig.functions.insert(crate::syntax::FnSig {
        name: "a".to_string(),
        arity: 0,
        result_sort: None,
    });

    for s in &answers {
        for v in s.domain() {
            let t = s.lookup(v).expect("bound var");
            assert!(
                term_uses_only_symbols(t, &allowed_sig),
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

    let stmt = Statement::Query(Query::new(vec![Literal::pos(
        "p",
        vec![Term::var("Y")],
    )]));
    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    match result {
        ExecResult::QueryResult(crate::sggs::QueryResult::Exhausted) => {}
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
            crate::parser::Setting::Projection(crate::parser::ProjectionSetting::AllowInternal),
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

    let stmt = Statement::Query(Query::new(vec![Literal::pos(
        "p",
        vec![Term::var("Y")],
    )]));
    let result = session
        .execute_statement(stmt)
        .expect("execute_statement failed");
    let answer = match result {
        ExecResult::QueryResult(crate::sggs::QueryResult::Answer(ans)) => ans,
        other => panic!("expected answer, got {:?}", other),
    };

    // User signature has no constants, so any bound term is internal.
    let sig = session.user_signature();
    assert!(
        answer.domain().iter().any(|v| {
            let t = answer.lookup(v).expect("bound var");
            !term_uses_only_symbols(t, sig.signature())
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
fn session_user_signature_excludes_internal_skolems() {
    // User signature should include only user-provided symbols, not Skolem symbols.
    let mut session = Session::new();
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time")
        .as_nanos();
    let path = std::env::temp_dir().join(format!("sggslog_skolem_sig_{}.sggs", unique));
    fs::write(&path, "∃X (p X)\n").expect("write test file");

    let _ = session
        .load_file(path.to_str().expect("path string"))
        .expect("load_file failed");

    let sig = session.user_signature().signature();
    assert!(sig.contains_predicate_name("p"));
    assert!(
        sig.functions.is_empty(),
        "user signature should not include internal Skolem functions"
    );

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
    assert!(sig.contains_predicate_name("p"));
    assert!(sig.contains_predicate_name("q"));
    assert!(sig.contains_predicate_name("r"));
    assert!(sig.contains_function_name("f"));
    assert!(sig.contains_function("a", 0));

    let _ = fs::remove_file(&path);
}
