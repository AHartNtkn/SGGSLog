use super::*;

// =============================================================================
// QUERY SEMANTICS (GOAL ANSWERING)
// =============================================================================
//
// Queries are interpreted as conjunctions of literals.
// Queries are answered against the SGGS-constructed model (not refutation).

use crate::sggs::{answer_query, Query, QueryResult};
use crate::unify::Substitution;
use std::collections::HashSet;

fn subst_key(s: &Substitution) -> String {
    let mut entries: Vec<String> = s
        .domain()
        .into_iter()
        .filter_map(|v| s.lookup(v).map(|t| format!("{}={:?}", v.name(), t)))
        .collect();
    entries.sort();
    entries.join(",")
}

fn assert_no_spurious_bindings(ans: &[Substitution], query_vars: &HashSet<Var>) {
    for s in ans {
        for v in s.domain() {
            assert!(
                query_vars.contains(v),
                "answers must not bind variables not in the query"
            );
        }
    }
}

fn assert_no_duplicates(ans: &[Substitution]) {
    let keys: HashSet<String> = ans.iter().map(subst_key).collect();
    assert_eq!(keys.len(), ans.len(), "answers must be duplicate-free");
}

#[test]
fn ground_query_proved_when_entailed() {
    // Theory: p(a). Query: p(a). Should be true in the constructed model.
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    let query = Query::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
    match answer_query(&theory, &query, crate::sggs::DerivationConfig::default()) {
        QueryResult::Answers(ans) => {
            assert_eq!(ans.len(), 1, "ground query should yield exactly one answer");
            assert!(ans[0].domain().is_empty(), "ground answer should be empty substitution");
            assert_no_spurious_bindings(&ans, &query.variables());
            assert_no_duplicates(&ans);
        }
        other => panic!("Expected query proved, got {:?}", other),
    }
}

#[test]
fn ground_query_not_entailed_has_no_answers() {
    let theory = crate::theory::Theory::new();
    let query = Query::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
    match answer_query(&theory, &query, crate::sggs::DerivationConfig::default()) {
        QueryResult::NoAnswers => {}
        other => panic!("Expected no answers, got {:?}", other),
    }
}

#[test]
fn non_ground_query_returns_instance_answer() {
    // Theory: p(a). Query: p(X). Expect answer X=a in the constructed model.
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    let query = Query::new(vec![Literal::pos("p", vec![Term::var("X")])]);
    match answer_query(&theory, &query, crate::sggs::DerivationConfig::default()) {
        QueryResult::Answers(ans) => {
            let x = Var::new("X");
            assert_eq!(ans.len(), 1, "expected exactly one answer");
            assert_eq!(
                ans[0].lookup(&x),
                Some(&Term::constant("a")),
                "expected an answer binding X to a"
            );
            assert_no_spurious_bindings(&ans, &query.variables());
            assert_no_duplicates(&ans);
        }
        other => panic!("Expected answers, got {:?}", other),
    }
}

#[test]
fn conjunctive_query_multiple_answers() {
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("b")],
    )]));
    let query = Query::new(vec![Literal::pos("p", vec![Term::var("X")])]);
    match answer_query(&theory, &query, crate::sggs::DerivationConfig::default()) {
        QueryResult::Answers(ans) => {
            let x = Var::new("X");
            assert_eq!(ans.len(), 2, "expected exactly two answers");
            assert!(ans.iter().any(|s| s.lookup(&x) == Some(&Term::constant("a"))));
            assert!(ans.iter().any(|s| s.lookup(&x) == Some(&Term::constant("b"))));
            assert_no_spurious_bindings(&ans, &query.variables());
            assert_no_duplicates(&ans);
        }
        other => panic!("Expected answers, got {:?}", other),
    }
}

#[test]
fn conjunctive_query_joins_answers() {
    // Theory: p(a), p(b), q(a). Query: p(X) ∧ q(X) should yield X=a only.
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("b")],
    )]));
    theory.add_clause(Clause::new(vec![Literal::pos(
        "q",
        vec![Term::constant("a")],
    )]));

    let query = Query::new(vec![
        Literal::pos("p", vec![Term::var("X")]),
        Literal::pos("q", vec![Term::var("X")]),
    ]);
    match answer_query(&theory, &query, crate::sggs::DerivationConfig::default()) {
        QueryResult::Answers(ans) => {
            let x = Var::new("X");
            assert_eq!(ans.len(), 1, "expected exactly one joined answer");
            assert_eq!(ans[0].lookup(&x), Some(&Term::constant("a")));
            assert_no_spurious_bindings(&ans, &query.variables());
            assert_no_duplicates(&ans);
        }
        other => panic!("Expected answers, got {:?}", other),
    }
}

#[test]
fn negative_literal_query_no_answers() {
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    let query = Query::new(vec![Literal::neg("p", vec![Term::constant("a")])]);
    match answer_query(&theory, &query, crate::sggs::DerivationConfig::default()) {
        QueryResult::NoAnswers => {}
        other => panic!("Expected no answers, got {:?}", other),
    }
}

#[test]
fn query_respects_resource_limit() {
    let theory = crate::theory::Theory::new();
    let query = Query::new(vec![Literal::pos("p", vec![Term::var("X")])]);
    let config = crate::sggs::DerivationConfig {
        max_steps: Some(0),
        initial_interp: crate::sggs::InitialInterpretation::AllNegative,
    };
    match answer_query(&theory, &query, config) {
        QueryResult::ResourceLimit => {}
        other => panic!("Expected resource limit, got {:?}", other),
    }
}
