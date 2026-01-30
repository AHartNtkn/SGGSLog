use super::*;

// =============================================================================
// QUERY SEMANTICS (GOAL ANSWERING)
// =============================================================================
//
// Queries are interpreted as conjunctions of literals.
// Queries are answered against the SGGS-constructed model (not refutation).

use crate::sggs::{answer_query, Query, QueryResult};

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
            assert!(
                ans.iter().any(|s| s.domain().is_empty()),
                "ground proof should include empty substitution"
            );
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
            assert!(
                ans.iter()
                    .any(|s| s.lookup(&x) == Some(&Term::constant("a"))),
                "expected an answer binding X to a"
            );
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
            let mut found = 0;
            for s in ans {
                if s.lookup(&x) == Some(&Term::constant("a"))
                    || s.lookup(&x) == Some(&Term::constant("b"))
                {
                    found += 1;
                }
            }
            assert!(found >= 2, "expected answers for a and b");
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
