use super::*;

// =============================================================================
// QUERY SEMANTICS (GOAL ANSWERING)
// =============================================================================
//
// Queries are interpreted as conjunctions of literals.
// Queries are answered against the SGGS-constructed model (not refutation).

use crate::sggs::{answer_query, Query, QueryResult};
use crate::sggs::{answer_query_projected, ProjectionPolicy};
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
fn query_helpers_ground_and_negation() {
    let ground = Query::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
    assert!(ground.is_ground());
    let nonground = Query::new(vec![Literal::pos("p", vec![Term::var("X")])]);
    assert!(!nonground.is_ground());

    let query = Query::new(vec![
        Literal::pos("p", vec![Term::var("X")]),
        Literal::neg("q", vec![Term::constant("a")]),
    ]);
    let neg = query.negated_as_clause();
    let lits: std::collections::HashSet<_> = neg.literals.iter().cloned().collect();
    let expected: std::collections::HashSet<_> = vec![
        Literal::neg("p", vec![Term::var("X")]),
        Literal::pos("q", vec![Term::constant("a")]),
    ]
    .into_iter()
    .collect();
    assert_eq!(lits, expected);
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
            assert!(
                ans[0].domain().is_empty(),
                "ground answer should be empty substitution"
            );
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
            assert!(ans
                .iter()
                .any(|s| s.lookup(&x) == Some(&Term::constant("a"))));
            assert!(ans
                .iter()
                .any(|s| s.lookup(&x) == Some(&Term::constant("b"))));
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
fn negative_literal_query_true_when_atom_absent() {
    // Empty theory under I⁻ has no true atoms, so ¬p(a) should be true.
    let theory = crate::theory::Theory::new();
    let query = Query::new(vec![Literal::neg("p", vec![Term::constant("a")])]);
    match answer_query(&theory, &query, crate::sggs::DerivationConfig::default()) {
        QueryResult::Answers(ans) => {
            assert_eq!(
                ans.len(),
                1,
                "ground negative query should yield one answer"
            );
            assert!(
                ans[0].domain().is_empty(),
                "ground answer should be empty substitution"
            );
        }
        other => panic!("Expected answers, got {:?}", other),
    }
}

#[test]
fn negative_literal_query_with_shared_variable() {
    // Source: spec.md (queries answered against constructed model; safe variable use).
    // Safe query: variable appears in positive literal; negative filters results.
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
        Literal::neg("q", vec![Term::var("X")]),
    ]);
    match answer_query(&theory, &query, crate::sggs::DerivationConfig::default()) {
        QueryResult::Answers(ans) => {
            let x = Var::new("X");
            assert_eq!(ans.len(), 1, "expected exactly one answer");
            assert_eq!(ans[0].lookup(&x), Some(&Term::constant("b")));
            assert_no_spurious_bindings(&ans, &query.variables());
            assert_no_duplicates(&ans);
        }
        other => panic!("Expected answers, got {:?}", other),
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

#[test]
fn projected_query_filters_internal_symbols() {
    // Source: spec.md (ProjectionPolicy: OnlyUserSymbols).
    let mut theory = crate::theory::Theory::new();
    // Use an internal Skolem-like constant not present in the user signature.
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("$sk0")],
    )]));

    let query = Query::new(vec![Literal::pos("p", vec![Term::var("Y")])]);
    let user_sig = crate::syntax::Signature::empty();

    let result = answer_query_projected(
        &theory,
        &query,
        crate::sggs::DerivationConfig::default(),
        &user_sig,
        ProjectionPolicy::OnlyUserSymbols,
    );
    assert!(
        matches!(result, QueryResult::NoAnswers),
        "internal witnesses must be filtered under OnlyUserSymbols"
    );
}

#[test]
fn projected_query_keeps_user_witnesses_and_drops_internal() {
    // Mixed answers: p(a) should be kept, p($sk0) should be dropped.
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("$sk0")],
    )]));

    let query = Query::new(vec![Literal::pos("p", vec![Term::var("X")])]);
    let mut user_sig = crate::syntax::Signature::empty();
    user_sig.constants.insert("a".to_string());
    user_sig.functions.insert("a".to_string());

    let result = answer_query_projected(
        &theory,
        &query,
        crate::sggs::DerivationConfig::default(),
        &user_sig,
        ProjectionPolicy::OnlyUserSymbols,
    );
    let answers = match result {
        QueryResult::Answers(ans) => ans,
        other => panic!("Expected answers, got {:?}", other),
    };
    let x = Var::new("X");
    assert!(answers.iter().any(|s| s.lookup(&x) == Some(&Term::constant("a"))));
    assert!(answers.iter().all(|s| {
        s.domain().iter().all(|v| {
            let t = s.lookup(v).expect("bound var");
            match t {
                Term::Var(_) => true,
                Term::Const(c) => user_sig.constants.contains(c.name()),
                Term::App(sym, _) => user_sig.functions.contains(&sym.name),
            }
        })
    }));
    assert_no_duplicates(&answers);
}

#[test]
fn projected_query_allows_internal_symbols_when_enabled() {
    // Source: spec.md (ProjectionPolicy: AllowInternal).
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("$sk0")],
    )]));

    let query = Query::new(vec![Literal::pos("p", vec![Term::var("Y")])]);
    let user_sig = crate::syntax::Signature::empty();

    let result = answer_query_projected(
        &theory,
        &query,
        crate::sggs::DerivationConfig::default(),
        &user_sig,
        ProjectionPolicy::AllowInternal,
    );
    let answers = match result {
        QueryResult::Answers(ans) => ans,
        other => panic!("Expected answers, got {:?}", other),
    };
    assert!(
        answers.iter().any(|s| {
            s.domain().iter().any(|v| {
                let t = s.lookup(v).expect("bound var");
                // user_sig is empty, so any non-var symbol is internal
                match t {
                    Term::Var(_) => false,
                    Term::Const(c) => !user_sig.constants.contains(c.name()),
                    Term::App(sym, _) => !user_sig.functions.contains(&sym.name),
                }
            })
        }),
        "internal witnesses should be allowed under AllowInternal"
    );
}
