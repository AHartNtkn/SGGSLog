use super::*;

// =============================================================================
// QUERY SEMANTICS (GOAL ANSWERING)
// =============================================================================
//
// Queries are interpreted as conjunctions of literals.
// Queries are answered against the SGGS-constructed model (not refutation).

use crate::sggs::{answer_query, answer_query_projected, ProjectionPolicy, Query, QueryResult};
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
    let mut stream = answer_query(&theory, &query, crate::sggs::DerivationConfig::default());
    match stream.next() {
        QueryResult::Answer(ans) => {
            assert!(ans.domain().is_empty(), "ground answer should be empty");
            assert_no_spurious_bindings(&[ans], &query.variables());
        }
        other => panic!("Expected query proved, got {:?}", other),
    }
    match stream.next() {
        QueryResult::Exhausted => {}
        other => panic!("Expected exhausted stream, got {:?}", other),
    }
}

#[test]
fn ground_query_not_entailed_has_no_answers() {
    let theory = crate::theory::Theory::new();
    let query = Query::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
    let mut stream = answer_query(&theory, &query, crate::sggs::DerivationConfig::default());
    match stream.next() {
        QueryResult::Exhausted => {}
        other => panic!("Expected no answers, got {:?}", other),
    }
}

#[test]
fn unsatisfiable_theory_query_exhausted() {
    // Source: spec.md (unsatisfiable theory yields no model for query answering).
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    theory.add_clause(Clause::new(vec![Literal::neg(
        "p",
        vec![Term::constant("a")],
    )]));
    let query = Query::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
    let mut stream = answer_query(&theory, &query, crate::sggs::DerivationConfig::default());
    match stream.next() {
        QueryResult::Exhausted => {}
        other => panic!("Expected exhausted on unsatisfiable theory, got {:?}", other),
    }
}

#[test]
fn unsatisfiable_query_exhausted() {
    let theory = crate::theory::Theory::new();
    let query = Query::new(vec![
        Literal::pos("p", vec![Term::constant("a")]),
        Literal::neg("p", vec![Term::constant("a")]),
    ]);
    let mut stream = answer_query(&theory, &query, crate::sggs::DerivationConfig::default());
    match stream.next() {
        QueryResult::Exhausted => {}
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
    let mut stream = answer_query(&theory, &query, crate::sggs::DerivationConfig::default());
    match stream.next() {
        QueryResult::Answer(ans) => {
            let x = Var::new("X");
            assert_eq!(ans.lookup(&x), Some(&Term::constant("a")));
            assert_no_spurious_bindings(&[ans], &query.variables());
        }
        other => panic!("Expected answers, got {:?}", other),
    }
    match stream.next() {
        QueryResult::Exhausted => {}
        other => panic!("Expected exhausted stream, got {:?}", other),
    }
}

#[test]
fn non_ground_query_derived_answer() {
    // Theory: p(a), ¬p(X) ∨ q(X). Query: q(X) should yield X=a.
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    theory.add_clause(Clause::new(vec![
        Literal::neg("p", vec![Term::var("X")]),
        Literal::pos("q", vec![Term::var("X")]),
    ]));
    let query = Query::new(vec![Literal::pos("q", vec![Term::var("X")])]);
    let mut stream = answer_query(&theory, &query, crate::sggs::DerivationConfig::default());
    match stream.next() {
        QueryResult::Answer(ans) => {
            let x = Var::new("X");
            assert_eq!(ans.lookup(&x), Some(&Term::constant("a")));
            assert_no_spurious_bindings(&[ans], &query.variables());
        }
        other => panic!("Expected derived answer, got {:?}", other),
    }
    match stream.next() {
        QueryResult::Exhausted => {}
        other => panic!("Expected exhausted stream, got {:?}", other),
    }
}

#[test]
fn answer_query_does_not_project_internal_symbols() {
    // answer_query returns unprojected answers (spec.md).
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("$sk0")],
    )]));
    let query = Query::new(vec![Literal::pos("p", vec![Term::var("X")])]);
    let mut stream = answer_query(&theory, &query, crate::sggs::DerivationConfig::default());
    match stream.next() {
        QueryResult::Answer(ans) => {
            let x = Var::new("X");
            assert_eq!(ans.lookup(&x), Some(&Term::constant("$sk0")));
        }
        other => panic!("Expected answer with internal symbol, got {:?}", other),
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
    let mut stream = answer_query(&theory, &query, crate::sggs::DerivationConfig::default());
    let x = Var::new("X");
    let mut got = HashSet::new();
    for _ in 0..2 {
        match stream.next() {
            QueryResult::Answer(ans) => {
                let v = ans.lookup(&x).expect("expected binding for X").clone();
                got.insert(v);
                assert_no_spurious_bindings(&[ans], &query.variables());
            }
            other => panic!("Expected answer, got {:?}", other),
        }
    }
    assert!(got.contains(&Term::constant("a")));
    assert!(got.contains(&Term::constant("b")));
    match stream.next() {
        QueryResult::Exhausted => {}
        other => panic!("Expected exhausted stream, got {:?}", other),
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
    let mut stream = answer_query(&theory, &query, crate::sggs::DerivationConfig::default());
    match stream.next() {
        QueryResult::Answer(ans) => {
            let x = Var::new("X");
            assert_eq!(ans.lookup(&x), Some(&Term::constant("a")));
            assert_no_spurious_bindings(&[ans], &query.variables());
        }
        other => panic!("Expected answers, got {:?}", other),
    }
    match stream.next() {
        QueryResult::Exhausted => {}
        other => panic!("Expected exhausted stream, got {:?}", other),
    }
}

#[test]
fn query_stream_dedups_duplicate_facts() {
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )]));

    let query = Query::new(vec![Literal::pos("p", vec![Term::var("X")])]);
    let mut stream = answer_query(&theory, &query, crate::sggs::DerivationConfig::default());
    match stream.next() {
        QueryResult::Answer(ans) => {
            let x = Var::new("X");
            assert_eq!(ans.lookup(&x), Some(&Term::constant("a")));
        }
        other => panic!("Expected answer, got {:?}", other),
    }
    match stream.next() {
        QueryResult::Exhausted => {}
        other => panic!("Expected exhausted stream, got {:?}", other),
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
    let mut stream = answer_query(&theory, &query, crate::sggs::DerivationConfig::default());
    match stream.next() {
        QueryResult::Exhausted => {}
        other => panic!("Expected no answers, got {:?}", other),
    }
}

#[test]
fn negative_literal_query_true_when_atom_absent() {
    // Empty theory under I⁻ has no true atoms, so ¬p(a) should be true.
    let theory = crate::theory::Theory::new();
    let query = Query::new(vec![Literal::neg("p", vec![Term::constant("a")])]);
    let mut stream = answer_query(&theory, &query, crate::sggs::DerivationConfig::default());
    match stream.next() {
        QueryResult::Answer(ans) => {
            assert!(ans.domain().is_empty(), "ground answer should be empty");
        }
        other => panic!("Expected answers, got {:?}", other),
    }
    match stream.next() {
        QueryResult::Exhausted => {}
        other => panic!("Expected exhausted stream, got {:?}", other),
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
    let mut stream = answer_query(&theory, &query, crate::sggs::DerivationConfig::default());
    match stream.next() {
        QueryResult::Answer(ans) => {
            let x = Var::new("X");
            assert_eq!(ans.lookup(&x), Some(&Term::constant("b")));
            assert_no_spurious_bindings(&[ans], &query.variables());
        }
        other => panic!("Expected answers, got {:?}", other),
    }
    match stream.next() {
        QueryResult::Exhausted => {}
        other => panic!("Expected exhausted stream, got {:?}", other),
    }
}

#[test]
fn negative_only_query_streams_over_user_signature() {
    // Negative-only queries are allowed and stream answers from the user signature.
    // Source: spec.md (Negative-only queries).
    // Quote: "Negative-only queries ... stream answers over the user signature"
    let mut theory = crate::theory::Theory::new();
    // Introduce constant "a" via an unrelated fact.
    theory.add_clause(Clause::new(vec![Literal::pos(
        "q",
        vec![Term::constant("a")],
    )]));

    let query = Query::new(vec![Literal::neg("p", vec![Term::var("X")])]);
    let mut user_sig = crate::syntax::UserSignature::empty();
    user_sig.insert_function("a", 0, None);

    let mut stream = answer_query_projected(
        &theory,
        &query,
        crate::sggs::DerivationConfig::default(),
        &user_sig,
        ProjectionPolicy::OnlyUserSymbols,
    );
    match stream.next() {
        QueryResult::Answer(ans) => {
            let x = Var::new("X");
            assert_eq!(ans.lookup(&x), Some(&Term::constant("a")));
        }
        other => panic!("Expected answer for negative-only query, got {:?}", other),
    }
}

#[test]
fn query_respects_resource_limit() {
    let theory = crate::theory::Theory::new();
    let query = Query::new(vec![Literal::pos("p", vec![Term::var("X")])]);
    let config = crate::sggs::DerivationConfig {
        timeout_ms: Some(0),
        initial_interp: crate::sggs::InitialInterpretation::AllNegative,
    };
    let mut stream = answer_query(&theory, &query, config);
    match stream.next() {
        QueryResult::Timeout => {}
        other => panic!("Expected timeout, got {:?}", other),
    }
}

#[test]
fn projected_query_allows_user_functions() {
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::app("f", vec![Term::constant("a")])],
    )]));

    let query = Query::new(vec![Literal::pos("p", vec![Term::var("X")])]);
    let mut user_sig = crate::syntax::UserSignature::empty();
    user_sig.insert_function("a", 0, None);
    user_sig.insert_function("f", 1, None);

    let mut stream = answer_query_projected(
        &theory,
        &query,
        crate::sggs::DerivationConfig::default(),
        &user_sig,
        ProjectionPolicy::OnlyUserSymbols,
    );
    let ans = match stream.next() {
        QueryResult::Answer(ans) => ans,
        other => panic!("Expected answers, got {:?}", other),
    };
    let x = Var::new("X");
    assert_eq!(
        ans.lookup(&x),
        Some(&Term::app("f", vec![Term::constant("a")]))
    );
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
    let user_sig = crate::syntax::UserSignature::empty();

    let mut stream = answer_query_projected(
        &theory,
        &query,
        crate::sggs::DerivationConfig::default(),
        &user_sig,
        ProjectionPolicy::OnlyUserSymbols,
    );
    assert!(matches!(stream.next(), QueryResult::Exhausted));
}

#[test]
fn projected_query_filters_internal_functions() {
    // Internal function symbols should be filtered under OnlyUserSymbols.
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::app("f", vec![Term::constant("a")])],
    )]));

    let query = Query::new(vec![Literal::pos("p", vec![Term::var("Y")])]);
    let mut user_sig = crate::syntax::UserSignature::empty();
    user_sig.insert_function("a", 0, None);

    let mut stream = answer_query_projected(
        &theory,
        &query,
        crate::sggs::DerivationConfig::default(),
        &user_sig,
        ProjectionPolicy::OnlyUserSymbols,
    );
    assert!(matches!(stream.next(), QueryResult::Exhausted));
}

#[test]
fn projected_query_filters_internal_symbols_nested_in_user_terms() {
    // Internal symbols inside user terms should be filtered under OnlyUserSymbols.
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::app("f", vec![Term::constant("$sk0")])],
    )]));

    let query = Query::new(vec![Literal::pos("p", vec![Term::var("Y")])]);
    let mut user_sig = crate::syntax::UserSignature::empty();
    user_sig.insert_function("f", 1, None);

    let mut stream = answer_query_projected(
        &theory,
        &query,
        crate::sggs::DerivationConfig::default(),
        &user_sig,
        ProjectionPolicy::OnlyUserSymbols,
    );
    assert!(matches!(stream.next(), QueryResult::Exhausted));
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
    let mut user_sig = crate::syntax::UserSignature::empty();
    user_sig.insert_function("a", 0, None);

    let mut stream = answer_query_projected(
        &theory,
        &query,
        crate::sggs::DerivationConfig::default(),
        &user_sig,
        ProjectionPolicy::OnlyUserSymbols,
    );
    let ans = match stream.next() {
        QueryResult::Answer(ans) => ans,
        other => panic!("Expected answers, got {:?}", other),
    };
    let x = Var::new("X");
    assert_eq!(ans.lookup(&x), Some(&Term::constant("a")));
    assert_no_duplicates(&[ans.clone()]);
    assert!(ans.domain().iter().all(|v| {
        let t = ans.lookup(v).expect("bound var");
        match t {
            Term::Var(_) => true,
            Term::App(sym, _) => user_sig.contains_function(&sym.name, sym.arity),
        }
    }));
    match stream.next() {
        QueryResult::Exhausted => {}
        other => panic!("Expected exhausted stream, got {:?}", other),
    }
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
    let user_sig = crate::syntax::UserSignature::empty();

    let mut stream = answer_query_projected(
        &theory,
        &query,
        crate::sggs::DerivationConfig::default(),
        &user_sig,
        ProjectionPolicy::AllowInternal,
    );
    let ans = match stream.next() {
        QueryResult::Answer(ans) => ans,
        other => panic!("Expected answers, got {:?}", other),
    };
    assert!(ans.domain().iter().any(|v| {
        let t = ans.lookup(v).expect("bound var");
        match t {
            Term::Var(_) => false,
            Term::App(sym, _) => !user_sig.contains_function(&sym.name, sym.arity),
        }
    }));
    match stream.next() {
        QueryResult::Exhausted => {}
        other => panic!("Expected exhausted stream, got {:?}", other),
    }
}

#[test]
fn projected_query_allows_internal_functions_when_enabled() {
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "p",
        vec![Term::app("$skf", vec![Term::constant("a")])],
    )]));

    let query = Query::new(vec![Literal::pos("p", vec![Term::var("Y")])]);
    let mut user_sig = crate::syntax::UserSignature::empty();
    user_sig.insert_function("a", 0, None);

    let mut stream = answer_query_projected(
        &theory,
        &query,
        crate::sggs::DerivationConfig::default(),
        &user_sig,
        ProjectionPolicy::AllowInternal,
    );
    let ans = match stream.next() {
        QueryResult::Answer(ans) => ans,
        other => panic!("Expected answer, got {:?}", other),
    };
    let x = Var::new("Y");
    assert_eq!(
        ans.lookup(&x),
        Some(&Term::app("$skf", vec![Term::constant("a")]))
    );
    match stream.next() {
        QueryResult::Exhausted => {}
        other => panic!("Expected exhausted stream, got {:?}", other),
    }
}
