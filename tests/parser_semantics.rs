use sggslog::parser::{parse_file, parse_query};
use sggslog::parser::Statement;
use sggslog::syntax::{Clause, Literal, Term, Var};

fn single_clause(src: &str) -> Clause {
    let stmts = parse_file(src).expect("parse_file failed");
    assert_eq!(stmts.len(), 1, "expected one statement");
    match &stmts[0] {
        Statement::Clause(c) => c.clone(),
        _ => panic!("expected a clause"),
    }
}

#[test]
fn test_zero_ary_predicate_parsing() {
    let clause1 = single_clause("p");
    let clause2 = single_clause("(p)");
    assert_eq!(clause1, clause2);
    assert_eq!(clause1.literals.len(), 1);
    assert_eq!(clause1.literals[0], Literal::pos("p", vec![]));
}

#[test]
fn test_negation_sugar_ascii_and_unicode() {
    let clause1 = single_clause("~p");
    let clause2 = single_clause("¬p");
    assert_eq!(clause1.literals.len(), 1);
    assert_eq!(clause2.literals.len(), 1);
    assert_eq!(clause1.literals[0], Literal::neg("p", vec![]));
    assert_eq!(clause2.literals[0], Literal::neg("p", vec![]));
}

#[test]
fn test_implication_to_clause() {
    // Standard pipeline: eliminate implication and drop universals.
    let clause = single_clause("∀X ((p X) -> (q X))");
    assert_eq!(
        clause,
        Clause::new(vec![
            Literal::neg("p", vec![Term::var("X")]),
            Literal::pos("q", vec![Term::var("X")]),
        ])
    );
}

#[test]
fn test_distribution_to_cnf() {
    // P ∨ (Q ∧ R) => (P ∨ Q) ∧ (P ∨ R)
    let stmts = parse_file("p ∨ (q ∧ r)").expect("parse_file failed");
    assert_eq!(stmts.len(), 2);
    let mut clauses = stmts
        .into_iter()
        .map(|s| match s {
            Statement::Clause(c) => c,
            _ => panic!("expected clause"),
        })
        .collect::<Vec<_>>();
    clauses.sort_by_key(|c| c.literals.len());

    assert!(clauses.iter().any(|c| {
        c.literals == vec![Literal::pos("p", vec![]), Literal::pos("q", vec![])]
            || c.literals == vec![Literal::pos("q", vec![]), Literal::pos("p", vec![])]
    }));
    assert!(clauses.iter().any(|c| {
        c.literals == vec![Literal::pos("p", vec![]), Literal::pos("r", vec![])]
            || c.literals == vec![Literal::pos("r", vec![]), Literal::pos("p", vec![])]
    }));
}

#[test]
fn test_exists_skolemizes_to_constant() {
    let clause = single_clause("∃X (p X)");
    assert_eq!(clause.literals.len(), 1);
    let lit = &clause.literals[0];
    match &lit.atom.args[0] {
        Term::Const(_) => {
            assert!(lit.is_ground());
        }
        _ => panic!("expected Skolem constant"),
    }
}

#[test]
fn test_forall_exists_skolemizes_to_function() {
    let clause = single_clause("∀X ∃Y (p X Y)");
    assert_eq!(clause.literals.len(), 1);
    let lit = &clause.literals[0];
    assert_eq!(lit.atom.args.len(), 2);
    match &lit.atom.args[1] {
        Term::App(sym, args) => {
            assert_eq!(sym.arity, 1);
            assert_eq!(args[0], Term::var("X"));
        }
        _ => panic!("expected Skolem function application"),
    }
}

#[test]
fn test_query_parsing_with_ascii_and_unicode() {
    let q1 = parse_query("?- (p a) & (q a)").expect("parse_query failed");
    let q2 = parse_query("?- (p a) ∧ (q a)").expect("parse_query failed");
    assert_eq!(q1.len(), 2);
    assert_eq!(q1, q2);
}

#[test]
fn test_comment_and_newline_separation() {
    let stmts = parse_file(
        r#"
// comment
p
q
"#,
    )
    .expect("parse_file failed");
    assert_eq!(stmts.len(), 2);
}

#[test]
fn test_sorted_identifiers_in_terms() {
    let clause = single_clause("∀X:s1 (p (f:s2 X:s1))");
    let lit = &clause.literals[0];
    match &lit.atom.args[0] {
        Term::App(sym, args) => {
            assert_eq!(sym.result_sort.as_deref(), Some("s2"));
            assert_eq!(args.len(), 1);
            match &args[0] {
                Term::Var(v) => {
                    assert_eq!(v.name(), "X");
                    assert_eq!(v.sort(), Some("s1"));
                }
                _ => panic!("expected sorted variable"),
            }
        }
        _ => panic!("expected function application"),
    }
}
