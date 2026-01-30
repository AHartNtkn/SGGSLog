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
    assert!(
        stmts.len() >= 2,
        "CNF distribution should produce at least the two expected clauses"
    );
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
        Term::App(sym, args) if sym.arity == 0 && args.is_empty() => {
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
fn test_operator_precedence_and_distribution() {
    // ∧ should bind tighter than ∨: p ∨ q ∧ r == p ∨ (q ∧ r)
    let stmts = parse_file("p ∨ q ∧ r").expect("parse_file failed");
    // Expect CNF equivalent to (p ∨ q) ∧ (p ∨ r)
    assert!(stmts.len() >= 2);
    let clauses = stmts
        .into_iter()
        .map(|s| match s {
            Statement::Clause(c) => c,
            _ => panic!("expected clause"),
        })
        .collect::<Vec<_>>();
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
fn test_implication_right_associative() {
    // p -> q -> r should parse as p -> (q -> r)
    let clause = single_clause("p -> q -> r");
    let expected = Clause::new(vec![
        Literal::neg("p", vec![]),
        Literal::neg("q", vec![]),
        Literal::pos("r", vec![]),
    ]);
    assert_eq!(clause, expected);
}

#[test]
fn test_directive_parsing_load_and_set() {
    let stmts = parse_file(":load \"file.sggs\"\n:set max_steps 10")
        .expect("parse_file failed");
    assert_eq!(stmts.len(), 2);
    assert_eq!(
        stmts[0],
        Statement::Directive(sggslog::parser::Directive::Load("file.sggs".to_string()))
    );
    assert_eq!(
        stmts[1],
        Statement::Directive(sggslog::parser::Directive::Set(
            "max_steps".to_string(),
            "10".to_string()
        ))
    );
}

#[test]
fn test_parse_error_includes_position() {
    let err = parse_file("p ∧").expect_err("expected parse error");
    assert!(err.line > 0);
    assert!(err.column > 0);
    assert!(!err.message.is_empty());
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

#[test]
fn test_multiple_exists_skolem_functions_distinct() {
    let clause = single_clause("∀X ∃Y ∃Z (p X Y Z)");
    assert_eq!(clause.literals.len(), 1);
    let lit = &clause.literals[0];
    assert_eq!(lit.atom.args.len(), 3);
    let x = Term::var("X");
    match (&lit.atom.args[1], &lit.atom.args[2]) {
        (Term::App(fy, fy_args), Term::App(fz, fz_args)) => {
            assert_eq!(fy_args.len(), 1);
            assert_eq!(fz_args.len(), 1);
            assert_eq!(fy_args[0], x);
            assert_eq!(fz_args[0], x);
            assert_ne!(fy.name, fz.name, "distinct existentials require distinct Skolem symbols");
        }
        _ => panic!("expected Skolem function applications for Y and Z"),
    }
}

#[test]
fn test_skolem_depends_on_in_scope_universals() {
    // ∀X ∃Y ∀Z ∃W p(X,Y,Z,W) => Y = f(X), W = g(X,Z)
    let clause = single_clause("∀X ∃Y ∀Z ∃W (p X Y Z W)");
    assert_eq!(clause.literals.len(), 1);
    let lit = &clause.literals[0];
    assert_eq!(lit.atom.args.len(), 4);
    let x = Term::var("X");
    let z = Term::var("Z");
    match (&lit.atom.args[1], &lit.atom.args[3]) {
        (Term::App(fy, fy_args), Term::App(fw, fw_args)) => {
            assert_eq!(fy_args.len(), 1);
            assert_eq!(fy_args[0], x);
            assert_eq!(fw_args.len(), 2);
            assert!(fw_args.contains(&x));
            assert!(fw_args.contains(&z));
            assert_ne!(fy.name, fw.name);
        }
        _ => panic!("expected Skolem functions for Y and W"),
    }
}

#[test]
fn test_exists_before_forall_skolem_constant() {
    // ∃X ∀Y p(X,Y) => X = c, Y remains variable
    let clause = single_clause("∃X ∀Y (p X Y)");
    assert_eq!(clause.literals.len(), 1);
    let lit = &clause.literals[0];
    match &lit.atom.args[0] {
        Term::Const(_) => {}
        Term::App(sym, args) if sym.arity == 0 && args.is_empty() => {}
        _ => panic!("expected Skolem constant for X"),
    }
    assert_eq!(lit.atom.args[1], Term::var("Y"));
}

#[test]
fn test_nested_distribution_four_clauses() {
    // (p ∧ q) ∨ (r ∧ s) => 4 clauses: p∨r, p∨s, q∨r, q∨s
    let stmts = parse_file("(p ∧ q) ∨ (r ∧ s)").expect("parse_file failed");
    assert!(
        stmts.len() >= 4,
        "CNF distribution should include the four expected clauses"
    );
    let mut clauses = stmts
        .into_iter()
        .map(|s| match s {
            Statement::Clause(c) => c,
            _ => panic!("expected clause"),
        })
        .collect::<Vec<_>>();
    clauses.sort_by_key(|c| c.literals.len());

    let expected = vec![
        vec![Literal::pos("p", vec![]), Literal::pos("r", vec![])],
        vec![Literal::pos("p", vec![]), Literal::pos("s", vec![])],
        vec![Literal::pos("q", vec![]), Literal::pos("r", vec![])],
        vec![Literal::pos("q", vec![]), Literal::pos("s", vec![])],
    ];
    for want in expected {
        assert!(clauses.iter().any(|c| {
            c.literals == want
                || c.literals == vec![want[1].clone(), want[0].clone()]
        }));
    }
}
