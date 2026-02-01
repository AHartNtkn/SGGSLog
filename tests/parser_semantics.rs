use sggslog::parser::{parse_file, parse_query, Statement};
use sggslog::syntax::{Atom, Formula, Literal, Term, Var};

fn single_formula(src: &str) -> Formula {
    let stmts = parse_file(src).expect("parse_file failed");
    assert_eq!(stmts.len(), 1, "expected one statement");
    match &stmts[0] {
        Statement::Formula(f) => f.clone(),
        other => panic!("expected a formula statement, got {:?}", other),
    }
}

fn atom(name: &str) -> Formula {
    Formula::atom(Atom::prop(name))
}

#[test]
fn test_zero_ary_predicate_parsing() {
    let f1 = single_formula("p");
    let f2 = single_formula("(p)");
    assert_eq!(f1, f2);
    assert_eq!(f1, atom("p"));
}

#[test]
fn test_application_without_parentheses() {
    // Source: spec.md (surface syntax allows predicate application in files/REPL).
    // Surface syntax should allow "p a b" as p(a,b).
    let f = single_formula("p a b");
    let expected = Formula::atom(Atom::new(
        "p",
        vec![Term::constant("a"), Term::constant("b")],
    ));
    assert_eq!(f, expected);
}

#[test]
fn test_negation_sugar_ascii_and_unicode() {
    let f1 = single_formula("~p");
    let f2 = single_formula("¬p");
    let expected = Formula::negation(atom("p"));
    assert_eq!(f1, expected);
    assert_eq!(f2, expected);
}

#[test]
fn test_implication_right_associative() {
    // p -> q -> r should parse as p -> (q -> r)
    let f = single_formula("p -> q -> r");
    let expected = Formula::implies(atom("p"), Formula::implies(atom("q"), atom("r")));
    assert_eq!(f, expected);
}

#[test]
fn test_operator_precedence_and_parentheses() {
    // ∧ should bind tighter than ∨: p ∨ q ∧ r == p ∨ (q ∧ r)
    let f = single_formula("p ∨ q ∧ r");
    let expected = Formula::or(atom("p"), Formula::and(atom("q"), atom("r")));
    assert_eq!(f, expected);
}

#[test]
fn test_operator_precedence_ascii() {
    // & should bind tighter than |: p | q & r == p | (q & r)
    let f = single_formula("p | q & r");
    let expected = Formula::or(atom("p"), Formula::and(atom("q"), atom("r")));
    assert_eq!(f, expected);
}

#[test]
fn test_quantifier_parsing_preserved() {
    let f = single_formula("∀X (p X)");
    let expected = Formula::forall(
        Var::new("X"),
        Formula::atom(Atom::new("p", vec![Term::var("X")])),
    );
    assert_eq!(f, expected);
}

#[test]
fn test_nested_quantifiers_parse_as_nested() {
    // Source: standard FOL quantifier nesting (consistent with spec.md surface syntax).
    let f = single_formula("∀X ∀Y (p X Y)");
    match f {
        Formula::Forall(x, inner) => match *inner {
            Formula::Forall(y, body) => {
                assert_eq!(x.name(), "X");
                assert_eq!(y.name(), "Y");
                match *body {
                    Formula::Atom(atom) => {
                        assert_eq!(atom.predicate, "p");
                        assert_eq!(atom.args, vec![Term::var("X"), Term::var("Y")]);
                    }
                    _ => panic!("expected atom under nested quantifiers"),
                }
            }
            _ => panic!("expected nested forall"),
        },
        _ => panic!("expected outer forall"),
    }
}

#[test]
fn test_quantifier_scoping_allows_shadowing() {
    let f = single_formula("∀X (p X ∧ ∃X (q X))");
    match f {
        Formula::Forall(outer, body) => {
            assert_eq!(outer.name(), "X");
            match *body {
                Formula::And(left, right) => {
                    match *left {
                        Formula::Atom(atom) => {
                            assert_eq!(atom.predicate, "p");
                            assert_eq!(atom.args, vec![Term::var("X")]);
                        }
                        _ => panic!("expected atom on left of ∧"),
                    }
                    match *right {
                        Formula::Exists(inner, inner_body) => {
                            assert_eq!(inner.name(), "X");
                            match *inner_body {
                                Formula::Atom(atom) => {
                                    assert_eq!(atom.predicate, "q");
                                    assert_eq!(atom.args, vec![Term::var("X")]);
                                }
                                _ => panic!("expected atom inside ∃"),
                            }
                        }
                        _ => panic!("expected ∃ on right of ∧"),
                    }
                }
                _ => panic!("expected conjunction"),
            }
        }
        _ => panic!("expected outer ∀"),
    }
}

#[test]
fn test_sorted_identifiers_in_terms() {
    let f = single_formula("∀X:s1 (p (f:s2 X:s1))");
    match f {
        Formula::Forall(v, body) => {
            assert_eq!(v.name(), "X");
            assert_eq!(v.sort(), Some("s1"));
            match *body {
                Formula::Atom(atom) => match &atom.args[0] {
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
                },
                _ => panic!("expected atom"),
            }
        }
        _ => panic!("expected forall formula"),
    }
}

#[test]
fn test_sorted_constants_in_terms() {
    let f = single_formula("p a:s1");
    match f {
        Formula::Atom(atom) => {
            assert_eq!(atom.predicate, "p");
            assert_eq!(atom.args.len(), 1);
            match &atom.args[0] {
                Term::App(sym, args) => {
                    assert_eq!(sym.name, "a");
                    assert_eq!(sym.arity, 0);
                    assert_eq!(sym.result_sort.as_deref(), Some("s1"));
                    assert!(args.is_empty());
                }
                _ => panic!("expected sorted constant as 0-ary application"),
            }
        }
        _ => panic!("expected atom"),
    }
}

#[test]
fn test_query_parsing_with_ascii_and_unicode() {
    let q1 = parse_query("?- (p a) & (q a)").expect("parse_query failed");
    let q2 = parse_query("?- (p a) ∧ (q a)").expect("parse_query failed");
    assert_eq!(q1.literals.len(), 2);
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
    assert!(matches!(stmts[0], Statement::Formula(_)));
    assert!(matches!(stmts[1], Statement::Formula(_)));
}

#[test]
fn test_directive_parsing_load_and_set() {
    let stmts = parse_file(":load \"file.sggs\"\n:set timeout_ms 10").expect("parse_file failed");
    assert_eq!(stmts.len(), 2);
    assert_eq!(
        stmts[0],
        Statement::Directive(sggslog::parser::Directive::Load("file.sggs".to_string()))
    );
    assert_eq!(
        stmts[1],
        Statement::Directive(sggslog::parser::Directive::Set(
            sggslog::parser::Setting::TimeoutMs(10)
        ))
    );
}

#[test]
fn test_directive_parsing_next() {
    let stmts = parse_file(":next").expect("parse_file failed");
    assert_eq!(stmts.len(), 1);
    assert_eq!(
        stmts[0],
        Statement::Directive(sggslog::parser::Directive::Next)
    );
}

#[test]
fn test_directive_parsing_quit() {
    let stmts = parse_file(":quit").expect("parse_file failed");
    assert_eq!(stmts.len(), 1);
    assert_eq!(
        stmts[0],
        Statement::Directive(sggslog::parser::Directive::Quit)
    );
}

#[test]
fn test_directive_parsing_set_projection() {
    let stmts = parse_file(":set projection only_user_symbols\n:set projection allow_internal")
        .expect("parse_file failed");
    assert_eq!(stmts.len(), 2);
    assert_eq!(
        stmts[0],
        Statement::Directive(sggslog::parser::Directive::Set(
            sggslog::parser::Setting::Projection(
                sggslog::parser::ProjectionSetting::OnlyUserSymbols
            )
        ))
    );
    assert_eq!(
        stmts[1],
        Statement::Directive(sggslog::parser::Directive::Set(
            sggslog::parser::Setting::Projection(sggslog::parser::ProjectionSetting::AllowInternal)
        ))
    );
}

#[test]
fn test_parenthesized_function_application() {
    let f = single_formula("p (f a)");
    let expected = Formula::atom(Atom::new(
        "p",
        vec![Term::app("f", vec![Term::constant("a")])],
    ));
    assert_eq!(f, expected);
}

#[test]
fn test_parse_error_includes_position() {
    let err = parse_file("p ∧").expect_err("expected parse error");
    assert!(!err.message.is_empty());
}

#[test]
fn test_directive_parsing_unknown_setting() {
    let stmts = parse_file(":set foo bar").expect("parse_file failed");
    assert_eq!(stmts.len(), 1);
    assert_eq!(
        stmts[0],
        Statement::Directive(sggslog::parser::Directive::Set(
            sggslog::parser::Setting::Unknown {
                key: "foo".to_string(),
                value: "bar".to_string()
            }
        ))
    );
}
