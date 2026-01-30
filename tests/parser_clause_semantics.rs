use sggslog::parser::{parse_file, Statement};
use sggslog::syntax::{Clause, Literal};

#[test]
fn test_clause_keyword_parses_to_clause_statement_ascii() {
    // Explicit clause syntax: "clause" introduces a clausal statement.
    let stmts = parse_file("clause p | ~q").expect("parse_file failed");
    assert_eq!(stmts.len(), 1);
    match &stmts[0] {
        Statement::Clause(c) => {
            let expected = Clause::new(vec![Literal::pos("p", vec![]), Literal::neg("q", vec![])]);
            assert_eq!(c.literals.len(), expected.literals.len());
            for lit in &expected.literals {
                assert!(c.literals.contains(lit));
            }
        }
        other => panic!("expected clause statement, got {:?}", other),
    }
}

#[test]
fn test_clause_keyword_parses_to_clause_statement_unicode() {
    let stmts = parse_file("clause p ∨ ¬q").expect("parse_file failed");
    assert_eq!(stmts.len(), 1);
    match &stmts[0] {
        Statement::Clause(c) => {
            let expected = Clause::new(vec![Literal::pos("p", vec![]), Literal::neg("q", vec![])]);
            assert_eq!(c.literals.len(), expected.literals.len());
            for lit in &expected.literals {
                assert!(c.literals.contains(lit));
            }
        }
        other => panic!("expected clause statement, got {:?}", other),
    }
}
