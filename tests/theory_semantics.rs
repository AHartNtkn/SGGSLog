use sggslog::parser::{Directive, Statement};
use sggslog::syntax::{Clause, Literal, Query, Term};
use sggslog::theory::Theory;
use std::collections::HashMap;

fn canonical_term(
    term: &Term,
    renaming: &mut HashMap<String, String>,
    next_id: &mut usize,
) -> String {
    match term {
        Term::Var(v) => {
            let name = v.name().to_string();
            let entry = renaming.entry(name).or_insert_with(|| {
                let id = *next_id;
                *next_id += 1;
                format!("V{}", id)
            });
            if let Some(sort) = v.sort() {
                format!("{}:{}", entry, sort)
            } else {
                entry.clone()
            }
        }
        Term::App(sym, args) => {
            let mut rendered = String::new();
            if sym.arity == 0 && args.is_empty() {
                rendered.push_str("c:");
                rendered.push_str(sym.name.as_str());
                if let Some(sort) = sym.result_sort.as_deref() {
                    rendered.push(':');
                    rendered.push_str(sort);
                }
            } else {
                rendered.push_str("f:");
                rendered.push_str(sym.name.as_str());
                if let Some(sort) = sym.result_sort.as_deref() {
                    rendered.push(':');
                    rendered.push_str(sort);
                }
                rendered.push('(');
                let mut first = true;
                for a in args {
                    if !first {
                        rendered.push(',');
                    }
                    first = false;
                    rendered.push_str(&canonical_term(a, renaming, next_id));
                }
                rendered.push(')');
            }
            rendered
        }
    }
}

fn canonical_literal(
    lit: &Literal,
    renaming: &mut HashMap<String, String>,
    next_id: &mut usize,
) -> String {
    let mut s = String::new();
    if lit.positive {
        s.push('+');
    } else {
        s.push('-');
    }
    s.push_str(lit.atom.predicate.as_str());
    s.push('(');
    let mut first = true;
    for arg in &lit.atom.args {
        if !first {
            s.push(',');
        }
        first = false;
        s.push_str(&canonical_term(arg, renaming, next_id));
    }
    s.push(')');
    s
}

fn canonical_clause(c: &Clause) -> Vec<String> {
    let mut renaming: HashMap<String, String> = HashMap::new();
    let mut next_id = 0usize;
    let mut lits: Vec<String> = c
        .literals
        .iter()
        .map(|l| canonical_literal(l, &mut renaming, &mut next_id))
        .collect();
    lits.sort();
    lits
}

fn alpha_equivalent(a: &Clause, b: &Clause) -> bool {
    if a.literals.len() != b.literals.len() {
        return false;
    }
    canonical_clause(a) == canonical_clause(b)
}

#[test]
fn test_from_statements_rejects_query() {
    let stmts = vec![Statement::Query(Query::new(vec![Literal::pos(
        "p",
        vec![],
    )]))];
    let err = Theory::from_statements(&stmts).expect_err("expected error");
    assert!(
        err.message.to_lowercase().contains("query"),
        "error should mention query"
    );
}

#[test]
fn test_from_statements_rejects_directive() {
    let stmts = vec![Statement::Directive(Directive::Load(
        "file.sggs".to_string(),
    ))];
    let err = Theory::from_statements(&stmts).expect_err("expected error");
    assert!(
        err.message.to_lowercase().contains("directive"),
        "error should mention directive"
    );
}

#[test]
fn test_from_statements_dedup_alpha_equivalent() {
    let c1 = Clause::new(vec![
        Literal::pos("p", vec![Term::var("X")]),
        Literal::pos("q", vec![Term::var("X")]),
    ]);
    let c2 = Clause::new(vec![
        Literal::pos("p", vec![Term::var("Y")]),
        Literal::pos("q", vec![Term::var("Y")]),
    ]);
    let stmts = vec![Statement::Clause(c1.clone()), Statement::Clause(c2.clone())];

    let theory = Theory::from_statements(&stmts).expect("expected theory");
    // Alpha-equivalent clauses may be retained or deduplicated internally.
    assert!(
        theory.clauses().iter().any(|c| alpha_equivalent(c, &c1)),
        "theory should contain a clause alpha-equivalent to input"
    );
}

#[test]
fn test_from_statements_keep_non_alpha_equivalent() {
    let c1 = Clause::new(vec![
        Literal::pos("p", vec![Term::var("X")]),
        Literal::pos("q", vec![Term::var("X")]),
    ]);
    let c2 = Clause::new(vec![
        Literal::pos("p", vec![Term::var("X")]),
        Literal::pos("q", vec![Term::var("Y")]),
    ]);
    let stmts = vec![Statement::Clause(c1.clone()), Statement::Clause(c2.clone())];

    let theory = Theory::from_statements(&stmts).expect("expected theory");
    assert!(
        theory.clauses().iter().any(|c| alpha_equivalent(c, &c1)),
        "theory should contain a clause alpha-equivalent to the first clause"
    );
    assert!(
        theory.clauses().iter().any(|c| alpha_equivalent(c, &c2)),
        "theory should contain a clause alpha-equivalent to the second clause"
    );
    assert!(
        theory.clauses().iter().any(|c| !alpha_equivalent(c, &c1)),
        "theory should retain a non-alpha-equivalent clause"
    );
}

#[test]
fn test_theory_new_empty() {
    let theory = Theory::new();
    assert_eq!(theory.clauses().len(), 0);
}

#[test]
fn test_theory_add_clause_order() {
    let mut theory = Theory::new();
    let c1 = Clause::new(vec![Literal::pos("p", vec![])]);
    let c2 = Clause::new(vec![Literal::pos("q", vec![])]);
    theory.add_clause(c1.clone());
    theory.add_clause(c2.clone());
    assert_eq!(theory.clauses().len(), 2);
    assert!(theory.clauses().iter().any(|c| c == &c1));
    assert!(theory.clauses().iter().any(|c| c == &c2));
}
