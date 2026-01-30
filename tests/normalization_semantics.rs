use sggslog::normalize::{clausify_formula, clausify_statements};
use sggslog::parser::{parse_file, Statement};
use sggslog::syntax::{Clause, Formula, Literal, Term};
use std::collections::HashMap;

fn single_formula(src: &str) -> sggslog::syntax::Formula {
    let stmts = parse_file(src).expect("parse_file failed");
    assert_eq!(stmts.len(), 1, "expected one statement");
    match &stmts[0] {
        Statement::Formula(f) => f.clone(),
        other => panic!("expected a formula statement, got {:?}", other),
    }
}

fn clausify_single(src: &str) -> Clause {
    let formula = single_formula(src);
    let clauses = clausify_formula(&formula).expect("clausify_formula failed");
    assert_eq!(clauses.len(), 1, "expected one clause");
    clauses[0].clone()
}

fn clausify_src(src: &str) -> Vec<Clause> {
    let stmts = parse_file(src).expect("parse_file failed");
    clausify_statements(&stmts).expect("clausify_statements failed")
}

fn eval_literal(lit: &Literal, env: &HashMap<String, bool>) -> bool {
    if !lit.atom.args.is_empty() {
        panic!("propositional evaluator only supports zero-ary predicates");
    }
    let val = *env
        .get(lit.atom.predicate.as_str())
        .expect("missing variable assignment");
    if lit.positive {
        val
    } else {
        !val
    }
}

fn eval_clause(clause: &Clause, env: &HashMap<String, bool>) -> bool {
    clause.literals.iter().any(|l| eval_literal(l, env))
}

fn eval_cnf(clauses: &[Clause], env: &HashMap<String, bool>) -> bool {
    clauses.iter().all(|c| eval_clause(c, env))
}

fn eval_formula(formula: &Formula, env: &HashMap<String, bool>) -> bool {
    match formula {
        Formula::Atom(atom) => {
            if !atom.args.is_empty() {
                panic!("propositional evaluator only supports zero-ary predicates");
            }
            *env.get(atom.predicate.as_str())
                .expect("missing variable assignment")
        }
        Formula::Not(inner) => !eval_formula(inner, env),
        Formula::And(left, right) => eval_formula(left, env) && eval_formula(right, env),
        Formula::Or(left, right) => eval_formula(left, env) || eval_formula(right, env),
        Formula::Implies(left, right) => !eval_formula(left, env) || eval_formula(right, env),
        Formula::Forall(_, _) | Formula::Exists(_, _) => {
            panic!("propositional evaluator does not support quantifiers");
        }
    }
}

fn collect_formula_preds(formula: &Formula, acc: &mut std::collections::HashSet<String>) {
    match formula {
        Formula::Atom(atom) => {
            if !atom.args.is_empty() {
                panic!("propositional collector only supports zero-ary predicates");
            }
            acc.insert(atom.predicate.clone());
        }
        Formula::Not(inner) => collect_formula_preds(inner, acc),
        Formula::And(left, right) | Formula::Or(left, right) | Formula::Implies(left, right) => {
            collect_formula_preds(left, acc);
            collect_formula_preds(right, acc);
        }
        Formula::Forall(_, body) | Formula::Exists(_, body) => {
            collect_formula_preds(body, acc);
        }
    }
}

fn collect_cnf_preds(clauses: &[Clause]) -> std::collections::HashSet<String> {
    let mut preds = std::collections::HashSet::new();
    for c in clauses {
        for l in &c.literals {
            if !l.atom.args.is_empty() {
                panic!("propositional collector only supports zero-ary predicates");
            }
            preds.insert(l.atom.predicate.clone());
        }
    }
    preds
}

fn assert_conservative_extension(src: &str) {
    let formula = single_formula(src);
    let clauses = clausify_formula(&formula).expect("clausify_formula failed");

    let mut orig_preds = std::collections::HashSet::new();
    collect_formula_preds(&formula, &mut orig_preds);
    let cnf_preds = collect_cnf_preds(&clauses);
    let new_preds: Vec<String> = cnf_preds.difference(&orig_preds).cloned().collect();

    let orig_vars: Vec<String> = orig_preds.into_iter().collect();
    let new_vars: Vec<String> = new_preds;

    for env_orig in all_assignments(&orig_vars.iter().map(|s| s.as_str()).collect::<Vec<_>>()) {
        let original = eval_formula(&formula, &env_orig);
        let mut exists_ext = false;
        for env_new in all_assignments(&new_vars.iter().map(|s| s.as_str()).collect::<Vec<_>>()) {
            let mut env_full = env_orig.clone();
            for (k, v) in env_new {
                env_full.insert(k, v);
            }
            if eval_cnf(&clauses, &env_full) {
                exists_ext = true;
                break;
            }
        }
        assert_eq!(
            original, exists_ext,
            "CNF must be a conservative extension over the original symbols"
        );
    }
}

fn all_assignments(vars: &[&str]) -> Vec<HashMap<String, bool>> {
    let mut envs = Vec::new();
    let n = vars.len();
    for mask in 0..(1 << n) {
        let mut env = HashMap::new();
        for (i, name) in vars.iter().enumerate() {
            env.insert((*name).to_string(), (mask & (1 << i)) != 0);
        }
        envs.push(env);
    }
    envs
}

#[test]
fn test_implication_to_clause() {
    // Standard pipeline: eliminate implication and drop universals.
    let clause = clausify_single("∀X ((p X) -> (q X))");
    assert_eq!(clause.literals.len(), 2);
    let mut var_term: Option<Term> = None;
    for lit in &clause.literals {
        match (
            lit.positive,
            lit.atom.predicate.as_str(),
            lit.atom.args.as_slice(),
        ) {
            (false, "p", [t]) | (true, "q", [t]) => {
                if let Some(prev) = &var_term {
                    assert_eq!(prev, t, "same variable should be shared across literals");
                } else {
                    var_term = Some(t.clone());
                }
            }
            _ => panic!("expected literals p(X) and q(X) with shared variable"),
        }
    }
}

#[test]
fn test_distribution_to_cnf() {
    // P ∨ (Q ∧ R) should be a conservative extension of the original vocabulary.
    assert_conservative_extension("p ∨ (q ∧ r)");
}

#[test]
fn test_operator_precedence_and_distribution() {
    // ∧ should bind tighter than ∨: p ∨ q ∧ r == p ∨ (q ∧ r)
    assert_conservative_extension("p ∨ q ∧ r");
}

#[test]
fn test_conjunction_produces_multiple_clauses() {
    // p ∧ q should produce two separate clauses.
    let clauses = clausify_src("p ∧ q");
    assert_eq!(clauses.len(), 2);
}

#[test]
fn test_demorgan_conservative_extension() {
    // ¬(p ∨ q) should be a conservative extension over the original vocabulary.
    assert_conservative_extension("¬(p ∨ q)");
}

#[test]
fn test_double_negation_conservative_extension() {
    // ¬¬p should be equivalent to p.
    assert_conservative_extension("¬¬p");
}

#[test]
fn test_nested_distribution_four_clauses() {
    // (p ∧ q) ∨ (r ∧ s) should be a conservative extension of the original vocabulary.
    assert_conservative_extension("(p ∧ q) ∨ (r ∧ s)");
}

#[test]
fn test_exists_skolemizes_to_constant() {
    let clause = clausify_single("∃X (p X)");
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
fn test_exists_skolem_constant_preserves_sort() {
    let clause = clausify_single("∃X:s1 (p X)");
    let lit = &clause.literals[0];
    match &lit.atom.args[0] {
        Term::Const(c) => {
            assert_eq!(c.sort(), Some("s1"));
        }
        Term::App(sym, args) if sym.arity == 0 && args.is_empty() => {
            assert_eq!(sym.result_sort.as_deref(), Some("s1"));
        }
        _ => panic!("expected sorted Skolem constant"),
    }
}

#[test]
fn test_forall_exists_skolemizes_to_function() {
    let clause = clausify_single("∀X ∃Y (p X Y)");
    assert_eq!(clause.literals.len(), 1);
    let lit = &clause.literals[0];
    assert_eq!(lit.atom.args.len(), 2);
    let x = lit.atom.args[0].clone();
    match &lit.atom.args[1] {
        Term::App(sym, args) => {
            assert_eq!(sym.arity, 1);
            assert_eq!(args[0], x);
        }
        _ => panic!("expected Skolem function application"),
    }
}

#[test]
fn test_forall_exists_skolem_function_preserves_sort() {
    let clause = clausify_single("∀X:s1 ∃Y:s2 (p X Y)");
    let lit = &clause.literals[0];
    match &lit.atom.args[1] {
        Term::App(sym, args) => {
            assert_eq!(sym.result_sort.as_deref(), Some("s2"));
            assert_eq!(args.len(), 1);
            match &args[0] {
                Term::Var(v) => assert_eq!(v.sort(), Some("s1")),
                _ => panic!("expected sorted argument"),
            }
        }
        _ => panic!("expected Skolem function application"),
    }
}

#[test]
fn test_multiple_exists_skolem_functions_distinct() {
    let clause = clausify_single("∀X ∃Y ∃Z (p X Y Z)");
    assert_eq!(clause.literals.len(), 1);
    let lit = &clause.literals[0];
    assert_eq!(lit.atom.args.len(), 3);
    let x = lit.atom.args[0].clone();
    match (&lit.atom.args[1], &lit.atom.args[2]) {
        (Term::App(fy, fy_args), Term::App(fz, fz_args)) => {
            assert_eq!(fy_args.len(), 1);
            assert_eq!(fz_args.len(), 1);
            assert_eq!(fy_args[0], x);
            assert_eq!(fz_args[0], x);
            assert_ne!(
                fy.name, fz.name,
                "distinct existentials require distinct Skolem symbols"
            );
        }
        _ => panic!("expected Skolem function applications for Y and Z"),
    }
}

#[test]
fn test_skolem_depends_on_in_scope_universals() {
    // ∀X ∃Y ∀Z ∃W p(X,Y,Z,W) => Y = f(X), W = g(X,Z)
    let clause = clausify_single("∀X ∃Y ∀Z ∃W (p X Y Z W)");
    assert_eq!(clause.literals.len(), 1);
    let lit = &clause.literals[0];
    assert_eq!(lit.atom.args.len(), 4);
    let x = lit.atom.args[0].clone();
    let z = lit.atom.args[2].clone();
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
    let clause = clausify_single("∃X ∀Y (p X Y)");
    assert_eq!(clause.literals.len(), 1);
    let lit = &clause.literals[0];
    match &lit.atom.args[0] {
        Term::Const(_) => {}
        Term::App(sym, args) if sym.arity == 0 && args.is_empty() => {}
        _ => panic!("expected Skolem constant for X"),
    }
    match &lit.atom.args[1] {
        Term::Var(_) => {}
        _ => panic!("expected universal variable for Y"),
    }
}

#[test]
fn test_skolem_symbols_fresh_across_clauses() {
    // Each existential should introduce a fresh Skolem symbol (global uniqueness).
    let clauses = clausify_src("∃X (p X)\n∃Y (q Y)");
    assert_eq!(clauses.len(), 2);
    let sk1 = match &clauses[0].literals[0].atom.args[0] {
        Term::Const(c) => c.name().to_string(),
        Term::App(sym, args) if sym.arity == 0 && args.is_empty() => sym.name.clone(),
        _ => panic!("expected Skolem constant in first clause"),
    };
    let sk2 = match &clauses[1].literals[0].atom.args[0] {
        Term::Const(c) => c.name().to_string(),
        Term::App(sym, args) if sym.arity == 0 && args.is_empty() => sym.name.clone(),
        _ => panic!("expected Skolem constant in second clause"),
    };
    assert_ne!(
        sk1, sk2,
        "distinct existentials require distinct Skolem symbols"
    );
}
