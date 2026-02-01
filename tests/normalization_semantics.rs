use proptest::prelude::*;
use sggslog::normalize::{clausify_formula, clausify_statements};
use sggslog::parser::{parse_file, Statement};
use sggslog::syntax::{Atom, Clause, Formula, Literal, Query, Term};
use std::collections::HashMap;

fn single_formula(src: &str) -> sggslog::syntax::Formula {
    let stmts = parse_file(src).expect("parse_file failed");
    assert_eq!(stmts.len(), 1, "expected one statement");
    match &stmts[0] {
        Statement::Formula(f) => f.clone(),
        other => panic!("expected a formula statement, got {:?}", other),
    }
}

fn clausify_all(src: &str) -> Vec<Clause> {
    let formula = single_formula(src);
    let clauses = clausify_formula(&formula).expect("clausify_formula failed");
    assert!(!clauses.is_empty(), "expected at least one clause");
    clauses
}

fn find_clause_with_predicates(clauses: &[Clause], preds: &[&str]) -> Clause {
    clauses
        .iter()
        .find(|c| {
            preds
                .iter()
                .all(|p| c.literals.iter().any(|l| l.atom.predicate == *p))
        })
        .cloned()
        .expect("no clause contained all expected predicates")
}

fn first_literal_with_predicate<'a>(clause: &'a Clause, pred: &str) -> &'a Literal {
    clause
        .literals
        .iter()
        .find(|l| l.atom.predicate == pred)
        .expect("expected literal with predicate")
}

fn clause_has_literal(clause: &Clause, pred: &str, positive: bool) -> bool {
    clause
        .literals
        .iter()
        .any(|l| l.atom.predicate == pred && l.positive == positive)
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

fn clause_to_formula_propositional(clause: &Clause) -> Formula {
    // Convert a propositional clause (zero-ary atoms) into a Formula.
    let mut iter = clause.literals.iter();
    let first = iter
        .next()
        .expect("clause_to_formula_propositional requires non-empty clause");
    let mut acc = literal_to_formula_propositional(first);
    for lit in iter {
        acc = Formula::or(acc, literal_to_formula_propositional(lit));
    }
    acc
}

fn literal_to_formula_propositional(lit: &Literal) -> Formula {
    if !lit.atom.args.is_empty() {
        panic!("propositional conversion only supports zero-ary predicates");
    }
    let atom = Formula::atom(Atom::prop(lit.atom.predicate.as_str()));
    if lit.positive {
        atom
    } else {
        Formula::negation(atom)
    }
}

fn assert_conservative_extension_formula(formula: &Formula, clauses: &[Clause]) {
    let mut orig_preds = std::collections::HashSet::new();
    collect_formula_preds(formula, &mut orig_preds);
    let cnf_preds = collect_cnf_preds(clauses);
    let new_preds: Vec<String> = cnf_preds.difference(&orig_preds).cloned().collect();

    let orig_vars: Vec<String> = orig_preds.into_iter().collect();
    let new_vars: Vec<String> = new_preds;

    for env_orig in all_assignments(&orig_vars.iter().map(|s| s.as_str()).collect::<Vec<_>>()) {
        let original = eval_formula(formula, &env_orig);
        let mut exists_ext = false;
        for env_new in all_assignments(&new_vars.iter().map(|s| s.as_str()).collect::<Vec<_>>()) {
            let mut env_full = env_orig.clone();
            for (k, v) in env_new {
                env_full.insert(k, v);
            }
            if eval_cnf(clauses, &env_full) {
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

fn arb_pred() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("p".to_string()),
        Just("q".to_string()),
        Just("r".to_string()),
        Just("s".to_string()),
    ]
}

fn arb_formula(depth: u32) -> impl Strategy<Value = Formula> {
    if depth == 0 {
        arb_pred()
            .prop_map(|p| Formula::atom(Atom::prop(p.as_str())))
            .boxed()
    } else {
        prop_oneof![
            arb_pred().prop_map(|p| Formula::atom(Atom::prop(p.as_str()))),
            arb_formula(depth - 1).prop_map(Formula::negation),
            (arb_formula(depth - 1), arb_formula(depth - 1)).prop_map(|(a, b)| Formula::and(a, b)),
            (arb_formula(depth - 1), arb_formula(depth - 1)).prop_map(|(a, b)| Formula::or(a, b)),
            (arb_formula(depth - 1), arb_formula(depth - 1))
                .prop_map(|(a, b)| Formula::implies(a, b)),
        ]
        .boxed()
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    #[test]
    fn clausify_conservative_extension_prop(formula in arb_formula(2)) {
        let clauses = clausify_formula(&formula).expect("clausify_formula failed");
        prop_assert!(!clauses.is_empty(), "expected at least one clause");
        assert_conservative_extension_formula(&formula, &clauses);
    }
}

#[test]
fn test_clausify_statement_clause_passthrough() {
    let clause = Clause::new(vec![Literal::pos("p", vec![]), Literal::neg("q", vec![])]);
    let stmt = Statement::Clause(clause.clone());
    let clauses = sggslog::normalize::clausify_statement(&stmt).expect("clausify_statement failed");
    assert!(
        clauses.iter().any(|c| {
            c.literals.len() == 2
                && clause_has_literal(c, "p", true)
                && clause_has_literal(c, "q", false)
        }),
        "explicit clause statement should be preserved"
    );
}

#[test]
fn test_clausify_statement_rejects_query_and_directive() {
    let query = Statement::Query(Query::new(vec![Literal::pos("p", vec![])]));
    assert!(
        sggslog::normalize::clausify_statement(&query).is_err(),
        "clausify_statement should reject queries"
    );
    let directive = Statement::Directive(sggslog::parser::Directive::Load("f.sggs".to_string()));
    assert!(
        sggslog::normalize::clausify_statement(&directive).is_err(),
        "clausify_statement should reject directives"
    );
}

#[test]
fn test_clausify_statements_mixed_clause_and_formula() {
    let stmts = parse_file("clause p | ~q\nr -> s").expect("parse_file failed");
    let clauses = clausify_statements(&stmts).expect("clausify_statements failed");
    assert!(
        clauses
            .iter()
            .any(|c| clause_has_literal(c, "p", true) && clause_has_literal(c, "q", false)),
        "explicit clause should appear in normalized output"
    );

    // Allow definitional/Tseitin CNF: require conservative extension over the original symbols.
    let clause_formula = clause_to_formula_propositional(&Clause::new(vec![
        Literal::pos("p", vec![]),
        Literal::neg("q", vec![]),
    ]));
    let implication = single_formula("r -> s");
    let combined = Formula::and(clause_formula, implication);
    assert_conservative_extension_formula(&combined, &clauses);
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
    let clauses = clausify_all("∀X ((p X) -> (q X))");
    let p_lits: Vec<&Literal> = clauses
        .iter()
        .flat_map(|c| c.literals.iter())
        .filter(|l| l.atom.predicate == "p")
        .collect();
    let q_lits: Vec<&Literal> = clauses
        .iter()
        .flat_map(|c| c.literals.iter())
        .filter(|l| l.atom.predicate == "q")
        .collect();
    assert!(!p_lits.is_empty(), "expected some occurrence of p in CNF");
    assert!(!q_lits.is_empty(), "expected some occurrence of q in CNF");
    let has_both = clauses.iter().any(|c| {
        c.literals.iter().any(|l| l.atom.predicate == "p")
            && c.literals.iter().any(|l| l.atom.predicate == "q")
    });
    assert!(
        has_both,
        "implication should produce at least one clause relating p and q"
    );
    for lit in p_lits.iter().chain(q_lits.iter()) {
        match &lit.atom.args[0] {
            Term::Var(_) => {}
            _ => panic!("implication under ∀ should not introduce Skolem terms for p/q"),
        }
    }

    // If any clause contains both p and q, their argument terms must match.
    for clause in &clauses {
        let p_terms: Vec<&Term> = clause
            .literals
            .iter()
            .filter(|l| l.atom.predicate == "p")
            .map(|l| &l.atom.args[0])
            .collect();
        let q_terms: Vec<&Term> = clause
            .literals
            .iter()
            .filter(|l| l.atom.predicate == "q")
            .map(|l| &l.atom.args[0])
            .collect();
        if let (Some(p), Some(q)) = (p_terms.first(), q_terms.first()) {
            assert_eq!(
                p, q,
                "p and q occurrences in the same clause should share the same argument"
            );
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
    // p ∧ q should be a conservative extension of the original vocabulary.
    assert_conservative_extension("p ∧ q");
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
    let clauses = clausify_all("∃X (p X)");
    let clause = find_clause_with_predicates(&clauses, &["p"]);
    let lit = first_literal_with_predicate(&clause, "p");
    match &lit.atom.args[0] {
        Term::App(sym, args) if sym.arity == 0 && args.is_empty() => {
            assert!(lit.is_ground());
        }
        _ => panic!("expected Skolem constant"),
    }
}

#[test]
fn test_exists_skolem_constant_preserves_sort() {
    let clauses = clausify_all("∃X:s1 (p X)");
    let clause = find_clause_with_predicates(&clauses, &["p"]);
    let lit = first_literal_with_predicate(&clause, "p");
    match &lit.atom.args[0] {
        Term::App(sym, args) if sym.arity == 0 && args.is_empty() => {
            assert_eq!(sym.result_sort.as_deref(), Some("s1"));
        }
        _ => panic!("expected sorted Skolem constant"),
    }
}

#[test]
fn test_forall_exists_skolemizes_to_function() {
    let clauses = clausify_all("∀X ∃Y (p X Y)");
    let clause = find_clause_with_predicates(&clauses, &["p"]);
    let lit = first_literal_with_predicate(&clause, "p");
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
    let clauses = clausify_all("∀X:s1 ∃Y:s2 (p X Y)");
    let clause = find_clause_with_predicates(&clauses, &["p"]);
    let lit = first_literal_with_predicate(&clause, "p");
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
    let clauses = clausify_all("∀X ∃Y ∃Z (p X Y Z)");
    let clause = find_clause_with_predicates(&clauses, &["p"]);
    let lit = first_literal_with_predicate(&clause, "p");
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
    let clauses = clausify_all("∀X ∃Y ∀Z ∃W (p X Y Z W)");
    let clause = find_clause_with_predicates(&clauses, &["p"]);
    let lit = first_literal_with_predicate(&clause, "p");
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
    let clauses = clausify_all("∃X ∀Y (p X Y)");
    let clause = find_clause_with_predicates(&clauses, &["p"]);
    let lit = first_literal_with_predicate(&clause, "p");
    match &lit.atom.args[0] {
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
        Term::App(sym, args) if sym.arity == 0 && args.is_empty() => sym.name.clone(),
        _ => panic!("expected Skolem constant in first clause"),
    };
    let sk2 = match &clauses[1].literals[0].atom.args[0] {
        Term::App(sym, args) if sym.arity == 0 && args.is_empty() => sym.name.clone(),
        _ => panic!("expected Skolem constant in second clause"),
    };
    assert_ne!(
        sk1, sk2,
        "distinct existentials require distinct Skolem symbols"
    );
}

#[test]
fn test_skolem_symbols_fresh_from_user_signature() {
    // Skolem symbols must be fresh relative to user-provided symbols.
    let clauses = clausify_src("p a\n∃X (p X)");
    let mut p_consts = std::collections::HashSet::new();
    for c in clauses {
        for lit in c.literals {
            if lit.atom.predicate == "p" && lit.atom.args.len() == 1 {
                if let Term::App(sym, args) = &lit.atom.args[0] {
                    if sym.arity == 0 && args.is_empty() {
                        p_consts.insert(sym.name.clone());
                    }
                }
            }
        }
    }
    assert!(p_consts.contains("a"));
    assert!(
        p_consts.len() >= 2,
        "Skolem constant must be distinct from user constant"
    );
}

#[test]
fn test_skolem_functions_fresh_across_statements_with_universals() {
    // Each existential in separate statements should get a fresh Skolem function
    // even if the formulas are alpha-equivalent.
    // Source: standard Skolemization; distinct existentials introduce fresh symbols.
    let clauses = clausify_src("∀X ∃Y (p X Y)\n∀X ∃Y (q X Y)");
    assert_eq!(clauses.len(), 2);

    let f1 = match &clauses[0].literals[0].atom.args[1] {
        Term::App(sym, args) => (sym.name.clone(), args.clone()),
        _ => panic!("expected Skolem function in first clause"),
    };
    let f2 = match &clauses[1].literals[0].atom.args[1] {
        Term::App(sym, args) => (sym.name.clone(), args.clone()),
        _ => panic!("expected Skolem function in second clause"),
    };
    assert_ne!(
        f1.0, f2.0,
        "Skolem functions should be fresh across statements"
    );
    assert_eq!(
        f1.1.len(),
        1,
        "Skolem function should depend on the universal"
    );
    assert_eq!(
        f2.1.len(),
        1,
        "Skolem function should depend on the universal"
    );
}

#[test]
fn test_skolemization_does_not_capture_universals_from_other_statements() {
    // Source: standard Skolemization + spec.md (variables scoped per clause).
    let clauses = clausify_src("∀X (p X)\n∃Y (q Y)");
    assert_eq!(clauses.len(), 2);

    // The existential in the second statement should introduce a Skolem constant,
    // not a function of the unrelated universal from the first statement.
    let sk = match &clauses[1].literals[0].atom.args[0] {
        Term::App(sym, args) => (sym.name.clone(), args.len()),
        _ => panic!("expected Skolem symbol in second clause"),
    };
    assert_eq!(
        sk.1, 0,
        "Skolem symbol should be a constant; universals from other statements are out of scope"
    );
}

#[test]
fn test_negated_forall_pushes_negation_and_skolemizes() {
    // ¬∀X p(X) == ∃X ¬p(X) => Skolem constant, negative literal.
    let clauses = clausify_all("¬∀X (p X)");
    let clause = find_clause_with_predicates(&clauses, &["p"]);
    let lit = first_literal_with_predicate(&clause, "p");
    assert!(
        !lit.positive,
        "negated forall should produce negative literal"
    );
    assert!(
        lit.is_ground(),
        "existential after negation should skolemize"
    );
}

#[test]
fn test_negated_exists_pushes_negation_to_forall() {
    // ¬∃X p(X) == ∀X ¬p(X) => negative literal with variable.
    let clauses = clausify_all("¬∃X (p X)");
    let clause = find_clause_with_predicates(&clauses, &["p"]);
    let lit = first_literal_with_predicate(&clause, "p");
    assert!(
        !lit.positive,
        "negated exists should produce negative literal"
    );
    match &lit.atom.args[0] {
        Term::Var(_) => {}
        _ => panic!("expected variable (universal) after negated exists"),
    }
}
