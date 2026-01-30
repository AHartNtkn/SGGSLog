use super::*;
use proptest::prelude::*;

// =============================================================================
// PROPERTY-BASED TESTS
// =============================================================================
//
// These use proptest to verify properties hold for arbitrary inputs.
// References:  for unification,  for MGU properties.

fn arb_var() -> impl Strategy<Value = Var> {
    "[A-Z][a-z0-9]*".prop_map(|s| Var::new(s))
}

fn arb_constant() -> impl Strategy<Value = Term> {
    "[a-z][a-z0-9]*".prop_map(|s| Term::constant(s))
}

fn arb_ground_term(depth: u32) -> impl Strategy<Value = Term> {
    if depth == 0 {
        arb_constant().boxed()
    } else {
        prop_oneof![
            arb_constant(),
            (
                "[a-z]+",
                prop::collection::vec(arb_ground_term(depth - 1), 1..=3)
            )
                .prop_map(|(name, args)| Term::app(name, args))
        ]
        .boxed()
    }
}

fn arb_term(depth: u32) -> impl Strategy<Value = Term> {
    if depth == 0 {
        prop_oneof![arb_var().prop_map(Term::Var), arb_constant()].boxed()
    } else {
        prop_oneof![
            arb_var().prop_map(Term::Var),
            arb_constant(),
            ("[a-z]+", prop::collection::vec(arb_term(depth - 1), 1..=3))
                .prop_map(|(name, args)| Term::app(name, args))
        ]
        .boxed()
    }
}

fn arb_literal(depth: u32) -> impl Strategy<Value = Literal> {
    (any::<bool>(), "[a-z]+", prop::collection::vec(arb_term(depth), 0..=3))
        .prop_map(|(pos, pred, args)| {
            if pos {
                Literal::pos(pred, args)
            } else {
                Literal::neg(pred, args)
            }
        })
}

fn arb_clause(depth: u32) -> impl Strategy<Value = Clause> {
    prop::collection::vec(arb_literal(depth), 0..=5).prop_map(Clause::new)
}

fn arb_subst_map(depth: u32) -> impl Strategy<Value = HashMap<Var, Term>> {
    prop::collection::vec((arb_var(), arb_term(depth)), 0..=4).prop_map(|pairs| {
        let mut map = HashMap::new();
        for (v, t) in pairs {
            map.insert(v, t);
        }
        map
    })
}

// -------------------------------------------------------------------------
//  Self-unification always succeeds
// -------------------------------------------------------------------------
proptest! {
    #[test]
    fn self_unification_succeeds(term in arb_term(2)) {
        //  Any term unifies with itself
        let result = unify(&term, &term);
        prop_assert!(result.is_success(), "Any term unifies with itself");
        if let UnifyResult::Success(sigma) = result {
            //  Self-MGU should be identity
            let unified = sigma.apply_to_term(&term);
            prop_assert_eq!(unified, term, "Self-unification MGU is identity on term");
        }
    }
}

// -------------------------------------------------------------------------
//  Ground terms unify iff syntactically equal
// -------------------------------------------------------------------------
proptest! {
    #[test]
    fn ground_unification_iff_equal(t1 in arb_ground_term(2), t2 in arb_ground_term(2)) {
        //  Ground unification = syntactic equality
        let result = unify(&t1, &t2);
        if t1 == t2 {
            prop_assert!(result.is_success(), "Equal ground terms must unify");
        } else {
            prop_assert!(result.is_failure(), "Unequal ground terms must not unify");
        }
    }
}

// -------------------------------------------------------------------------
//  Unification is symmetric
// -------------------------------------------------------------------------
proptest! {
    #[test]
    fn unification_is_symmetric(t1 in arb_term(2), t2 in arb_term(2)) {
        //  Symmetry
        let r1 = unify(&t1, &t2);
        let r2 = unify(&t2, &t1);
        prop_assert_eq!(
            r1.is_success(),
            r2.is_success(),
            "Unification must be symmetric"
        );
    }
}

proptest! {
    #[test]
    fn subst_application_distributes_over_app(
        name in "[a-z]+",
        arg1 in arb_term(1),
        arg2 in arb_term(1),
        var_name in "[A-Z][a-z]*",
        replacement in arb_ground_term(1)
    ) {
        // Substitution distributes over function application
        let term = Term::app(&name, vec![arg1.clone(), arg2.clone()]);
        let var = Var::new(&var_name);
        let mut subst = HashMap::new();
        subst.insert(var.clone(), replacement.clone());
        let substituted = term.apply_subst(&subst);
        match substituted {
            Term::App(sym, args) => {
                prop_assert_eq!(sym.name, name);
                prop_assert_eq!(args.len(), 2);
                prop_assert_eq!(args[0].clone(), arg1.apply_subst(&subst));
                prop_assert_eq!(args[1].clone(), arg2.apply_subst(&subst));
            }
            _ => prop_assert!(false, "App should remain App after substitution"),
        }
    }
}

proptest! {
    #[test]
    fn unification_success_makes_terms_equal(t1 in arb_term(2), t2 in arb_term(2)) {
        let result = unify(&t1, &t2);
        if let UnifyResult::Success(sigma) = result {
            let u1 = sigma.apply_to_term(&t1);
            let u2 = sigma.apply_to_term(&t2);
            prop_assert_eq!(u1, u2, "MGU must equalize both terms");
        }
    }
}

proptest! {
    #[test]
    fn unification_idempotent_on_unifier(t1 in arb_term(2), t2 in arb_term(2)) {
        let result = unify(&t1, &t2);
        if let UnifyResult::Success(sigma) = result {
            let u1 = sigma.apply_to_term(&t1);
            let u2 = sigma.apply_to_term(&t2);
            prop_assert_eq!(sigma.apply_to_term(&u1), u1);
            prop_assert_eq!(sigma.apply_to_term(&u2), u2);
        }
    }
}

proptest! {
    #[test]
    fn unification_of_already_unified_terms_is_identity(t1 in arb_term(2), t2 in arb_term(2)) {
        let result = unify(&t1, &t2);
        if let UnifyResult::Success(sigma) = result {
            let u1 = sigma.apply_to_term(&t1);
            let u2 = sigma.apply_to_term(&t2);
            let r2 = unify(&u1, &u2);
            prop_assert!(r2.is_success());
            if let UnifyResult::Success(tau) = r2 {
                prop_assert_eq!(tau.apply_to_term(&u1), u1);
            }
        }
    }
}

proptest! {
    #[test]
    fn occurs_check_rejects_variable_in_term(
        var_name in "[A-Z][a-z]*",
        f in "[a-z]+",
        g in "[a-z]+"
    ) {
        let v = Term::var(&var_name);
        let term = Term::app(&f, vec![Term::app(&g, vec![Term::var(&var_name)])]);
        let result = unify(&v, &term);
        prop_assert!(result.is_failure(), "Occurs check must reject X = f(g(X))");
    }
}

proptest! {
    #[test]
    fn ground_term_unchanged_by_substitution(
        term in arb_ground_term(2),
        subst in arb_subst_map(2)
    ) {
        let applied = term.apply_subst(&subst);
        prop_assert_eq!(applied, term);
    }
}

proptest! {
    #[test]
    fn clause_is_ground_iff_no_variables(clause in arb_clause(2)) {
        let vars = clause.variables();
        prop_assert_eq!(clause.is_ground(), vars.is_empty());
    }
}

proptest! {
    #[test]
    fn literal_negation_involutive(lit in arb_literal(2)) {
        let neg = lit.negated();
        prop_assert_eq!(neg.negated(), lit);
    }
}

proptest! {
    #[test]
    fn literal_unification_success_implies_atom_equality(l1 in arb_literal(2), l2 in arb_literal(2)) {
        let result = unify_literals(&l1, &l2);
        if let UnifyResult::Success(sigma) = result {
            let a1 = sigma.apply_to_term(&Term::app(&l1.atom.predicate, l1.atom.args.clone()));
            let a2 = sigma.apply_to_term(&Term::app(&l2.atom.predicate, l2.atom.args.clone()));
            prop_assert_eq!(a1, a2);
        }
    }
}

proptest! {
    #[test]
    fn variables_collection_complete(term in arb_term(3)) {
        let vars = term.variables();
        fn check_var_in_set(t: &Term, vars: &std::collections::HashSet<Var>) -> bool {
            match t {
                Term::Var(v) => vars.contains(v),
                Term::Const(_) => true,
                Term::App(_, args) => args.iter().all(|a| check_var_in_set(a, vars)),
            }
        }
        prop_assert!(check_var_in_set(&term, &vars), "All variables must be collected");
    }
}

proptest! {
    #[test]
    fn ground_terms_have_no_variables(term in arb_ground_term(3)) {
        let vars = term.variables();
        prop_assert!(vars.is_empty(), "Ground term must have no variables");
        prop_assert!(term.is_ground(), "Ground term must report is_ground = true");
    }
}

proptest! {
    #[test]
    fn substitution_preserves_clause_size(
        preds in prop::collection::vec("[a-z]+", 1..5),
        signs in prop::collection::vec(any::<bool>(), 1..5),
    ) {
        let n = preds.len().min(signs.len());
        let literals: Vec<Literal> = preds.into_iter().zip(signs.into_iter())
            .take(n)
            .map(|(p, s)| {
                if s {
                    Literal::pos(p, vec![Term::var("X")])
                } else {
                    Literal::neg(p, vec![Term::var("X")])
                }
            })
            .collect();
        let clause = Clause::new(literals);
        let mut subst = HashMap::new();
        subst.insert(Var::new("X"), Term::constant("a"));
        let result = clause.apply_subst(&subst);
        prop_assert_eq!(result.literals.len(), clause.literals.len());
    }
}
