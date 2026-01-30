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
