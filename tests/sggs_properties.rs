use proptest::prelude::*;
use sggslog::syntax::{Atom, Clause, Constant, FnSym, Literal, Term, Var};
use std::collections::{HashMap, HashSet};

// ============================================================================
// Strategies
// ============================================================================

prop_compose! {
    fn any_var()(name in "[A-Z][a-zA-Z0-9_]*") -> Var {
        Var::new(name)
    }
}

prop_compose! {
    fn any_constant()(name in "[a-z][a-z0-9_]*") -> Constant {
        Constant::new(name)
    }
}

fn any_term() -> impl Strategy<Value = Term> {
    let leaf = prop_oneof![
        any_var().prop_map(Term::Var),
        any_constant().prop_map(Term::Const),
    ];

    leaf.prop_recursive(
        3,  // deep
        16, // max size
        4,  // items per collection
        |inner| {
            ("[a-z][a-z0-9_]*", prop::collection::vec(inner, 0..3))
                .prop_map(|(name, args)| Term::app(name, args))
        },
    )
}

prop_compose! {
    fn any_atom()(predicate in "[a-z][a-z0-9_]*", args in prop::collection::vec(any_term(), 0..3)) -> Atom {
        Atom::new(predicate, args)
    }
}

prop_compose! {
    fn any_literal()(positive in any::<bool>(), atom in any_atom()) -> Literal {
        if positive {
            Literal::positive(atom)
        } else {
            Literal::negative(atom)
        }
    }
}

prop_compose! {
    fn any_clause()(literals in prop::collection::vec(any_literal(), 0..5)) -> Clause {
        Clause::new(literals)
    }
}

// ============================================================================
// Semantic Properties
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    // === Clause Properties ===

    #[test]
    fn prop_clause_is_horn_semantics(clause in any_clause()) {
        // Semantic definition: A clause is Horn if it has at most one positive literal.
        let positive_count = clause.literals.iter().filter(|l| l.positive).count();
        let expected = positive_count <= 1;

        // This will fail until Clause::is_horn is implemented
        prop_assert_eq!(clause.is_horn(), expected);
    }

    #[test]
    fn prop_clause_variables_soundness(clause in any_clause()) {
        let vars = clause.variables();

        // Every variable found in the terms must be in the set
        for lit in &clause.literals {
            for arg in &lit.atom.args {
                // We do a shallow check or need a helper to collect all vars manually for the test
                // Let's rely on the property:
                // recursive_collect(clause) == clause.variables()
                let mut manual_vars = HashSet::new();
                collect_vars_term(arg, &mut manual_vars);

                for v in manual_vars {
                    prop_assert!(vars.contains(&v));
                }
            }
        }
    }

    #[test]
    fn prop_clause_variables_complete(clause in any_clause()) {
        let mut manual = HashSet::new();
        for lit in &clause.literals {
            collect_vars_literal(lit, &mut manual);
        }
        prop_assert_eq!(clause.variables(), manual);
    }

    #[test]
    fn prop_clause_is_ground_semantics(clause in any_clause()) {
        // Ground iff no variables
        let vars = clause.variables();
        prop_assert_eq!(clause.is_ground(), vars.is_empty());
    }

    // === Literal Properties ===

    #[test]
    fn prop_literal_negation_involutive(lit in any_literal()) {
        // negation is involutive: ¬(¬L) == L
        prop_assert_eq!(lit.negated().negated(), lit.clone());
    }

    #[test]
    fn prop_literal_negation_semantics(lit in any_literal()) {
        let negated = lit.negated();
        // Signs must be opposite
        prop_assert_ne!(lit.positive, negated.positive);
        // Atoms must be identical
        prop_assert_eq!(&lit.atom, &negated.atom);
    }

    #[test]
    fn prop_literal_complementary(lit in any_literal()) {
        let neg = lit.negated();
        prop_assert!(lit.is_complementary(&neg));
        prop_assert!(neg.is_complementary(&lit));
    }

    // === Term Properties ===

    #[test]
    fn prop_term_substitution_identity(term in any_term()) {
        let subst = HashMap::new();
        prop_assert_eq!(term.apply_subst(&subst), term);
    }

    #[test]
    fn prop_term_is_ground_semantics(term in any_term()) {
        let vars = term.variables();
        prop_assert_eq!(term.is_ground(), vars.is_empty());
    }
}

// Helper to manually collect variables for verification
fn collect_vars_term(term: &Term, acc: &mut HashSet<Var>) {
    match term {
        Term::Var(v) => {
            acc.insert(v.clone());
        }
        Term::Const(_) => {}
        Term::App(_, args) => {
            for arg in args {
                collect_vars_term(arg, acc);
            }
        }
    }
}

fn collect_vars_literal(lit: &Literal, acc: &mut HashSet<Var>) {
    for arg in &lit.atom.args {
        collect_vars_term(arg, acc);
    }
}
