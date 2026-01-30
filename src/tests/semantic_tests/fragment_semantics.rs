use super::*;
use crate::syntax::{Atom, AtomCmp, AtomOrder};

fn term_size(t: &Term) -> usize {
    match t {
        Term::Var(_) | Term::Const(_) => 1,
        Term::App(_, args) => 1 + args.iter().map(term_size).sum::<usize>(),
    }
}

struct SizeOrder;

impl AtomOrder for SizeOrder {
    fn cmp(&self, a: &Atom, b: &Atom) -> AtomCmp {
        if a.predicate != b.predicate {
            return AtomCmp::Incomparable;
        }
        let sa: usize = a.args.iter().map(term_size).sum();
        let sb: usize = b.args.iter().map(term_size).sum();
        if sa == sb {
            AtomCmp::Equal
        } else if sa > sb {
            AtomCmp::Greater
        } else {
            AtomCmp::Less
        }
    }
}

// =============================================================================
// FRAGMENT DETECTION (DECIDABLE FRAGMENTS)
// =============================================================================
//
// Reference: [BW20] Definitions 3 and 5 (ground-preserving, restrained)

#[test]
fn ground_preserving_check() {
    // Datalog-style clause: Var(C+) ⊆ Var(C-)
    let clause = Clause::new(vec![
        Literal::neg("edge", vec![Term::var("X"), Term::var("Z")]),
        Literal::neg("path", vec![Term::var("Z"), Term::var("Y")]),
        Literal::pos("path", vec![Term::var("X"), Term::var("Y")]),
    ]);
    assert!(clause.is_positively_ground_preserving());
}

#[test]
fn ground_preserving_negative_variant() {
    // Negatively ground-preserving: Var(C) ⊆ Var(C+)
    let clause = Clause::new(vec![
        Literal::neg("q", vec![Term::var("X")]),
        Literal::pos("p", vec![Term::var("X"), Term::var("Y")]),
    ]);
    assert!(clause.is_negatively_ground_preserving());
    assert!(!clause.is_positively_ground_preserving());
    assert!(clause.is_ground_preserving());
}

#[test]
fn restrained_vacuous_for_ground_positive() {
    // No non-ground positive literals => restrained condition is vacuous.
    let clause = Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("Q", vec![Term::constant("a")]),
    ]);
    let order = SizeOrder;
    assert!(clause.is_restrained(&order));
}

#[test]
fn restrained_requires_ground_preserving() {
    // [BW20] Def 5: restrained implies ground-preserving.
    let clause = Clause::new(vec![
        Literal::neg("Q", vec![Term::constant("a")]),
        Literal::pos("P", vec![Term::var("X")]),
    ]);
    assert!(!clause.is_positively_ground_preserving());
    let order = SizeOrder;
    assert!(!clause.is_restrained(&order));
}

#[test]
fn not_ground_preserving_when_positive_introduces_new_var() {
    // Var(C+) ⊄ Var(C-) => not positively ground-preserving
    let clause = Clause::new(vec![
        Literal::neg("Q", vec![Term::var("X")]),
        Literal::pos("P", vec![Term::var("X"), Term::var("Y")]),
    ]);
    assert!(!clause.is_positively_ground_preserving());
    assert!(!clause.is_ground_preserving());
}

#[test]
fn restrained_rejects_non_dominating_negative_literal() {
    // ¬P(x) ∨ P(f(x)) is ground-preserving but not restrained under size-based order.
    let clause = Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("P", vec![Term::app("f", vec![Term::var("X")])]),
    ]);
    let order = SizeOrder;
    assert!(clause.is_positively_ground_preserving());
    assert!(!clause.is_restrained(&order));
}

#[test]
fn pvd_clause_true_when_depth_non_increasing() {
    // PVD: depth_x(C+) <= depth_x(C-) for all x in Var(C+)
    let clause = Clause::new(vec![
        Literal::neg("P", vec![Term::app("f", vec![Term::var("X")])]),
        Literal::pos("P", vec![Term::var("X")]),
    ]);
    assert!(clause.is_pvd());
}

#[test]
fn pvd_clause_false_when_depth_increases() {
    let clause = Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("P", vec![Term::app("f", vec![Term::var("X")])]),
    ]);
    assert!(!clause.is_pvd());
}

#[test]
fn pvd_clause_requires_positive_ground_preserving() {
    let clause = Clause::new(vec![
        Literal::neg("Q", vec![Term::constant("a")]),
        Literal::pos("P", vec![Term::var("X")]),
    ]);
    assert!(!clause.is_pvd());
}

#[test]
fn theory_pvd_all_clauses() {
    let mut theory = crate::theory::Theory::new();
    let c1 = Clause::new(vec![
        Literal::neg("P", vec![Term::app("f", vec![Term::var("X")])]),
        Literal::pos("P", vec![Term::var("X")]),
    ]);
    let c2 = Clause::new(vec![
        Literal::neg("Q", vec![Term::var("Y")]),
        Literal::pos("R", vec![Term::var("Y")]),
    ]);
    theory.add_clause(c1);
    theory.add_clause(c2);
    assert!(theory.is_pvd());
}

#[test]
fn sort_refined_pvd_respects_infinite_sorts_depth() {
    use std::collections::HashSet;
    let mut inf = HashSet::new();
    inf.insert("s_inf".to_string());

    let x = Term::Var(Var::new_with_sort("X", "s_inf"));
    let fx = Term::app_with_sort("f", "s_inf", vec![x.clone()]);
    let clause = Clause::new(vec![
        Literal::neg("P", vec![fx]),
        Literal::pos("P", vec![x]),
    ]);
    assert!(clause.is_sort_refined_pvd(&inf));
}

#[test]
fn sort_refined_pvd_fails_on_depth_increase() {
    use std::collections::HashSet;
    let mut inf = HashSet::new();
    inf.insert("s_inf".to_string());

    let x = Term::Var(Var::new_with_sort("X", "s_inf"));
    let fx = Term::app_with_sort("f", "s_inf", vec![x.clone()]);
    let clause = Clause::new(vec![
        Literal::neg("P", vec![x]),
        Literal::pos("P", vec![fx]),
    ]);
    assert!(!clause.is_sort_refined_pvd(&inf));
}

#[test]
fn sort_restrained_vacuous_for_finite_sorts() {
    use std::collections::HashSet;
    let inf = HashSet::new();
    let x = Term::Var(Var::new_with_sort("X", "s_fin"));
    let clause = Clause::new(vec![Literal::pos("P", vec![x])]);
    let order = SizeOrder;
    assert!(clause.is_sort_restrained(&inf, &order));
}

#[test]
fn sort_restrained_requires_negative_dominance_for_infinite() {
    use std::collections::HashSet;
    let mut inf = HashSet::new();
    inf.insert("s_inf".to_string());
    let x = Term::Var(Var::new_with_sort("X", "s_inf"));
    let clause = Clause::new(vec![Literal::pos("P", vec![x])]);
    let order = SizeOrder;
    assert!(!clause.is_sort_restrained(&inf, &order));
}

#[test]
fn sort_restrained_mixed_sorts_still_requires_infinite_dominance() {
    use std::collections::HashSet;
    let mut inf = HashSet::new();
    inf.insert("s_inf".to_string());
    let x = Term::Var(Var::new_with_sort("X", "s_inf"));
    let y = Term::Var(Var::new_with_sort("Y", "s_fin"));
    let fx = Term::app_with_sort("f", "s_inf", vec![x.clone()]);
    let clause = Clause::new(vec![
        Literal::neg("P", vec![x, y.clone()]),
        Literal::pos("P", vec![fx, y]),
    ]);
    let order = SizeOrder;
    assert!(!clause.is_sort_restrained(&inf, &order));
}

#[test]
fn sort_refined_pvd_ignores_finite_sorts() {
    use std::collections::HashSet;
    let mut inf = HashSet::new();
    inf.insert("s_inf".to_string());

    let x = Term::Var(Var::new_with_sort("X", "s_inf"));
    let y = Term::Var(Var::new_with_sort("Y", "s_fin"));
    let fx = Term::app_with_sort("f", "s_inf", vec![x.clone()]);
    let clause = Clause::new(vec![
        Literal::neg("P", vec![fx, y.clone()]),
        Literal::pos("P", vec![x, y]),
    ]);
    assert!(clause.is_sort_refined_pvd(&inf));
}

#[test]
fn sort_refined_pvd_fails_when_infinite_depth_increases() {
    use std::collections::HashSet;
    let mut inf = HashSet::new();
    inf.insert("s_inf".to_string());

    let x = Term::Var(Var::new_with_sort("X", "s_inf"));
    let fx = Term::app_with_sort("f", "s_inf", vec![x.clone()]);
    let clause = Clause::new(vec![
        Literal::neg("P", vec![x.clone()]),
        Literal::pos("P", vec![fx]),
    ]);
    assert!(!clause.is_sort_refined_pvd(&inf));
}

#[test]
fn theory_sort_restrained_and_sort_refined_pvd() {
    use std::collections::HashSet;
    let mut inf = HashSet::new();
    inf.insert("s_inf".to_string());

    let x = Term::Var(Var::new_with_sort("X", "s_inf"));
    let fx = Term::app_with_sort("f", "s_inf", vec![x.clone()]);
    let clause = Clause::new(vec![
        Literal::neg("P", vec![fx]),
        Literal::pos("P", vec![x]),
    ]);

    let mut theory = crate::theory::Theory::new();
    theory.add_clause(clause);
    assert!(theory.is_sort_refined_pvd(&inf));
}

#[test]
fn theory_restrained_respects_ordering() {
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("P", vec![Term::app("f", vec![Term::var("X")])]),
    ]));
    let order = SizeOrder;
    assert!(!theory.is_restrained(&order));
}

#[test]
fn theory_sort_restrained_respects_ordering() {
    use std::collections::HashSet;
    let mut inf = HashSet::new();
    inf.insert("s_inf".to_string());
    let x = Term::Var(Var::new_with_sort("X", "s_inf"));
    let clause = Clause::new(vec![Literal::pos("P", vec![x])]);
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(clause);
    let order = SizeOrder;
    assert!(!theory.is_sort_restrained(&inf, &order));
}

#[test]
fn theory_epr_function_free() {
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "P",
        vec![Term::constant("a")],
    )]));
    assert!(theory.is_epr());

    let mut theory2 = crate::theory::Theory::new();
    theory2.add_clause(Clause::new(vec![Literal::pos(
        "P",
        vec![Term::app("f", vec![Term::constant("a")])],
    )]));
    assert!(!theory2.is_epr());
}

#[test]
fn theory_bdi_ground_is_true_and_depth_increase_is_false() {
    let mut t1 = crate::theory::Theory::new();
    t1.add_clause(Clause::new(vec![Literal::pos(
        "P",
        vec![Term::constant("a")],
    )]));
    assert!(t1.is_bdi());

    let mut t2 = crate::theory::Theory::new();
    t2.add_clause(Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("P", vec![Term::app("f", vec![Term::var("X")])]),
    ]));
    assert!(!t2.is_bdi());
}

#[test]
fn theory_bdi_allows_non_increasing_depth() {
    let mut t = crate::theory::Theory::new();
    t.add_clause(Clause::new(vec![
        Literal::neg("P", vec![Term::app("f", vec![Term::var("X")])]),
        Literal::pos("P", vec![Term::app("f", vec![Term::var("X")])]),
    ]));
    assert!(t.is_bdi());
}

#[test]
fn theory_bdi_allows_multi_arity_when_depth_constant() {
    let mut t = crate::theory::Theory::new();
    t.add_clause(Clause::new(vec![
        Literal::neg(
            "P",
            vec![Term::app("f", vec![Term::var("X"), Term::var("Y")])],
        ),
        Literal::pos(
            "P",
            vec![Term::app("f", vec![Term::var("X"), Term::var("Y")])],
        ),
    ]));
    assert!(t.is_bdi());
}
