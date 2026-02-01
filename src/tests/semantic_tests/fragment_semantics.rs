use super::*;
use crate::syntax::{Atom, AtomCmp, AtomOrder};

fn term_size(t: &Term) -> usize {
    match t {
        Term::Var(_) => 1,
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
fn not_positively_ground_preserving_when_positive_introduces_new_var() {
    // SGGSdpFOL Def. 4: "positively ground-preserving if Var(C) ⊆ Var(C − )".
    // SGGSdpFOL Def. 4: "negatively ground-preserving if Var(C) ⊆ Var(C + )".
    // SGGSdpFOL Def. 4: "ground-preserving if it is one or the other."
    let clause = Clause::new(vec![
        Literal::neg("Q", vec![Term::var("X")]),
        Literal::pos("P", vec![Term::var("X"), Term::var("Y")]),
    ]);
    assert!(!clause.is_positively_ground_preserving());
    assert!(clause.is_negatively_ground_preserving());
    assert!(clause.is_ground_preserving()); // true because negatively ground-preserving
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
fn negatively_restrained_accepts_positive_dominance() {
    // Dual of restrained: non-ground negative literal must be dominated by a positive literal.
    // Source: BW20 (restrained fragment), dual of Def. 5.
    let clause = Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("P", vec![Term::app("f", vec![Term::var("X")])]),
    ]);
    let order = SizeOrder;
    assert!(clause.is_negatively_ground_preserving());
    assert!(clause.is_negatively_restrained(&order));
}

#[test]
fn negatively_restrained_requires_negative_ground_preserving() {
    // Source: BW20 (ground-preserving requirement for restrained fragments).
    let clause = Clause::new(vec![
        Literal::neg("P", vec![Term::var("X"), Term::var("Y")]),
        Literal::pos("P", vec![Term::var("X")]),
    ]);
    let order = SizeOrder;
    assert!(!clause.is_negatively_ground_preserving());
    assert!(!clause.is_negatively_restrained(&order));
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
fn sort_negatively_restrained_vacuous_for_finite_sorts() {
    // Source: BW20 Def. 10 (sort-restrained), negative variant.
    use std::collections::HashSet;
    let inf = HashSet::new();
    let x = Term::Var(Var::new_with_sort("X", "s_fin"));
    let clause = Clause::new(vec![Literal::neg("P", vec![x])]);
    let order = SizeOrder;
    assert!(clause.is_sort_negatively_restrained(&inf, &order));
}

#[test]
fn sort_negatively_restrained_requires_positive_dominance_for_infinite() {
    // Source: BW20 Def. 10 (sort-restrained), negative variant.
    use std::collections::HashSet;
    let mut inf = HashSet::new();
    inf.insert("s_inf".to_string());
    let x = Term::Var(Var::new_with_sort("X", "s_inf"));
    let clause = Clause::new(vec![Literal::neg("P", vec![x])]);
    let order = SizeOrder;
    assert!(!clause.is_sort_negatively_restrained(&inf, &order));
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
fn theory_restrained_fails_if_any_clause_violates() {
    // Source: BW20 (restrained fragment requires all clauses).
    let mut theory = crate::theory::Theory::new();
    // Restrained clause
    theory.add_clause(Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("P", vec![Term::var("X")]),
    ]));
    // Non-restrained clause (positive literal not dominated)
    theory.add_clause(Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("P", vec![Term::app("f", vec![Term::var("X")])]),
    ]));
    let order = SizeOrder;
    assert!(!theory.is_restrained(&order));
}

#[test]
fn theory_negatively_restrained_respects_ordering() {
    // Source: BW20 (restrained fragment, theory-level all-clauses check).
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("P", vec![Term::app("f", vec![Term::var("X")])]),
    ]));
    let order = SizeOrder;
    assert!(theory.is_negatively_restrained(&order));
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
fn theory_sort_negatively_restrained_respects_ordering() {
    // Source: BW20 Def. 10 (sort-restrained), negative variant.
    use std::collections::HashSet;
    let mut inf = HashSet::new();
    inf.insert("s_inf".to_string());
    let x = Term::Var(Var::new_with_sort("X", "s_inf"));
    let clause = Clause::new(vec![Literal::neg("P", vec![x])]);
    let mut theory = crate::theory::Theory::new();
    theory.add_clause(clause);
    let order = SizeOrder;
    assert!(!theory.is_sort_negatively_restrained(&inf, &order));
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

// =============================================================================
// BDI (Bounded Depth Increase) fragment
// =============================================================================
//
// Formal definition source:
// Lamotte-Schubert, M. & Weidenbach, C. "BDI: a new decidable clause class."
// Journal of Logic and Computation (2014).
//
// Formal definition (Lamotte-Schubert & Weidenbach, 2014):
//
// Let a clause be written Γ -> Δ (i.e., ¬Γ ∨ Δ). Let depth(t) be term depth
// (variables/constants depth 0; f(t1..tn) has depth 1+max depth), and depth_x(t)
// the max depth of variable x in t (0 if x does not occur). For a literal/atom,
// depth_x is the max over its arguments; for Γ or Δ, depth_x is the max over all atoms.
//
// A watched-arguments function warg assigns each predicate symbol P a list of
// watched argument positions. For an atom P(t1..tm), warg(P(t1..tm)) is the list
// of subterms at those positions.
//
// Similar atoms: same predicate symbol and same term shape position-wise
// (same function/constant symbols; variables may differ).
//
// Depth-increasing clause: there exist a variable x and a positive atom
// P(t1..tm) in Δ with a unique depth-increasing position i such that:
//   - depth_x(ti) > depth_x(Γ)
//   - for all j != i, depth_x(tj) <= depth_x(Γ)
//   - for every depth-increasing variable x, replacing ti with x yields
//     depth_x(P(t1..t{i-1}, x, t{i+1}..tm)) <= depth_x(Γ)
// The predicate P is the depth-increasing predicate, and i its unique position.
//
// Reachability: predicate Q is reachable from P if some clause has P in Γ and Q in Δ,
// using the transitive closure. Depth-increasing predicates must be acyclic under
// reachability (no cycles among depth-increasing predicates).
//
// Origination: terms in warg(P(...)) in a clause derived from a depth-increasing
// clause must appear among warg(Q(...)) for some body atom Q in the originating
// depth-increasing clause.
//
// BDI requires existence of a warg function such that every clause satisfies:
//
// PVD: Var(Δ) ⊆ Var(Γ) and for all x in Var(Δ), depth_x(Δ) <= depth_x(Γ), OR
//
// BDI-1 (Γ -> Δ is depth-increasing, P is the depth-increasing predicate, i unique):
//   (i) Every atom P' in Δ is similar to P and uses the same depth-increasing position i.
//   (ii) For any atom Q in Δ not similar to P, all watched arguments are variables.
//   (iii) For any atom Q in Γ, all watched arguments are variables.
//   (iv) For any similar pair Q in Γ and Q in Δ, their watched-argument lists are identical.
//   (v) For any atom Q in Γ whose predicate is reachable from P, all watched arguments are variables.
//
// BDI-2 (Γ -> Δ is not depth-increasing):
//   (i) For any atom P in Δ whose predicate is reachable from some depth-increasing clause,
//       all watched arguments are variables.
//   (ii) For any similar pair P in Δ and P' in Γ, their watched-argument lists are identical.
//   (iii) For any depth-increasing clause C that reaches P, the watched arguments of P in
//         this clause must originate from C.
//
// The tests below use the paper's example clause sets: one BDI set and one non-BDI set.

fn bdi_example_from_paper() -> crate::theory::Theory {
    // Source: Lamotte-Schubert & Weidenbach (2014), Example BDI clause set (1)-(5).
    // (1) -> P(f(a), h(a), a)
    // (2) P(x,y,z) -> Q(x,y,f(g(x))), S(x,y)
    // (3) Q(x,y,f(u)) -> P(x,y,u)
    // (4) S(x,y) -> T(x)
    // (5) P(a,b,c) ->
    let a = Term::constant("a");
    let b = Term::constant("b");
    let c = Term::constant("c");
    let x = Term::var("x");
    let y = Term::var("y");
    let z = Term::var("z");
    let u = Term::var("u");

    let f_a = Term::app("f", vec![a.clone()]);
    let h_a = Term::app("h", vec![a.clone()]);
    let g_x = Term::app("g", vec![x.clone()]);
    let f_g_x = Term::app("f", vec![g_x]);
    let f_u = Term::app("f", vec![u.clone()]);

    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![Literal::pos(
        "P",
        vec![f_a, h_a, a.clone()],
    )]));
    theory.add_clause(Clause::new(vec![
        Literal::neg("P", vec![x.clone(), y.clone(), z.clone()]),
        Literal::pos("Q", vec![x.clone(), y.clone(), f_g_x]),
        Literal::pos("S", vec![x.clone(), y.clone()]),
    ]));
    theory.add_clause(Clause::new(vec![
        Literal::neg("Q", vec![x.clone(), y.clone(), f_u]),
        Literal::pos("P", vec![x.clone(), y.clone(), u]),
    ]));
    theory.add_clause(Clause::new(vec![
        Literal::neg("S", vec![x.clone(), y.clone()]),
        Literal::pos("T", vec![x]),
    ]));
    theory.add_clause(Clause::new(vec![Literal::neg("P", vec![a, b, c])]));
    theory
}

fn bdi_counterexample_from_paper() -> crate::theory::Theory {
    // Source: Lamotte-Schubert & Weidenbach (2014), BDI-1/BDI-2 counterexample (1)-(3).
    // (1) P(f(x,y),z,u) -> P(x,z,y)
    // (2) P(x,z,y) -> Q(x,g(z),u), Q(x,g(z),y)
    // (3) Q(x,g(z),u) -> P(x,z,y)
    let x = Term::var("x");
    let y = Term::var("y");
    let z = Term::var("z");
    let u = Term::var("u");
    let f_xy = Term::app("f", vec![x.clone(), y.clone()]);
    let g_z = Term::app("g", vec![z.clone()]);

    let mut theory = crate::theory::Theory::new();
    theory.add_clause(Clause::new(vec![
        Literal::neg("P", vec![f_xy, z.clone(), u.clone()]),
        Literal::pos("P", vec![x.clone(), z.clone(), y.clone()]),
    ]));
    theory.add_clause(Clause::new(vec![
        Literal::neg("P", vec![x.clone(), z.clone(), y.clone()]),
        Literal::pos("Q", vec![x.clone(), g_z.clone(), u.clone()]),
        Literal::pos("Q", vec![x.clone(), g_z, y.clone()]),
    ]));
    theory.add_clause(Clause::new(vec![
        Literal::neg("Q", vec![x.clone(), Term::app("g", vec![z]), u]),
        Literal::pos("P", vec![x, Term::var("z"), y]),
    ]));
    theory
}

#[test]
fn theory_bdi_example_from_paper_is_bdi() {
    let theory = bdi_example_from_paper();
    assert!(theory.is_bdi());
}

#[test]
fn theory_bdi_counterexample_from_paper_is_not_bdi() {
    let theory = bdi_counterexample_from_paper();
    assert!(!theory.is_bdi());
}
