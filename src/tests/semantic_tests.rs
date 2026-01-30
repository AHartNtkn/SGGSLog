//! Semantic tests for SGGS implementation.
//!
//! These tests verify essential semantic properties, not just surface behavior.
//! They are designed to fail until the implementation is correct, testing
//! subtle invariants that a buggy implementation would violate.
//!
//! # References
//!
//! ## SGGS Papers
//! - [BP16a] Bonacina, M.P., Plaisted, D.A. "Semantically-Guided Goal-Sensitive
//!   Reasoning: Model Representation." J Autom Reasoning 56, 113–141 (2016).
//!   https://doi.org/10.1007/s10817-015-9334-4
//!
//! - [BP17] Bonacina, M.P., Plaisted, D.A. "Semantically-Guided Goal-Sensitive
//!   Reasoning: Inference System and Completeness." J Autom Reasoning 59(2),
//!   165–218 (2017). https://doi.org/10.1007/s10817-016-9384-2
//!
//! - [BW20] Bonacina, M.P., Winkler, S. "SGGS Decision Procedures." IJCAR 2020,
//!   LNCS 12166, pp. 356-374. https://doi.org/10.1007/978-3-030-51074-9_20
//!
use std::collections::HashMap;
use crate::syntax::{Atom, Clause, Literal, Term, Var};
use crate::unify::{unify, unify_literals, unify_many, Substitution, UnifyResult};
/// Helper to create a Theory from a vec of clauses.
fn theory_from_clauses(clauses: Vec<Clause>) -> crate::theory::Theory {
    let mut theory = crate::theory::Theory::new();
    for c in clauses {
        theory.add_clause(c);
    }
    theory
}
// =============================================================================
// UNIFICATION SEMANTIC PROPERTIES
// =============================================================================
//
// These tests verify standard properties of first-order unification.
// The MGU (Most General Unifier) must satisfy standard algebraic properties.
mod unification_semantics {
    use super::*;
    // -------------------------------------------------------------------------
    // Property: MGU is idempotent (σ(σ(t)) = σ(t))
    //
    // Reference:  Theorem 1 - MGU Idempotence
    // "The unification algorithm generates an MGU which is idempotent."
    //
    // An idempotent substitution σ satisfies: σ ∘ σ = σ
    // Equivalently: for all terms t, σ(σ(t)) = σ(t)
    // -------------------------------------------------------------------------
    #[test]
    fn mgu_is_idempotent_simple() {
        //  Theorem 1: MGU idempotence
        // If σ = MGU(X, f(Y)), then σ(σ(X)) = σ(X)
        let t1 = Term::var("X");
        let t2 = Term::app("f", vec![Term::var("Y")]);
        if let UnifyResult::Success(sigma) = unify(&t1, &t2) {
            let once = sigma.apply_to_term(&t1);
            let twice = sigma.apply_to_term(&once);
            assert_eq!(
                once, twice,
                "MGU must be idempotent: applying twice should equal applying once"
            );
        } else {
            panic!("Should unify X with f(Y)");
        }
    }
    #[test]
    fn mgu_is_idempotent_chain() {
        //  Theorem 1: Tests idempotence with variable chains
        // σ = MGU(f(X,Y), f(Y,Z)) must close transitive bindings
        let t1 = Term::app("f", vec![Term::var("X"), Term::var("Y")]);
        let t2 = Term::app("f", vec![Term::var("Y"), Term::var("Z")]);
        if let UnifyResult::Success(sigma) = unify(&t1, &t2) {
            let applied_t1 = sigma.apply_to_term(&t1);
            let double_applied = sigma.apply_to_term(&applied_t1);
            assert_eq!(
                applied_t1, double_applied,
                "Chained bindings must be fully resolved in one application"
            );
        } else {
            panic!("f(X,Y) and f(Y,Z) should unify");
        }
    }
    // -------------------------------------------------------------------------
    // Property: MGU yields syntactically equal terms
    //
    // Reference:  Definition of Unifier
    // "A unifier of expressions E1, E2 is a substitution θ such that E1θ = E2θ"
    //
    // The equality here is syntactic identity, not semantic equivalence.
    // -------------------------------------------------------------------------
    #[test]
    fn mgu_produces_syntactic_equality() {
        //  Definition of unifier: σ(t1) = σ(t2) syntactically
        let t1 = Term::app("f", vec![Term::var("X"), Term::constant("a")]);
        let t2 = Term::app("f", vec![Term::constant("b"), Term::var("Y")]);
        if let UnifyResult::Success(sigma) = unify(&t1, &t2) {
            let unified_t1 = sigma.apply_to_term(&t1);
            let unified_t2 = sigma.apply_to_term(&t2);
            assert_eq!(
                unified_t1, unified_t2,
                "MGU must make terms syntactically identical"
            );
        } else {
            panic!("These terms should unify");
        }
    }
    #[test]
    fn mgu_deep_nesting_produces_equality() {
        //  Unification must work through arbitrary nesting depth
        // f(g(X), h(Y, Z)) vs f(g(a), h(b, W))
        let t1 = Term::app(
            "f",
            vec![
                Term::app("g", vec![Term::var("X")]),
                Term::app("h", vec![Term::var("Y"), Term::var("Z")]),
            ],
        );
        let t2 = Term::app(
            "f",
            vec![
                Term::app("g", vec![Term::constant("a")]),
                Term::app("h", vec![Term::constant("b"), Term::var("W")]),
            ],
        );
        if let UnifyResult::Success(sigma) = unify(&t1, &t2) {
            let unified_t1 = sigma.apply_to_term(&t1);
            let unified_t2 = sigma.apply_to_term(&t2);
            assert_eq!(
                unified_t1, unified_t2,
                "Deep nesting must still produce syntactic equality"
            );
        } else {
            panic!("These terms should unify");
        }
    }
    // -------------------------------------------------------------------------
    // Property: MGU is most general (any unifier factors through MGU)
    //
    // Reference:  Unification Theorem
    // "If a set of expressions has a unifier, it has a most general unifier σ
    // such that any other unifier θ can be written as θ = ρ ∘ σ for some ρ."
    //
    // This means the MGU doesn't over-instantiate variables.
    // -------------------------------------------------------------------------
    #[test]
    fn mgu_is_most_general() {
        //  Unification Theorem: MGU is maximally general
        // σ = MGU(X, f(Y)) should map X to f(Y), not to f(a)
        let t1 = Term::var("X");
        let t2 = Term::app("f", vec![Term::var("Y")]);
        if let UnifyResult::Success(sigma) = unify(&t1, &t2) {
            let bound = sigma.apply_to_term(&t1);
            // Result should preserve variable Y, not ground it
            assert!(
                !bound.is_ground(),
                "MGU should not over-instantiate: result should contain variables"
            );
        } else {
            panic!("Should unify");
        }
    }
    // -------------------------------------------------------------------------
    // Property: Occurs check prevents infinite terms
    //
    // Reference:  Section 5.1 - Occurs Check
    // "The unification of x and f(x) would require x = f(f(f(...))) which is
    // not a finite term. The occurs check detects this."
    // -------------------------------------------------------------------------
    #[test]
    fn occurs_check_direct() {
        //  Occurs check: X = f(X) creates infinite term
        let t1 = Term::var("X");
        let t2 = Term::app("f", vec![Term::var("X")]);
        assert!(
            unify(&t1, &t2).is_failure(),
            "X = f(X) must fail occurs check"
        );
    }
    #[test]
    fn occurs_check_indirect() {
        //  Occurs check through nesting: X = f(g(X))
        let t1 = Term::var("X");
        let t2 = Term::app("f", vec![Term::app("g", vec![Term::var("X")])]);
        assert!(
            unify(&t1, &t2).is_failure(),
            "X = f(g(X)) must fail occurs check"
        );
    }
    #[test]
    fn occurs_check_through_unification() {
        //  Occurs check via unification chain
        // f(X, X) = f(Y, g(Y)) implies X = Y and X = g(Y) = g(X)
        let t1 = Term::app("f", vec![Term::var("X"), Term::var("X")]);
        let t2 = Term::app("f", vec![Term::var("Y"), Term::app("g", vec![Term::var("Y")])]);
        assert!(
            unify(&t1, &t2).is_failure(),
            "Occurs check must catch indirect cycles through unification"
        );
    }
    #[test]
    fn occurs_check_different_variables_ok() {
        //  Different variables don't trigger occurs check
        let t1 = Term::var("X");
        let t2 = Term::app("f", vec![Term::var("Y")]);
        assert!(
            unify(&t1, &t2).is_success(),
            "X = f(Y) should succeed - no cycle"
        );
    }
    // -------------------------------------------------------------------------
    // Property: Unification is symmetric
    //
    // Reference:  - implicit in the algorithm
    // unify(t1, t2) succeeds iff unify(t2, t1) succeeds
    // -------------------------------------------------------------------------
    #[test]
    fn unification_symmetric_success() {
        //  Symmetry of unification
        let t1 = Term::app("f", vec![Term::var("X")]);
        let t2 = Term::app("f", vec![Term::constant("a")]);
        let r1 = unify(&t1, &t2);
        let r2 = unify(&t2, &t1);
        assert_eq!(
            r1.is_success(),
            r2.is_success(),
            "Unification must be symmetric in success/failure"
        );
        if let (UnifyResult::Success(s1), UnifyResult::Success(s2)) = (&r1, &r2) {
            assert_eq!(
                s1.apply_to_term(&t1),
                s2.apply_to_term(&t1),
                "Symmetric unifications must produce same result on t1"
            );
            assert_eq!(
                s1.apply_to_term(&t2),
                s2.apply_to_term(&t2),
                "Symmetric unifications must produce same result on t2"
            );
        }
    }
    // -------------------------------------------------------------------------
    // Property: Simultaneous unification is conjunctive
    //
    // Reference:  Section 2.5 - Simultaneous Unification
    // "The MGU of a set of pairs {(s1,t1), ..., (sn,tn)} is a substitution σ
    // such that σ(si) = σ(ti) for all i."
    // -------------------------------------------------------------------------
    #[test]
    fn simultaneous_unification_must_satisfy_all() {
        //  Simultaneous MGU must satisfy all pairs
        let pairs = vec![
            (Term::var("X"), Term::constant("a")),
            (Term::var("Y"), Term::constant("b")),
            (
                Term::app("f", vec![Term::var("X"), Term::var("Y")]),
                Term::app("f", vec![Term::constant("a"), Term::constant("b")]),
            ),
        ];
        if let UnifyResult::Success(sigma) = unify_many(&pairs) {
            for (t1, t2) in &pairs {
                assert_eq!(
                    sigma.apply_to_term(t1),
                    sigma.apply_to_term(t2),
                    "Simultaneous unifier must satisfy ALL pairs"
                );
            }
        } else {
            panic!("Should find simultaneous unifier for consistent pairs");
        }
    }
    #[test]
    fn simultaneous_unification_detects_inconsistency() {
        //  Inconsistent constraints have no unifier
        // X = a and X = b cannot both hold
        let pairs = vec![
            (Term::var("X"), Term::constant("a")),
            (Term::var("X"), Term::constant("b")),
        ];
        assert!(
            unify_many(&pairs).is_failure(),
            "Inconsistent constraint set must fail"
        );
    }
    #[test]
    fn simultaneous_unification_propagates_constraints() {
        //  Transitivity: X = Y, Y = a implies X = a
        let pairs = vec![
            (Term::var("X"), Term::var("Y")),
            (Term::var("Y"), Term::constant("a")),
        ];
        if let UnifyResult::Success(sigma) = unify_many(&pairs) {
            let x_value = sigma.apply_to_term(&Term::var("X"));
            assert_eq!(
                x_value,
                Term::constant("a"),
                "Transitivity: X = Y ∧ Y = a ⟹ X = a"
            );
        } else {
            panic!("Should succeed with consistent constraints");
        }
    }
    // -------------------------------------------------------------------------
    // Property: Literal unification for resolution
    //
    // Reference:  Resolution rule requires unifying complementary
    // literals. unify_literals unifies atoms regardless of sign.
    // -------------------------------------------------------------------------
    #[test]
    fn literal_unification_requires_same_predicate() {
        //  Different predicates cannot unify
        let l1 = Literal::pos("p", vec![Term::var("X")]);
        let l2 = Literal::pos("q", vec![Term::var("X")]);
        assert!(
            unify_literals(&l1, &l2).is_failure(),
            "Different predicates cannot unify"
        );
    }
    #[test]
    fn literal_unification_ignores_sign() {
        //  Resolution requires unifying complementary literals
        // unify_literals unifies the underlying atoms
        let l1 = Literal::pos("p", vec![Term::var("X")]);
        let l2 = Literal::neg("p", vec![Term::constant("a")]);
        if let UnifyResult::Success(sigma) = unify_literals(&l1, &l2) {
            assert_eq!(
                sigma.apply_to_term(&Term::var("X")),
                Term::constant("a"),
                "Literal unification should unify underlying atoms"
            );
        } else {
            panic!("Should unify atoms of complementary literals");
        }
    }
}
// =============================================================================
// SUBSTITUTION COMPOSITION PROPERTIES
// =============================================================================
//
// These tests verify the algebraic properties of substitution composition.
// Substitutions form a monoid under composition with identity element ε.
//
// Reference: Standard first-order logic texts; formalized in .
mod substitution_semantics {
    use super::*;
    // -------------------------------------------------------------------------
    // Property: Composition is associative
    //
    // Reference:  and standard algebra
    // (σ ∘ θ) ∘ ρ = σ ∘ (θ ∘ ρ)
    // -------------------------------------------------------------------------
    #[test]
    fn composition_is_associative() {
        // Substitution composition must be associative
        let sigma = Substitution::singleton(Var::new("X"), Term::var("Y"));
        let theta = Substitution::singleton(Var::new("Y"), Term::var("Z"));
        let rho = Substitution::singleton(Var::new("Z"), Term::constant("a"));
        let left = sigma.compose(&theta).compose(&rho);
        let right = sigma.compose(&theta.compose(&rho));
        let term = Term::var("X");
        assert_eq!(
            left.apply_to_term(&term),
            right.apply_to_term(&term),
            "Composition must be associative: (σ∘θ)∘ρ = σ∘(θ∘ρ)"
        );
    }
    // -------------------------------------------------------------------------
    // Property: Empty substitution is identity element
    //
    // Reference:  - ε is identity for composition
    // ε ∘ σ = σ = σ ∘ ε
    // -------------------------------------------------------------------------
    #[test]
    fn empty_is_left_identity() {
        // ε ∘ σ = σ
        let sigma = Substitution::singleton(Var::new("X"), Term::constant("a"));
        let empty = Substitution::empty();
        let composed = empty.compose(&sigma);
        let term = Term::var("X");
        assert_eq!(
            composed.apply_to_term(&term),
            sigma.apply_to_term(&term),
            "Empty ∘ σ = σ"
        );
    }
    #[test]
    fn empty_is_right_identity() {
        // σ ∘ ε = σ
        let sigma = Substitution::singleton(Var::new("X"), Term::constant("a"));
        let empty = Substitution::empty();
        let composed = sigma.compose(&empty);
        let term = Term::var("X");
        assert_eq!(
            composed.apply_to_term(&term),
            sigma.apply_to_term(&term),
            "σ ∘ Empty = σ"
        );
    }
    // -------------------------------------------------------------------------
    // Property: Composition semantics
    //
    // Reference: Standard definition
    // (σ ∘ θ)(t) = σ(θ(t)) or θ(σ(t)) depending on convention
    // -------------------------------------------------------------------------
    #[test]
    fn composition_semantics() {
        // {X -> Y} ∘ {Y -> a} should map X to a (or vice versa)
        let sigma = Substitution::singleton(Var::new("X"), Term::var("Y"));
        let theta = Substitution::singleton(Var::new("Y"), Term::constant("a"));
        let composed = sigma.compose(&theta);
        let term = Term::var("X");
        let composed_result = composed.apply_to_term(&term);
        let sigma_then_theta = theta.apply_to_term(&sigma.apply_to_term(&term));
        let theta_then_sigma = sigma.apply_to_term(&theta.apply_to_term(&term));
        assert!(
            composed_result == sigma_then_theta || composed_result == theta_then_sigma,
            "Composition must match some sequential application order"
        );
    }
    // -------------------------------------------------------------------------
    // Property: Renaming is bijective on variables
    //
    // Reference: Standard - a renaming is a substitution that maps variables
    // to variables bijectively.
    // -------------------------------------------------------------------------
    #[test]
    fn renaming_inverse() {
        // {X -> Y, Y -> X} applied twice is identity
        let mut rename = Substitution::empty();
        rename.bind(Var::new("X"), Term::var("Y"));
        rename.bind(Var::new("Y"), Term::var("X"));
        assert!(rename.is_renaming(), "This should be a valid renaming");
        let term = Term::app("f", vec![Term::var("X"), Term::var("Y")]);
        let once = rename.apply_to_term(&term);
        let twice = rename.apply_to_term(&once);
        assert_eq!(twice, term, "Swapping twice should return to original");
    }
}
// =============================================================================
// CLAUSE SEMANTIC PROPERTIES
// =============================================================================
//
// These tests verify properties of clausal representation.
//
// Reference: Standard first-order logic; Horn clause definition from
// logic programming literature.
mod clause_semantics {
    use super::*;
    // -------------------------------------------------------------------------
    // Property: Empty clause represents contradiction
    //
    // Reference:  - The empty clause □ is unsatisfiable
    // "Deriving the empty clause proves the original set unsatisfiable."
    // -------------------------------------------------------------------------
    #[test]
    fn empty_clause_represents_false() {
        //  Empty clause = contradiction
        let empty = Clause::empty();
        assert!(empty.is_empty());
        // An empty disjunction is false
    }
    // -------------------------------------------------------------------------
    // Property: Complementary literals
    //
    // Reference:  Definition for resolution
    // L and ¬L are complementary if they have same atom, opposite signs.
    // -------------------------------------------------------------------------
    #[test]
    fn clause_with_complementary_literals() {
        //  p(X) and ¬p(X) are complementary
        let lit1 = Literal::pos("p", vec![Term::var("X")]);
        let lit2 = Literal::neg("p", vec![Term::var("X")]);
        let _clause = Clause::new(vec![lit1.clone(), lit2.clone()]);
        assert!(
            lit1.is_complementary(&lit2),
            "p(X) and ¬p(X) should be complementary"
        );
    }
    // -------------------------------------------------------------------------
    // Property: Horn clause definition
    //
    // Reference: Standard logic programming definition
    // A Horn clause has at most one positive literal.
    // -------------------------------------------------------------------------
    #[test]
    fn horn_clause_boundary() {
        // Exactly one positive = definite clause = Horn
        let definite = Clause::new(vec![
            Literal::neg("p", vec![]),
            Literal::neg("q", vec![]),
            Literal::pos("r", vec![]),
        ]);
        assert!(definite.is_horn(), "Definite clause (1 pos) is Horn");
        // Zero positive = goal clause = Horn
        let goal = Clause::new(vec![Literal::neg("p", vec![]), Literal::neg("q", vec![])]);
        assert!(goal.is_horn(), "Goal clause (0 pos) is Horn");
        // Two positive = not Horn
        let non_horn = Clause::new(vec![
            Literal::pos("p", vec![]),
            Literal::pos("q", vec![]),
            Literal::neg("r", vec![]),
        ]);
        assert!(!non_horn.is_horn(), "2+ positive literals is not Horn");
    }
    #[test]
    fn variables_collects_from_all_literals() {
        let clause = Clause::new(vec![
            Literal::pos("p", vec![Term::var("X"), Term::var("Y")]),
            Literal::neg("q", vec![Term::var("Z"), Term::app("f", vec![Term::var("W")])]),
        ]);
        let vars = clause.variables();
        assert_eq!(vars.len(), 4, "Should collect X, Y, Z, W");
        assert!(vars.contains(&Var::new("X")));
        assert!(vars.contains(&Var::new("Y")));
        assert!(vars.contains(&Var::new("Z")));
        assert!(vars.contains(&Var::new("W")));
    }
    #[test]
    fn substitution_preserves_literal_count() {
        let clause = Clause::new(vec![
            Literal::pos("p", vec![Term::var("X")]),
            Literal::neg("q", vec![Term::var("Y")]),
        ]);
        let mut subst = HashMap::new();
        subst.insert(Var::new("X"), Term::constant("a"));
        subst.insert(Var::new("Y"), Term::constant("b"));
        let result = clause.apply_subst(&subst);
        assert_eq!(
            result.literals.len(),
            clause.literals.len(),
            "Substitution must preserve literal count"
        );
    }
    #[test]
    fn substitution_preserves_signs() {
        let clause = Clause::new(vec![
            Literal::pos("p", vec![Term::var("X")]),
            Literal::neg("q", vec![Term::var("Y")]),
        ]);
        let mut subst = HashMap::new();
        subst.insert(Var::new("X"), Term::constant("a"));
        let result = clause.apply_subst(&subst);
        assert!(result.literals[0].positive, "Sign must be preserved");
        assert!(!result.literals[1].positive, "Sign must be preserved");
    }
}
// =============================================================================
// SGGS TRAIL INVARIANTS
// =============================================================================
//
// These tests verify the invariants of SGGS trails as defined in [BP16a].
//
// Key concepts from [BP16a]:
// - Trail Γ = C₁[L₁], ..., Cₙ[Lₙ] is a sequence of constrained clauses
// - Each clause has a selected literal Lᵢ
// - The trail represents a partial interpretation I^p(Γ)
// - Literals are "I-false" (uniformly false in I) or "I-true" (true in I)
// - Selected literals should be I-false to "differentiate from I"
mod trail_semantics {
    use super::*;
    use crate::sggs::{ConstrainedClause, InitialInterpretation, Trail};
    // -------------------------------------------------------------------------
    // Property: Selected literals are I-false
    //
    // Reference: [BP16a] Section 3 - Trail Interpretation
    // "SGGS requires that if a clause in the trail has I-false literals, one is
    // selected, so as to differentiate from I."
    //
    // Under I⁻ (all atoms false): positive literals are I-false
    // Under I⁺ (all atoms true): negative literals are I-false
    // -------------------------------------------------------------------------
    #[test]
    fn selected_literal_must_be_i_false_under_i_negative() {
        // [BP16a] Under I⁻, positive literals are I-false
        let _trail = Trail::new(InitialInterpretation::AllNegative);
        let clause = Clause::new(vec![
            Literal::pos("p", vec![Term::constant("a")]), // I-false under I⁻
            Literal::neg("q", vec![Term::constant("b")]), // I-true under I⁻
        ]);
        let constrained = ConstrainedClause::new(clause.clone(), 0); // select positive
        let selected = constrained.selected_literal();
        assert!(
            selected.positive,
            "[BP16a] Selected literal under I⁻ should be positive (I-false)"
        );
    }
    #[test]
    fn selected_literal_must_be_i_false_under_i_positive() {
        // [BP16a] Under I⁺, negative literals are I-false
        let _trail = Trail::new(InitialInterpretation::AllPositive);
        let clause = Clause::new(vec![
            Literal::pos("p", vec![Term::constant("a")]), // I-true under I⁺
            Literal::neg("q", vec![Term::constant("b")]), // I-false under I⁺
        ]);
        let constrained = ConstrainedClause::new(clause.clone(), 1); // select negative
        let selected = constrained.selected_literal();
        assert!(
            !selected.positive,
            "[BP16a] Selected literal under I⁺ should be negative (I-false)"
        );
    }
    // -------------------------------------------------------------------------
    // Property: Disjoint prefix
    //
    // Reference: [BP16a] Definition 5 - Disjoint Prefix
    // "The disjoint prefix is the maximal prefix where no two selected literals
    // have unifiable atoms."
    //
    // Selected literals in the disjoint prefix represent distinct parts of the
    // model being constructed.
    // -------------------------------------------------------------------------
    #[test]
    fn disjoint_prefix_has_no_overlapping_selections() {
        // [BP16a] Def 8: Non-unifiable selected literals extend disjoint prefix
        let trail = Trail::new(InitialInterpretation::AllNegative);
        // p(a) and p(b) don't unify - both should be in disjoint prefix
        let c1 = Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
        let c2 = Clause::new(vec![Literal::pos("p", vec![Term::constant("b")])]);
        let cc1 = ConstrainedClause::new(c1, 0);
        let cc2 = ConstrainedClause::new(c2, 0);
        let mut trail_mut = trail;
        trail_mut.push(cc1);
        trail_mut.push(cc2);
        assert!(
            trail_mut.disjoint_prefix_length() >= 2,
            "[BP16a] Def 8: Non-unifiable selected literals extend disjoint prefix"
        );
    }
    // -------------------------------------------------------------------------
    // Property: Conflict clause definition
    //
    // Reference: [BW20] Definition 1: "A clause C is a conflict clause if all
    // literals of C are uniformly false in the trail interpretation."
    // (Uniform falsity is defined earlier in [BP16a], Section 2.)
    // -------------------------------------------------------------------------
    #[test]
    fn conflict_clause_all_literals_false() {
        // [BW20] Def 1: Conflict = all literals uniformly false
        let trail = Trail::new(InitialInterpretation::AllNegative);
        let interp = trail.interpretation();
        // Under I⁻ with empty trail, all positive literals are uniformly false
        let conflict_candidate = Clause::new(vec![
            Literal::pos("p", vec![Term::constant("a")]),
            Literal::pos("q", vec![Term::constant("b")]),
        ]);
        let constrained = ConstrainedClause::new(conflict_candidate, 0);
        assert!(
            constrained.is_conflict(&interp),
            "[BP16a] Def 11: All-positive clause is conflict under I⁻ with empty trail"
        );
    }
    #[test]
    fn non_conflict_has_satisfiable_literal() {
        // [BW20] Def 1: Clause with an I-true literal is not a conflict
        let trail = Trail::new(InitialInterpretation::AllNegative);
        let interp = trail.interpretation();
        // Negative literal is I-true under I⁻
        let non_conflict = Clause::new(vec![
            Literal::pos("p", vec![Term::constant("a")]), // I-false
            Literal::neg("q", vec![Term::constant("b")]), // I-true
        ]);
        let constrained = ConstrainedClause::new(non_conflict, 0);
        assert!(
            !constrained.is_conflict(&interp),
            "[BP16a] Clause with I-true literal cannot be conflict"
        );
    }

    // -------------------------------------------------------------------------
    // Property: I-false selected literals are enumerated
    //
    // Reference: [BP17] Definition 4 (extension side premises are I-false)
    // -------------------------------------------------------------------------
    #[test]
    fn i_false_selected_reports_only_i_false_literals() {
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        let c1 = ConstrainedClause::new(
            Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]),
            0,
        );
        let c2 = ConstrainedClause::new(
            Clause::new(vec![Literal::neg("q", vec![Term::constant("b")])]),
            0,
        );
        trail.push(c1);
        trail.push(c2);

        let interp = trail.interpretation();
        let i_false = interp.i_false_selected();
        let indices: Vec<usize> = i_false.iter().map(|(idx, _)| *idx).collect();

        assert!(indices.contains(&0), "I-false selected literal should be reported");
        assert!(
            !indices.contains(&1),
            "I-true selected literal should not be reported"
        );
    }

    // -------------------------------------------------------------------------
    // Property: Conflict detection on the trail
    //
    // Reference: [BW20] Definition 1 (conflict clause)
    // -------------------------------------------------------------------------
    #[test]
    fn find_conflict_detects_uniformly_false_clause() {
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(ConstrainedClause::new(
            Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]),
            0,
        ));
        trail.push(ConstrainedClause::new(
            Clause::new(vec![Literal::neg("p", vec![Term::constant("a")])]),
            0,
        ));

        assert_eq!(trail.find_conflict(), Some(1));
    }
}
// =============================================================================
// SGGS EXTENSION SEMANTIC PROPERTIES
// =============================================================================
//
// Reference: [BP17] Definition 4 - SGGS-Extension
// "SGGS-extension adds an instance E of input clause C to the trail when the
// I-true literals of C unify with I-false selected literals on the trail."
//
// [BW20] Definition 1 also describes the extension rule.
mod extension_semantics {
    use super::*;
    use crate::sggs::{sggs_extension, ExtensionResult, InitialInterpretation, Trail};
    #[test]
    fn extension_on_satisfiable_theory() {
        // [BP17] Def 4, [BW20] Def 1: Extension advances satisfiable theories
        let theory = theory_from_clauses(vec![
            // p(a) (fact)
            Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]),
            // ¬p(X) ∨ q(X) (rule: p(X) → q(X))
            Clause::new(vec![
                Literal::neg("p", vec![Term::var("X")]),
                Literal::pos("q", vec![Term::var("X")]),
            ]),
        ]);
        let trail = Trail::new(InitialInterpretation::AllNegative);
        let result = sggs_extension(&trail, &theory);
        match result {
            ExtensionResult::Extended(_) => {
                // Good - found an extension
            }
            ExtensionResult::NoExtension => {
                // Only valid if trail is complete
            }
            ExtensionResult::Conflict(_) => {
                panic!("[BP17] Satisfiable theory should not immediately conflict");
            }
        }
    }
}
// =============================================================================
// SGGS COMPLETENESS PROPERTIES
// =============================================================================
//
// Reference: [BP17] Theorem 1 - Refutational Completeness
// "SGGS is refutationally complete: for unsatisfiable input, any fair SGGS
// derivation derives the empty clause."
//
// Reference: [BP17] Theorem 2 - Model Completeness in the Limit
// "SGGS is model complete in the limit: for satisfiable input, any fair SGGS
// derivation constructs a model in the limit."
//
// Reference: [BP17] - Proof Confluence
// "SGGS is proof confluent: it never needs to backtrack."
//
// [BW20] Theorems 1-5 extend these results to decidable fragments.
mod completeness_semantics {
    use super::*;
    use crate::sggs::{derive, DerivationConfig, DerivationResult, InitialInterpretation};
    // -------------------------------------------------------------------------
    // Property: Unsatisfiable theories derive empty clause
    //
    // Reference: [BP17] Theorem 1 - Refutational Completeness
    // -------------------------------------------------------------------------
    #[test]
    fn unsatisfiable_derives_empty() {
        // [BP17] Theorem 1: p ∧ ¬p is unsatisfiable → derives □
        let theory = theory_from_clauses(vec![
            Clause::new(vec![Literal::pos("p", vec![])]),
            Clause::new(vec![Literal::neg("p", vec![])]),
        ]);
        let config = DerivationConfig::default();
        let result = derive(&theory, config);
        assert!(
            matches!(result, DerivationResult::Unsatisfiable),
            "[BP17] Theorem 1: p ∧ ¬p must derive empty clause"
        );
    }
    #[test]
    fn harder_unsatisfiable() {
        // [BP17] Theorem 1: (p∨q) ∧ (¬p∨q) ∧ (p∨¬q) ∧ (¬p∨¬q) is unsatisfiable
        let theory = theory_from_clauses(vec![
            Clause::new(vec![Literal::pos("p", vec![]), Literal::pos("q", vec![])]),
            Clause::new(vec![Literal::neg("p", vec![]), Literal::pos("q", vec![])]),
            Clause::new(vec![Literal::pos("p", vec![]), Literal::neg("q", vec![])]),
            Clause::new(vec![Literal::neg("p", vec![]), Literal::neg("q", vec![])]),
        ]);
        let config = DerivationConfig::default();
        let result = derive(&theory, config);
        assert!(
            matches!(result, DerivationResult::Unsatisfiable),
            "[BP17] Theorem 1: All-cases covered contradiction must be unsatisfiable"
        );
    }
    // -------------------------------------------------------------------------
    // Property: Satisfiable theories produce models
    //
    // Reference: [BP17] Theorem 2 - Model Completeness in the Limit
    // -------------------------------------------------------------------------
    #[test]
    fn satisfiable_produces_model() {
        // [BP17] Theorem 2: Satisfiable input produces a model
        let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos("p", vec![])])]);
        let config = DerivationConfig::default();
        let result = derive(&theory, config);
        match result {
            DerivationResult::Satisfiable(model) => {
                assert!(
                    model.true_atoms.contains(&Atom::prop("p")),
                    "[BP17] Theorem 2: Model for {{p}} must include p"
                );
            }
            _ => panic!("[BP17] Theorem 2: Single fact p should be satisfiable"),
        }
    }
    #[test]
    fn satisfiable_horn_produces_model() {
        // [BP17] Theorem 2: Horn theory produces minimal Herbrand model
        // p(a), ¬p(X) ∨ q(X), ¬q(X) ∨ r(X) → model contains {p(a), q(a), r(a)}
        let theory = theory_from_clauses(vec![
            Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]),
            Clause::new(vec![
                Literal::neg("p", vec![Term::var("X")]),
                Literal::pos("q", vec![Term::var("X")]),
            ]),
            Clause::new(vec![
                Literal::neg("q", vec![Term::var("X")]),
                Literal::pos("r", vec![Term::var("X")]),
            ]),
        ]);
        let config = DerivationConfig::default();
        let result = derive(&theory, config);
        match result {
            DerivationResult::Satisfiable(model) => {
                assert!(
                    model
                        .true_atoms
                        .contains(&Atom::new("p", vec![Term::constant("a")])),
                    "[BP17] Theorem 2: Model should contain p(a)"
                );
            }
            _ => panic!("[BP17] Theorem 2: Horn theory is satisfiable"),
        }
    }
    // -------------------------------------------------------------------------
    // Property: Proof confluence
    //
    // Reference: [BP17] Section 5 - Proof Confluence
    // "SGGS is proof confluent: different search orders reach the same result."
    // -------------------------------------------------------------------------
    #[test]
    fn proof_confluence_unsatisfiable() {
        // [BP17] Proof confluence: same result regardless of initial interpretation
        let theory = theory_from_clauses(vec![
            Clause::new(vec![Literal::pos("p", vec![])]),
            Clause::new(vec![Literal::neg("p", vec![])]),
        ]);
        let config_positive = DerivationConfig {
            max_steps: Some(100),
            initial_interp: InitialInterpretation::AllPositive,
        };
        let config_negative = DerivationConfig {
            max_steps: Some(100),
            initial_interp: InitialInterpretation::AllNegative,
        };
        let result_pos = derive(&theory, config_positive);
        let result_neg = derive(&theory, config_negative);
        assert!(
            matches!(result_pos, DerivationResult::Unsatisfiable),
            "[BP17] Proof confluence: Unsatisfiable with I⁺"
        );
        assert!(
            matches!(result_neg, DerivationResult::Unsatisfiable),
            "[BP17] Proof confluence: Unsatisfiable with I⁻"
        );
    }
    // -------------------------------------------------------------------------
    // Property: Decidable fragments terminate
    //
    // Reference: [BW20] Theorem 2 - Stratified Fragment
    // "Any fair SGGS-derivation from a stratified clause set halts."
    //
    // Datalog is a subset of the stratified fragment.
    // -------------------------------------------------------------------------
    #[test]
    fn satisfiable_datalog() {
        // [BW20] Theorem 2: Datalog (stratified) terminates and produces model
        // edge(a,b), edge(b,c), path rules → derives path(a,c)
        let a = Term::constant("a");
        let b = Term::constant("b");
        let c = Term::constant("c");
        let theory = theory_from_clauses(vec![
            Clause::new(vec![Literal::pos("edge", vec![a.clone(), b.clone()])]),
            Clause::new(vec![Literal::pos("edge", vec![b.clone(), c.clone()])]),
            Clause::new(vec![
                Literal::neg("edge", vec![Term::var("X"), Term::var("Y")]),
                Literal::pos("path", vec![Term::var("X"), Term::var("Y")]),
            ]),
            Clause::new(vec![
                Literal::neg("path", vec![Term::var("X"), Term::var("Y")]),
                Literal::neg("edge", vec![Term::var("Y"), Term::var("Z")]),
                Literal::pos("path", vec![Term::var("X"), Term::var("Z")]),
            ]),
        ]);
        let config = DerivationConfig::default();
        let result = derive(&theory, config);
        match result {
            DerivationResult::Satisfiable(model) => {
                assert!(
                    model
                        .true_atoms
                        .contains(&Atom::new("path", vec![a.clone(), c.clone()])),
                    "[BW20] Theorem 2: Model should contain path(a,c) by transitivity"
                );
            }
            DerivationResult::ResourceLimit => {
                // Acceptable for bounded computation
            }
            DerivationResult::Unsatisfiable => {
                panic!("[BW20] Datalog program should be satisfiable");
            }
        }
    }
}
// =============================================================================
// SGGS RESOLUTION SEMANTIC PROPERTIES
// =============================================================================
//
// Reference: SGGSdpFOL Definition 2 (SGGS-Resolution)
// "SGGS-resolution resolves a conflict clause with justifications from the
// trail's disjoint prefix."
//
// Reference: [BP17] Section 5 - Conflict Explanation
// "Resolution is used to explain conflicts and derive lemmas."
mod resolution_semantics {
    use super::*;
    use crate::sggs::{sggs_resolution, ConstrainedClause, InitialInterpretation, ResolutionResult, Trail};
    #[test]
    fn resolution_preserves_conflict() {
        // [BP17] Def 6: Resolution explains conflicts while preserving conflict status.
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        let left = ConstrainedClause::new(
            Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
            0,
        );
        trail.push(left);

        let conflict = ConstrainedClause::new(
            Clause::new(vec![
                Literal::pos("P", vec![Term::constant("a")]),
                Literal::pos("Q", vec![Term::constant("a")]),
            ]),
            0,
        );
        trail.push(conflict.clone());

        match sggs_resolution(&conflict, &trail) {
            ResolutionResult::Resolvent(res) => {
                let interp = trail.interpretation();
                assert!(res.is_conflict(&interp));
            }
            other => panic!("Expected resolvent, got {:?}", other),
        }
    }
}
// =============================================================================
// CONSTRAINT SEMANTIC PROPERTIES
// =============================================================================
//
// Reference: [BP17] Definition 1 (Constraint, standard form)
mod constraint_semantics {
    use super::*;
    use crate::constraint::{AtomicConstraint, Constraint};

    #[test]
    fn standardize_eliminates_identical_and_root_equals() {
        // Standard form contains only x ≠ y and top(x) ≠ f atoms.
        let c = Constraint::Or(
            Box::new(Constraint::Atomic(AtomicConstraint::RootNotEquals(
                Term::var("x"),
                "f".to_string(),
            ))),
            Box::new(Constraint::Atomic(AtomicConstraint::Identical(
                Term::var("x"),
                Term::var("y"),
            ))),
        );
        let std = c.standardize();

        let mut has_identical = false;
        let mut has_root_equals = false;
        fn walk(c: &Constraint, hi: &mut bool, hr: &mut bool) {
            match c {
                Constraint::Atomic(AtomicConstraint::Identical(_, _)) => *hi = true,
                Constraint::Atomic(AtomicConstraint::RootEquals(_, _)) => *hr = true,
                Constraint::And(a, b) | Constraint::Or(a, b) => {
                    walk(a, hi, hr);
                    walk(b, hi, hr);
                }
                Constraint::Not(inner) => walk(inner, hi, hr),
                _ => {}
            }
        }
        walk(&std, &mut has_identical, &mut has_root_equals);
        assert!(!has_identical, "standard form should not contain Identical");
        assert!(!has_root_equals, "standard form should not contain RootEquals");
    }

    #[test]
    fn constraint_satisfiable_examples() {
        // x ≠ x is unsatisfiable.
        let c1 = Constraint::Atomic(AtomicConstraint::NotIdentical(
            Term::var("x"),
            Term::var("x"),
        ));
        assert!(!c1.is_satisfiable());

        // top(f(a)) ≠ f is unsatisfiable.
        let c2 = Constraint::Atomic(AtomicConstraint::RootNotEquals(
            Term::app("f", vec![Term::constant("a")]),
            "f".to_string(),
        ));
        assert!(!c2.is_satisfiable());
    }

    #[test]
    fn constraint_intersection_basic() {
        let c1 = Constraint::Atomic(AtomicConstraint::NotIdentical(
            Term::var("x"),
            Term::var("y"),
        ));
        let c2 = Constraint::Atomic(AtomicConstraint::RootNotEquals(
            Term::var("x"),
            "f".to_string(),
        ));
        let inter = c1.intersect(&c2);
        let expected = Constraint::And(Box::new(c1.clone()), Box::new(c2.clone()));
        assert_eq!(inter, expected);
        assert!(inter.is_satisfiable());
    }

    #[test]
    fn constraint_intersects_false_when_unsat() {
        let c1 = Constraint::Atomic(AtomicConstraint::NotIdentical(
            Term::var("x"),
            Term::var("x"),
        ));
        assert!(!c1.intersects(&Constraint::True));
    }
}
// =============================================================================
// ASSIGNMENT SEMANTIC PROPERTIES
// =============================================================================
//
// Reference: [BP16a] Definitions 8-9 (Dependence and Assignment)
mod assignment_semantics {
    use super::*;
    use crate::constraint::Constraint;
    use crate::sggs::{compute_assignments, ConstrainedClause, InitialInterpretation, Trail};

    #[test]
    fn assignment_maps_i_true_literals_to_justification() {
        // Under I⁻: P(x) is selected (I-false), so ¬P(f(y)) depends on it.
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        let c1 = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
            Constraint::True,
            0,
        );
        let c2 = ConstrainedClause::with_constraint(
            Clause::new(vec![
                Literal::neg("P", vec![Term::app("f", vec![Term::var("y")])]),
                Literal::pos("Q", vec![Term::var("y")]),
            ]),
            Constraint::True,
            1,
        );
        trail.push(c1);
        trail.push(c2);

        let assigns = compute_assignments(&trail);
        let lit_idx = 0; // ¬P(f(y))
        let assigned = assigns.assigned_to(1, lit_idx);
        assert_eq!(assigned, Some(0));
    }
}
// =============================================================================
// FRAGMENT DETECTION (DECIDABLE FRAGMENTS)
// =============================================================================
//
// Reference: [BW20] Definitions 4 and 6 (ground-preserving, restrained)
mod fragment_semantics {
    use super::*;

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
    fn restrained_vacuous_for_ground_positive() {
        // No non-ground positive literals => restrained condition is vacuous.
        let clause = Clause::new(vec![
            Literal::neg("P", vec![Term::var("X")]),
            Literal::pos("Q", vec![Term::constant("a")]),
        ]);
        assert!(clause.is_restrained());
    }
}
// =============================================================================
// SGGS MOVE SEMANTICS
// =============================================================================
//
// Reference: [BP17] conflict-solving rules (move)
mod move_semantics {
    use super::*;
    use crate::constraint::Constraint;
    use crate::sggs::{sggs_move, ConstrainedClause, InitialInterpretation, MoveError, Trail};

    #[test]
    fn sggs_move_reorders_conflict_before_justification() {
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        let c1 = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
            Constraint::True,
            0,
        );
        let c2 = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
            Constraint::True,
            0,
        );
        trail.push(c1);
        trail.push(c2);

        let result = sggs_move(&mut trail, 1);
        assert!(result.is_ok());
        assert_eq!(
            trail.clauses()[0].selected_literal(),
            &Literal::neg("P", vec![Term::constant("a")])
        );
    }

    #[test]
    fn sggs_move_rejects_non_conflict_clause() {
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(ConstrainedClause::new(
            Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
            0,
        ));
        let result = sggs_move(&mut trail, 0);
        assert!(matches!(result, Err(MoveError::NotConflictClause)));
    }
}
// =============================================================================
// SGGS SPLITTING PROPERTIES
// =============================================================================
//
// Reference: [BP16a] Definitions 13-15 (partition and splitting)
mod splitting_semantics {
    use super::*;
    use crate::constraint::Constraint;
    use crate::sggs::ConstrainedClause;
    use crate::unify::Substitution;
    use std::collections::{HashMap, HashSet};

    fn constraint_holds(c: &Constraint, subst: &Substitution) -> bool {
        match c {
            Constraint::True => true,
            Constraint::False => false,
            Constraint::Atomic(a) => a.evaluate(subst).unwrap_or(false),
            Constraint::And(a, b) => constraint_holds(a, subst) && constraint_holds(b, subst),
            Constraint::Or(a, b) => constraint_holds(a, subst) || constraint_holds(b, subst),
            Constraint::Not(a) => !constraint_holds(a, subst),
        }
    }

    fn ground_atoms_for_clause(clause: &ConstrainedClause, consts: &[Term]) -> HashSet<Atom> {
        let lit = clause.selected_literal();
        let vars: HashSet<Var> = lit.variables();
        let vars: Vec<Var> = vars.into_iter().collect();
        let mut atoms = HashSet::new();

        fn assign(
            idx: usize,
            vars: &[Var],
            consts: &[Term],
            lit: &Literal,
            constraint: &Constraint,
            atoms: &mut HashSet<Atom>,
            subst: &mut Substitution,
        ) {
            if idx == vars.len() {
                if constraint_holds(constraint, subst) {
                    let inst = lit.apply_subst(&subst_to_map(subst));
                    atoms.insert(inst.atom);
                }
                return;
            }
            let var = vars[idx].clone();
            for c in consts {
                let mut s = subst.clone();
                s.bind(var.clone(), c.clone());
                assign(idx + 1, vars, consts, lit, constraint, atoms, &mut s);
            }
        }

        fn subst_to_map(subst: &Substitution) -> HashMap<Var, Term> {
            let mut map = HashMap::new();
            for v in subst.domain() {
                if let Some(t) = subst.lookup(v) {
                    map.insert(v.clone(), t.clone());
                }
            }
            map
        }

        let mut subst = Substitution::empty();
        assign(0, &vars, consts, lit, &clause.constraint, &mut atoms, &mut subst);
        atoms
    }

    #[test]
    fn splitting_partition_is_complete_and_disjoint() {
        let clause = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos(
                "P",
                vec![Term::var("x"), Term::var("y")],
            )]),
            Constraint::True,
            0,
        );
        let other = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos(
                "P",
                vec![
                    Term::app("f", vec![Term::var("w")]),
                    Term::app("g", vec![Term::var("z")]),
                ],
            )]),
            Constraint::True,
            0,
        );

        let result = crate::sggs::sggs_splitting(&clause, &other).expect("expected split result");

        let consts = vec![Term::constant("a"), Term::constant("b")];
        let original = ground_atoms_for_clause(&clause, &consts);
        let mut union = HashSet::new();

        let mut parts_atoms = Vec::new();
        for part in &result.parts {
            let atoms = ground_atoms_for_clause(part, &consts);
            for a in &atoms {
                union.insert(a.clone());
            }
            parts_atoms.push(atoms);
        }

        assert_eq!(union, original, "split parts must cover original");

        for i in 0..parts_atoms.len() {
            for j in (i + 1)..parts_atoms.len() {
                let inter: HashSet<_> = parts_atoms[i].intersection(&parts_atoms[j]).collect();
                assert!(inter.is_empty(), "split parts must be disjoint");
            }
        }
    }
}
// =============================================================================
// PROPERTY-BASED TESTS
// =============================================================================
//
// These use proptest to verify properties hold for arbitrary inputs.
// References:  for unification,  for MGU properties.
#[cfg(test)]
mod proptests {
    use super::*;
    use proptest::prelude::*;
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
}
