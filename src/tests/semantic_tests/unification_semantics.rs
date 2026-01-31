use super::*;

// =============================================================================
// UNIFICATION SEMANTIC PROPERTIES
// =============================================================================
//
// These tests verify standard properties of first-order unification.
// The MGU (Most General Unifier) must satisfy standard algebraic properties.

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
    let t2 = Term::app(
        "f",
        vec![Term::var("Y"), Term::app("g", vec![Term::var("Y")])],
    );
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
// Property: Sorts are preserved by unification
// -------------------------------------------------------------------------
#[test]
fn unification_rejects_sort_mismatch_var_const() {
    let x = Term::Var(Var::new_with_sort("X", "s1"));
    let a = Term::app_with_sort("a", "s2", vec![]);
    assert!(
        unify(&x, &a).is_failure(),
        "Sort mismatch should fail unification"
    );
}

#[test]
fn unification_accepts_sort_match_var_const() {
    let x = Term::Var(Var::new_with_sort("X", "s1"));
    let a = Term::app_with_sort("a", "s1", vec![]);
    assert!(
        unify(&x, &a).is_success(),
        "Matching sorts should allow unification"
    );
}

#[test]
fn unification_rejects_result_sort_mismatch() {
    let t1 = Term::app_with_sort("f", "s1", vec![Term::constant("a")]);
    let t2 = Term::app_with_sort("f", "s2", vec![Term::constant("a")]);
    assert!(
        unify(&t1, &t2).is_failure(),
        "Function result sort mismatch should fail unification"
    );
}

// -------------------------------------------------------------------------
// Property: Symbol clash / arity mismatch reject unification
// -------------------------------------------------------------------------
#[test]
fn unification_symbol_clash_fails() {
    let t1 = Term::app("f", vec![Term::var("X")]);
    let t2 = Term::app("g", vec![Term::var("X")]);
    assert!(
        unify(&t1, &t2).is_failure(),
        "Different function symbols must not unify"
    );
}

#[test]
fn unification_arity_mismatch_fails() {
    let t1 = Term::app("f", vec![Term::var("X")]);
    let t2 = Term::app("f", vec![Term::var("X"), Term::var("Y")]);
    assert!(
        unify(&t1, &t2).is_failure(),
        "Same symbol with different arity must not unify"
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

#[test]
fn literal_unification_arity_mismatch_fails() {
    let l1 = Literal::pos("p", vec![Term::var("X")]);
    let l2 = Literal::pos("p", vec![Term::var("X"), Term::var("Y")]);
    assert!(
        unify_literals(&l1, &l2).is_failure(),
        "Same predicate with different arity must not unify"
    );
}
