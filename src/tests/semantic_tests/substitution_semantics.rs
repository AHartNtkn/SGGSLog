use super::*;

// =============================================================================
// SUBSTITUTION COMPOSITION PROPERTIES
// =============================================================================
//
// These tests verify the algebraic properties of substitution composition.
// Substitutions form a monoid under composition with identity element ε.
//
// Reference: Standard first-order logic texts; formalized in .

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
