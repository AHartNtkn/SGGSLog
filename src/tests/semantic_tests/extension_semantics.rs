use super::*;

// =============================================================================
// SGGS EXTENSION SEMANTIC PROPERTIES
// =============================================================================
//
// Reference: [BP17] Definition 4 - SGGS-Extension
// "SGGS-extension adds an instance E of input clause C to the trail when the
// I-true literals of C unify with I-false selected literals on the trail."
//
// [BW20] Definition 1 also describes the extension rule.
use crate::sggs::{
    sggs_extension, ConstrainedClause, ExtensionResult, InitialInterpretation, Trail,
};
use crate::unify::{unify_literals, UnifyResult};

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
        ExtensionResult::Critical { .. } => {
            // Critical extension is also a valid extension step.
        }
    }
}

#[test]
fn extension_returns_no_extension_when_complete() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos(
        "p",
        vec![Term::constant("a")],
    )])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::NoExtension => {}
        other => panic!("Expected NoExtension on complete trail, got {:?}", other),
    }
}

#[test]
fn extension_does_not_extend_when_clause_already_satisfied() {
    // SGGS-extension applies only if I[Γ] ⊭ S and Γ = dp(Γ).
    // If the current trail already makes a clause true, extension must not re-add it.
    // Source: "On SGGS and Horn Clauses" (paper6), progress condition:
    // "If ⊥ ∉ Γ and I[Γ] ⊭ S ... SGGS applies SGGS-extension ..."
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    // Selected p makes clause (p ∨ q) true in I[Γ].
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("p", vec![])]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![
        Literal::pos("p", vec![]),
        Literal::pos("q", vec![]),
    ])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::NoExtension => {}
        other => panic!(
            "Expected NoExtension when clause already satisfied, got {:?}",
            other
        ),
    }
}

#[test]
fn extension_selects_literal_with_proper_instances() {
    // Proper instances: an instance is proper if it is not satisfied by I^p(Γ)
    // and its complement is not in I^p(Γ). If all instances of L are complementary,
    // L has no proper instances and should not be selected.
    // Source: "On SGGS and Horn Clauses" (paper6), pcgi definition:
    // "A pcgi ... is not satisfied by I^p(Γ|n−1) ... and ¬L ∉ I^p(Γ|n−1)."
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    // A unit clause ¬p(X) contributes all ground instances of ¬p to I^p(Γ),
    // making every p(t) complementary.
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::neg("p", vec![Term::var("X")])]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![
        Literal::pos("p", vec![Term::var("X")]),
        Literal::pos("q", vec![Term::var("X")]),
    ])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::Extended(cc)
        | ExtensionResult::Conflict(cc)
        | ExtensionResult::Critical { clause: cc, .. } => {
            assert_eq!(cc.selected_literal().atom.predicate, "q");
        }
        ExtensionResult::NoExtension => {
            panic!("Expected extension to apply for a falsified clause");
        }
    }
}

#[test]
fn extension_uses_simultaneous_unification_of_i_true_literals() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("Q", vec![Term::constant("b")])]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::neg("Q", vec![Term::var("Y")]),
        Literal::pos("R", vec![Term::var("X"), Term::var("Y")]),
    ])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::Extended(cc) => {
            let got: std::collections::HashSet<_> =
                cc.clause.literals.clone().into_iter().collect();
            let expected: std::collections::HashSet<_> = vec![
                Literal::neg("P", vec![Term::constant("a")]),
                Literal::neg("Q", vec![Term::constant("b")]),
                Literal::pos("R", vec![Term::constant("a"), Term::constant("b")]),
            ]
            .into_iter()
            .collect();
            assert_eq!(got, expected);
            assert_eq!(
                cc.selected_literal(),
                &Literal::pos("R", vec![Term::constant("a"), Term::constant("b")])
            );
        }
        other => panic!(
            "Expected Extended for simultaneous unification, got {:?}",
            other
        ),
    }
}

#[test]
fn extension_does_not_over_instantiate_free_vars() {
    // Variables not constrained by side premises should remain variables (MGU, not a ground instance).
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("R", vec![Term::var("Y")]),
    ])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::Extended(cc) | ExtensionResult::Critical { clause: cc, .. } => {
            let lit = cc.selected_literal();
            assert_eq!(lit.atom.predicate, "R");
            match &lit.atom.args[0] {
                Term::Var(_) => {}
                _ => panic!("unconstrained variable should not be over-instantiated"),
            }
        }
        other => panic!("Expected extension with unconstrained variable, got {:?}", other),
    }
}

#[test]
fn extension_inherits_constraints_from_side_premises() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let constrained = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
        crate::constraint::Constraint::Atomic(crate::constraint::AtomicConstraint::NotIdentical(
            Term::var("x"),
            Term::constant("a"),
        )),
        0,
    );
    trail.push(constrained);

    let theory = theory_from_clauses(vec![Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("Q", vec![Term::var("X")]),
    ])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::Extended(cc) => {
            let mut found = false;
            for v in cc.clause.variables() {
                let constraint = crate::constraint::Constraint::Atomic(
                    crate::constraint::AtomicConstraint::NotIdentical(
                        Term::Var(v.clone()),
                        Term::constant("a"),
                    ),
                );
                if !cc.constraint.intersects(&constraint.not()) {
                    found = true;
                    break;
                }
            }
            assert!(found, "extension should inherit side-premise constraints");
        }
        other => panic!("Expected extension, got {:?}", other),
    }
}

#[test]
fn extension_not_applied_when_theory_already_satisfied_non_ground() {
    // SGGSdpFOL: extension applies only when I[Γ] does not satisfy S.
    // Formal requirement: if I[Γ] |= S, then no SGGS-extension should apply.
    // Short quote: "since I[Γ ] 6|= S ... SGGS applies SGGS-extension".
    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos(
        "P",
        vec![Term::app("f", vec![Term::var("X")])],
    )])]);

    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    // First extension adds the clause.
    match sggs_extension(&trail, &theory) {
        ExtensionResult::Extended(cc) => trail.push(cc),
        other => panic!("Expected initial extension, got {:?}", other),
    }

    // Now I[Γ] should satisfy S, so extension must not apply again.
    match sggs_extension(&trail, &theory) {
        ExtensionResult::NoExtension => {}
        other => panic!("Expected NoExtension when theory is already satisfied, got {:?}", other),
    }
}

#[test]
fn extension_requires_side_premises_in_disjoint_prefix() {
    // Side premises must be in dp(Γ); a matching literal outside dp should not be used.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));
    // This clause is outside dp because it intersects with the first.
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::var("X")])]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![
        Literal::neg("P", vec![Term::constant("b")]),
        Literal::pos("Q", vec![Term::constant("b")]),
    ])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::NoExtension => {}
        other => panic!(
            "Expected NoExtension when only side premise is outside dp(Γ), got {:?}",
            other
        ),
    }
}

#[test]
fn extension_inapplicable_when_trail_not_disjoint_prefix() {
    // SGGS-extension applies only when Γ = dp(Γ).
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::var("X")])]),
        0,
    ));
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos(
        "Q",
        vec![Term::constant("a")],
    )])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::NoExtension => {}
        other => panic!(
            "Expected NoExtension when Γ != dp(Γ), got {:?}",
            other
        ),
    }
}

#[test]
fn extension_inapplicable_when_conflict_exists() {
    // If a conflict clause exists, extension should not be applicable.
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![Literal::pos(
        "Q",
        vec![Term::constant("a")],
    )])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::NoExtension => {}
        other => panic!(
            "Expected NoExtension when a conflict exists, got {:?}",
            other
        ),
    }
}

/// "Let C ∈ S be a clause such that L1,…,Ln (n ≥ 0) are all its I-true literals."
/// (SGGSdpFOL, Definition 1)
///
/// Requirement: when n=0 there are no side premises; SGGS still uses a most-general
/// semantic falsifier, so variables should not be over-instantiated under sign-based I.
/// Source: bonacina2016.pdf, Definition 12.
/// Quote (Def. 12): "There is a most general semantic falsifier β of (C\\{L1,…,Ln})α"
/// and "As a special case, when n=0, there are no side premises ... [SGGS-extension]
/// adds ... I-all-false instances of input clauses (α is empty and β is not)."
#[test]
fn extension_n0_uses_most_general_falsifier() {
    let trail = Trail::new(InitialInterpretation::AllNegative);
    let clause = Clause::new(vec![Literal::pos("P", vec![Term::var("X")])]);
    let theory = theory_from_clauses(vec![clause.clone()]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::Extended(cc) => {
            let lit = cc.selected_literal();
            let original = &clause.literals[0];
            match unify_literals(lit, original) {
                UnifyResult::Success(_) => {}
                _ => panic!("extended literal must be an instance of the premise"),
            }
            // Semantic requirement: selected literal must be I-false under I⁻ (positive).
            assert!(lit.positive, "selected literal must be I-false under I⁻");
        }
        other => panic!("Expected extension with n=0, got {:?}", other),
    }
}

#[test]
fn extension_n0_uses_most_general_falsifier_i_positive() {
    // Dual of n=0 case under I⁺: selected literal should be I-false (negative).
    let trail = Trail::new(InitialInterpretation::AllPositive);
    let clause = Clause::new(vec![Literal::neg("P", vec![Term::var("X")])]);
    let theory = theory_from_clauses(vec![clause.clone()]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::Extended(cc) => {
            let lit = cc.selected_literal();
            let original = &clause.literals[0];
            match unify_literals(lit, original) {
                UnifyResult::Success(_) => {}
                _ => panic!("extended literal must be an instance of the premise"),
            }
            assert!(
                !lit.positive,
                "selected literal must be I-false under I⁺"
            );
        }
        other => panic!("Expected extension with n=0 under I⁺, got {:?}", other),
    }
}

#[test]
fn extension_conflict_via_extension_substitution() {
    // When every I-false literal intersects an I-true selected literal in dp(Γ),
    // SGGS-extension applies the extension substitution to make the clause uniformly false,
    // yielding a conflict clause (Bonacina 2016, Defs. 18–21).
    // Source: bonacina2016.pdf, Definitions 18–21 (extension substitution / conflict).
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    // I-false selected literal: P(a)
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));
    // I-true selected literal: ¬P(f(a))
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::neg(
            "P",
            vec![Term::app("f", vec![Term::constant("a")])],
        )]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("P", vec![Term::app("f", vec![Term::var("X")])]),
    ])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::Conflict(cc) => {
            // The instantiated clause should be ¬P(a) ∨ P(f(a)).
            let lits: std::collections::HashSet<_> = cc.clause.literals.iter().cloned().collect();
            let expected: std::collections::HashSet<_> = vec![
                Literal::neg("P", vec![Term::constant("a")]),
                Literal::pos("P", vec![Term::app("f", vec![Term::constant("a")])]),
            ]
            .into_iter()
            .collect();
            assert_eq!(lits, expected);
        }
        other => panic!(
            "Expected conflict via extension substitution, got {:?}",
            other
        ),
    }
}

#[test]
fn extension_conflict_via_extension_substitution_i_positive() {
    // Dual of extension_conflict_via_extension_substitution under I⁺.
    let mut trail = Trail::new(InitialInterpretation::AllPositive);
    // I-false selected literal: ¬P(a)
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
        0,
    ));
    // I-true selected literal: P(f(a))
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos(
            "P",
            vec![Term::app("f", vec![Term::constant("a")])],
        )]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![
        Literal::pos("P", vec![Term::var("X")]),
        Literal::neg("P", vec![Term::app("f", vec![Term::var("X")])]),
    ])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::Conflict(cc) => {
            let lits: std::collections::HashSet<_> = cc.clause.literals.iter().cloned().collect();
            let expected: std::collections::HashSet<_> = vec![
                Literal::pos("P", vec![Term::constant("a")]),
                Literal::neg("P", vec![Term::app("f", vec![Term::constant("a")])]),
            ]
            .into_iter()
            .collect();
            assert_eq!(lits, expected);
        }
        other => panic!(
            "Expected conflict via extension substitution under I⁺, got {:?}",
            other
        ),
    }
}

#[test]
fn extension_non_conflicting_selects_literal_with_proper_instances() {
    // Def. 20: choose an I-false literal with proper instances when possible.
    // Source: bonacina2016.pdf, Definition 20.
    // Quote: "provided pcgi(A ⊲ L , Γ A ⊲ E[L]) ≠ ∅"
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));
    // I-all-true clause in dp(Γ) with selected ¬R(a).
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::neg("R", vec![Term::constant("a")])]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("R", vec![Term::var("X")]),
        Literal::pos("S", vec![Term::var("X")]),
    ])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::Extended(cc) => {
            // Def. 20 requires a selected I-false literal with proper instances; it does not
            // require avoiding intersections with selected literals in Γ.
            let mut extended = trail.clone();
            let idx = extended.len();
            extended.push(cc.clone());
            assert!(
                extended.is_proper_selected_instance(idx, cc.selected_literal()),
                "selected literal should have proper constrained ground instances"
            );
            assert!(cc.selected_literal().positive, "selected literal must be I-false under I⁻");
        }
        other => panic!("Expected non-conflicting extension, got {:?}", other),
    }
}

#[test]
fn extension_critical_replaces_clause_when_only_prefix_allows_proper_instances() {
    // Def. 21: when an extension is possible only w.r.t. a proper prefix, it is critical.
    // Source: bonacina2016.pdf, Definition 21.
    // Quote: "the SGGS-extension inference rule replaces J ⊲ N[O] with A ⊲ E[L]"
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        0,
    ));
    // This I-all-true clause blocks R(a) in the full trail.
    trail.push(ConstrainedClause::new(
        Clause::new(vec![Literal::neg("R", vec![Term::constant("a")])]),
        0,
    ));

    let theory = theory_from_clauses(vec![Clause::new(vec![
        Literal::neg("P", vec![Term::var("X")]),
        Literal::pos("R", vec![Term::var("X")]),
    ])]);

    match sggs_extension(&trail, &theory) {
        ExtensionResult::Critical {
            replace_index,
            clause,
        } => {
            assert_eq!(
                replace_index, 1,
                "critical extension should replace the blocker"
            );
            assert_eq!(
                clause.selected_literal(),
                &Literal::pos("R", vec![Term::constant("a")])
            );
        }
        other => panic!("Expected critical extension, got {:?}", other),
    }
}
