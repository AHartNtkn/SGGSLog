use super::*;

// =============================================================================
// CONFLICT-SOLVING INTEGRATION (EXTENSION -> CONFLICT -> MOVE -> RESOLUTION)
// =============================================================================
//
// References: Semantically_Guided_Goal_Sensitive_Reaso.pdf (Example 9),
// SGGSdpFOL.pdf (conflict explanation and move rules).

use crate::constraint::Constraint;
use crate::sggs::{
    sggs_factoring, sggs_left_split, sggs_move, sggs_resolution, ConstrainedClause,
    InitialInterpretation, ResolutionResult, Trail,
};

#[test]
fn conflict_solving_chain_reaches_empty_clause() {
    // Theory: P(a), ¬P(x) ∨ Q(x), ¬Q(a)
    // Build the trail explicitly to avoid assuming a deterministic extension order.
    let a = Term::constant("a");
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![a.clone()])]),
        Constraint::True,
        0,
    ));
    // Extension must add the instance produced by unifying the I-true literal P(a)
    // with ¬P(x) ∨ Q(x), yielding ¬P(a) ∨ Q(a) (or an equivalent constraint).
    //
    // Formal basis (BP17 / bonacina2016.txt):
    // - Extension is defined as instance generation: "SGGS-extension inference scheme
    //   generates the clause A ⊢ E = (∧ Bj αβ) ⊢ Cαβ".
    // - The instance is built by unification with side premises: "simultaneous most general
    //   unifier α such that Lj α = ¬Mj α".
    // - This is model-driven: "SGGS-extension unifies literals with I -false selected literals".
    //
    // Concrete example (same source, Example 6):
    // - "SGGS-extension generates Γ2 = [P(a)], ¬P(a) ∨ [Q(f(y))]".
    //   The non-ground clause ¬P(x) ∨ Q(f(y)) does not appear; the instance ¬P(a) ∨ Q(f(y))
    //   does, because α = {x ← a} is applied.
    //
    // Therefore, the trail in this test must contain the instantiated clause ¬P(a) ∨ Q(a),
    // not the non-ground ¬P(x) ∨ Q(x). That alignment is required by the SGGS definition.
    trail.push(ConstrainedClause::with_constraint(
        Clause::new(vec![
            Literal::neg("P", vec![a.clone()]),
            Literal::pos("Q", vec![a.clone()]),
        ]),
        Constraint::True,
        1,
    ));
    let conflict = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::neg("Q", vec![a.clone()])]),
        Constraint::True,
        0,
    );
    trail.push(conflict.clone());

    // Conflict/move/resolution justification:
    // - Conflict clause criterion (BP17, bonacina2016.txt, §3): "if all literals of C are uniformly false in I [Γ ], C is a conflict clause."
    // - Conflict explanation (BP17, bonacina2016.txt, §3): "resolves a conflict clause and a justification".
    // - Move ordering (SGGSdpFOL.txt, §3, Fig. 2 discussion): "moves B B D[M ] to the left of the clause A B C[L] in dp(Γ ) to which M is assigned."
    // Move the I-all-true conflict clause ¬Q(a) before its justifying clause (¬P(x) ∨ Q(x)).
    let conflict_idx = trail.clauses().len() - 1;
    sggs_move(&mut trail, conflict_idx).expect("move failed");

    // After move, resolve the conflict clause with I-false selected literal (Q)
    // against its I-all-true justification (¬Q(a)).
    let conflict_clause = trail
        .clauses()
        .iter()
        .find(|c| c.selected_literal() == &Literal::pos("Q", vec![a.clone()]))
        .expect("conflict clause with selected Q(a) not found")
        .clone();
    let res1 = sggs_resolution(&conflict_clause, &trail);
    let cc = match res1 {
        ResolutionResult::Resolvent(cc) => cc,
        ResolutionResult::EmptyClause => {
            panic!("Expected non-empty conflict-preserving resolvent");
        }
        ResolutionResult::Inapplicable => {
            panic!("Resolution should be applicable");
        }
    };
    assert_eq!(cc.clause.literals, vec![Literal::neg("P", vec![a.clone()])]);
    assert!(cc.is_conflict(&trail.interpretation()));

    // Resolve ¬P(a) with P(a) to derive the empty clause.
    let res2 = sggs_resolution(&cc, &trail);
    assert!(matches!(res2, ResolutionResult::EmptyClause));
}

#[test]
fn resolution_can_return_conflict_resolvent() {
    // If resolution yields a conflict clause, it should return a resolvent
    // that is still a conflict under the trail interpretation.
    let a = Term::constant("a");
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![a.clone()])));
    trail.push(unit(Literal::pos("Q", vec![a.clone()])));

    let conflict = ConstrainedClause::with_constraint(
        Clause::new(vec![
            Literal::neg("P", vec![a.clone()]),
            Literal::neg("Q", vec![a.clone()]),
        ]),
        Constraint::True,
        0,
    );
    trail.push(conflict.clone());

    match sggs_resolution(&conflict, &trail) {
        ResolutionResult::Resolvent(cc) => {
            assert!(cc.clause.literals.iter().all(|l| !l.positive));
            assert!(cc.is_conflict(&trail.interpretation()));
        }
        ResolutionResult::EmptyClause => {
            panic!("Expected non-empty conflict clause");
        }
        ResolutionResult::Inapplicable => {
            panic!("Resolution should be applicable");
        }
    }
}

#[test]
fn conflict_solving_chain_with_factoring() {
    // Source: SGGSdpFOL, Fig. 2 (factor) and conflict solving sequence.
    // Conflict clause with duplicate same-sign literal should be factored before resolution.
    let a = Term::constant("a");
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![a.clone()])));

    let conflict = ConstrainedClause::with_constraint(
        Clause::new(vec![
            Literal::neg("P", vec![a.clone()]),
            Literal::neg("P", vec![a.clone()]),
        ]),
        Constraint::True,
        0,
    );

    let factored = sggs_factoring(&conflict, 1).expect("expected factoring");
    trail.push(factored.clone());

    let res = sggs_resolution(&factored, &trail);
    assert!(
        matches!(res, ResolutionResult::EmptyClause),
        "factoring should allow resolution to reach empty clause"
    );
}

#[test]
fn conflict_solving_chain_with_left_split() {
    // Source: SGGSdpFOL, Fig. 2 (l-split) and conflict solving sequence.
    // Left-split should isolate the intersection so resolution can eliminate the conflict.
    let a = Term::constant("a");
    let mut trail = Trail::new(InitialInterpretation::AllNegative);

    let base = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
        Constraint::True,
        0,
    );
    trail.push(base.clone());

    let conflict = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::neg("P", vec![a.clone()])]),
        Constraint::True,
        0,
    );

    let split = sggs_left_split(&base, &conflict).expect("expected left split");
    let x_eq_a = Constraint::Atomic(crate::constraint::AtomicConstraint::Identical(
        Term::var("x"),
        a.clone(),
    ));
    let representative = split
        .parts
        .iter()
        .find(|p| p.constraint.clone().and(x_eq_a.clone()).is_satisfiable())
        .expect("expected representative intersecting with P(a)")
        .clone();

    let mut trail2 = Trail::new(InitialInterpretation::AllNegative);
    trail2.push(representative.clone());
    trail2.push(conflict.clone());

    let res = sggs_resolution(&conflict, &trail2);
    match res {
        ResolutionResult::EmptyClause => {}
        ResolutionResult::Resolvent(cc) => {
            assert!(cc.is_conflict(&trail2.interpretation()));
        }
        ResolutionResult::Inapplicable => {
            panic!("Resolution should be applicable");
        }
    }
}
