use super::*;

// =============================================================================
// SGGS SPLITTING PROPERTIES
// =============================================================================
//
// Reference: [BP16a] Definitions 13-15 (partition and splitting)
use crate::constraint::{AtomicConstraint, Constraint};
use crate::sggs::ConstrainedClause;
use crate::unify::{unify_literals, Substitution};

fn combined_constraint(
    left: &Constraint,
    right: &Constraint,
    subst: &Substitution,
) -> Constraint {
    let mut acc = Constraint::True;
    for v in subst.domain() {
        if let Some(t) = subst.lookup(v) {
            acc = acc.and(Constraint::Atomic(AtomicConstraint::Identical(
                Term::Var(v.clone()),
                t.clone(),
            )));
        }
    }
    acc.and(left.clone()).and(right.clone())
}

fn intersects(a: &ConstrainedClause, b: &ConstrainedClause) -> bool {
    match unify_literals(a.selected_literal(), b.selected_literal()) {
        crate::unify::UnifyResult::Success(sigma) => {
            combined_constraint(&a.constraint, &b.constraint, &sigma).is_satisfiable()
        }
        crate::unify::UnifyResult::Failure(_) => false,
    }
}

#[test]
fn splitting_partition_is_disjoint_and_isolates_intersection() {
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

    // Each part must be an instance of the original specified literal.
    for part in &result.parts {
        assert!(
            unify_literals(part.selected_literal(), clause.selected_literal()).is_success(),
            "split part must be an instance of the original literal"
        );
        assert!(
            part.constraint.is_satisfiable(),
            "split part must not introduce an empty constraint"
        );
    }

    // Parts must be pairwise disjoint (no overlapping constrained instances).
    for i in 0..result.parts.len() {
        for j in (i + 1)..result.parts.len() {
            assert!(
                !intersects(&result.parts[i], &result.parts[j]),
                "split parts must be disjoint"
            );
        }
    }

    // Exactly one part should intersect the other clause's selected literal.
    let intersection_count = result
        .parts
        .iter()
        .filter(|p| intersects(p, &other))
        .count();
    assert_eq!(
        intersection_count, 1,
        "split should isolate exactly one intersection representative"
    );
}

#[test]
fn splitting_propagates_constraints_for_intersection() {
    // Split P(x) against P(a): expect one part with x = a and one with x ≠ a.
    let clause = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
        Constraint::True,
        0,
    );
    let other = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
        Constraint::True,
        0,
    );

    let result = crate::sggs::sggs_splitting(&clause, &other).expect("expected split result");
    let x_eq_a = Constraint::Atomic(AtomicConstraint::Identical(
        Term::var("x"),
        Term::constant("a"),
    ));

    let mut intersects = 0;
    let mut disjoint = 0;
    for part in &result.parts {
        if part.constraint.clone().and(x_eq_a.clone()).is_satisfiable() {
            intersects += 1;
        } else {
            disjoint += 1;
        }
    }
    assert_eq!(intersects, 1, "exactly one split part should allow x = a");
    assert!(disjoint >= 1, "at least one split part should exclude x = a");
}

#[test]
fn splitting_returns_none_for_disjoint_literals() {
    let clause = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
        Constraint::True,
        0,
    );
    let other = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("Q", vec![Term::var("y")])]),
        Constraint::True,
        0,
    );

    assert!(crate::sggs::sggs_splitting(&clause, &other).is_none());
}

#[test]
fn splitting_representative_matches_intersection() {
    let clause = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x"), Term::var("y")])]),
        Constraint::True,
        0,
    );
    let other = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a"), Term::var("y")])]),
        Constraint::True,
        0,
    );

    let result = crate::sggs::sggs_splitting(&clause, &other).expect("expected split result");
    let intersection_count = result
        .parts
        .iter()
        .filter(|p| intersects(p, &other))
        .count();
    assert_eq!(
        intersection_count, 1,
        "split should include representative of the intersection"
    );
}

#[test]
fn splitting_has_no_missing_instances_symbolically() {
    // [BP16a] Def 13-15: partition must cover all constrained ground instances.
    // We check symbolic coverage by ensuring the original constraint implies
    // the disjunction of the split-part constraints (after unifying literals).
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
    fn apply_subst_term(subst: &Substitution, term: &Term) -> Term {
        match term {
            Term::Var(v) => subst.lookup(v).cloned().unwrap_or_else(|| Term::Var(v.clone())),
            Term::Const(_) => term.clone(),
            Term::App(sym, args) => {
                let new_args = args.iter().map(|t| apply_subst_term(subst, t)).collect();
                Term::App(sym.clone(), new_args)
            }
        }
    }

    fn apply_subst_constraint(subst: &Substitution, c: &Constraint) -> Constraint {
        match c {
            Constraint::True => Constraint::True,
            Constraint::False => Constraint::False,
            Constraint::Atomic(a) => match a {
                AtomicConstraint::Identical(t1, t2) => Constraint::Atomic(
                    AtomicConstraint::Identical(
                        apply_subst_term(subst, t1),
                        apply_subst_term(subst, t2),
                    ),
                ),
                AtomicConstraint::NotIdentical(t1, t2) => Constraint::Atomic(
                    AtomicConstraint::NotIdentical(
                        apply_subst_term(subst, t1),
                        apply_subst_term(subst, t2),
                    ),
                ),
                AtomicConstraint::RootEquals(t, f) => Constraint::Atomic(
                    AtomicConstraint::RootEquals(apply_subst_term(subst, t), f.clone()),
                ),
                AtomicConstraint::RootNotEquals(t, f) => Constraint::Atomic(
                    AtomicConstraint::RootNotEquals(apply_subst_term(subst, t), f.clone()),
                ),
            },
            Constraint::And(a, b) => Constraint::And(
                Box::new(apply_subst_constraint(subst, a)),
                Box::new(apply_subst_constraint(subst, b)),
            ),
            Constraint::Or(a, b) => Constraint::Or(
                Box::new(apply_subst_constraint(subst, a)),
                Box::new(apply_subst_constraint(subst, b)),
            ),
            Constraint::Not(inner) => {
                Constraint::Not(Box::new(apply_subst_constraint(subst, inner)))
            }
        }
    }

    let mut coverage = Constraint::False;
    for part in &result.parts {
        let sigma = match unify_literals(part.selected_literal(), clause.selected_literal()) {
            crate::unify::UnifyResult::Success(s) => s,
            crate::unify::UnifyResult::Failure(_) => {
                panic!("split part must be an instance of the original literal");
            }
        };
        let translated = apply_subst_constraint(&sigma, &part.constraint);
        coverage = coverage.or(translated);
    }

    // No missing instances: original constraint implies coverage.
    let missing = clause.constraint.clone().and(coverage.not());
    assert!(
        !missing.is_satisfiable(),
        "split should not miss any instances of the original clause"
    );
}

#[test]
fn splitting_trivial_returns_none() {
    // [BP16a] Example 9: trivial splitting (by an equal/more general clause) should not apply.
    let clause = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
        Constraint::True,
        0,
    );
    let other = clause.clone();

    assert!(
        crate::sggs::sggs_splitting(&clause, &other).is_none(),
        "Trivial splitting should be rejected"
    );
}
