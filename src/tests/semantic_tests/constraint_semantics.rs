use super::*;

// =============================================================================
// CONSTRAINT SEMANTIC PROPERTIES
// =============================================================================
//
// Reference: [BP17] Definition 1 (Constraint, standard form)
use crate::constraint::{AtomicConstraint, Constraint};
use crate::unify::Substitution;

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
    assert!(
        !has_root_equals,
        "standard form should not contain RootEquals"
    );
}

#[test]
fn standardize_is_idempotent() {
    let c = Constraint::Or(
        Box::new(Constraint::Atomic(AtomicConstraint::RootEquals(
            Term::var("x"),
            "f".to_string(),
        ))),
        Box::new(Constraint::Atomic(AtomicConstraint::Identical(
            Term::var("x"),
            Term::var("y"),
        ))),
    );
    let std1 = c.standardize();
    let std2 = std1.standardize();
    assert_eq!(std1, std2);
}

#[test]
fn standardize_produces_conjunction_of_atomic_constraints() {
    // Standard form: true/false or conjunctions of x ≠ y and top(x) ≠ f atoms.
    let c = Constraint::Not(Box::new(Constraint::Or(
        Box::new(Constraint::Atomic(AtomicConstraint::Identical(
            Term::var("x"),
            Term::var("y"),
        ))),
        Box::new(Constraint::Atomic(AtomicConstraint::RootEquals(
            Term::var("x"),
            "f".to_string(),
        ))),
    )));
    let std = c.standardize();

    fn ok(c: &Constraint) -> bool {
        match c {
            Constraint::True | Constraint::False => true,
            Constraint::Atomic(AtomicConstraint::NotIdentical(_, _)) => true,
            Constraint::Atomic(AtomicConstraint::RootNotEquals(_, _)) => true,
            Constraint::And(a, b) => ok(a) && ok(b),
            _ => false,
        }
    }

    assert!(
        ok(&std),
        "standard form should be conjunctions of NotIdentical / RootNotEquals"
    );
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
    assert!(inter.is_satisfiable());
    // Intersection should entail both operands (even if simplified).
    assert!(!inter.intersects(&c1.not()));
    assert!(!inter.intersects(&c2.not()));
}

#[test]
fn constraint_intersects_false_when_unsat() {
    let c1 = Constraint::Atomic(AtomicConstraint::NotIdentical(
        Term::var("x"),
        Term::var("x"),
    ));
    assert!(!c1.intersects(&Constraint::True));
}

#[test]
fn constraint_intersects_is_symmetric() {
    let c1 = Constraint::Atomic(AtomicConstraint::NotIdentical(
        Term::var("x"),
        Term::var("y"),
    ));
    let c2 = Constraint::Atomic(AtomicConstraint::RootNotEquals(
        Term::var("x"),
        "f".to_string(),
    ));
    assert_eq!(c1.intersects(&c2), c2.intersects(&c1));
}

#[test]
fn constraint_intersect_with_false_is_unsatisfiable() {
    let c1 = Constraint::Atomic(AtomicConstraint::NotIdentical(
        Term::var("x"),
        Term::var("y"),
    ));
    let inter = c1.intersect(&Constraint::False);
    assert!(!inter.is_satisfiable());
}

#[test]
fn atomic_constraint_evaluate_with_substitution() {
    let c = AtomicConstraint::Identical(Term::var("X"), Term::constant("a"));
    let mut subst = Substitution::empty();
    subst.bind(Var::new("X"), Term::constant("a"));
    assert_eq!(c.evaluate(&subst), Some(true));

    let c = AtomicConstraint::RootNotEquals(Term::var("X"), "f".to_string());
    let mut subst = Substitution::empty();
    subst.bind(Var::new("X"), Term::app("f", vec![Term::constant("a")]));
    assert_eq!(c.evaluate(&subst), Some(false));
}

#[test]
fn atomic_constraint_root_equals_with_substitution() {
    // Source: Semantically_Guided_Goal_Sensitive_Reaso.pdf, Definition 1 (Constraint).
    let c = AtomicConstraint::RootEquals(Term::var("X"), "f".to_string());
    let mut subst = Substitution::empty();
    subst.bind(Var::new("X"), Term::app("f", vec![Term::constant("a")]));
    assert_eq!(c.evaluate(&subst), Some(true));
}

#[test]
fn constraint_simplify_with_true_false_identities() {
    let c = Constraint::Atomic(AtomicConstraint::NotIdentical(
        Term::var("x"),
        Term::var("y"),
    ));
    assert_eq!(c.clone().and(Constraint::True).simplify(), c);
    assert_eq!(c.clone().or(Constraint::False).simplify(), c);
    assert_eq!(
        c.clone().and(Constraint::False).simplify(),
        Constraint::False
    );
    assert_eq!(c.clone().or(Constraint::True).simplify(), Constraint::True);
}

#[test]
fn constraint_simplify_double_negation() {
    let c = Constraint::Atomic(AtomicConstraint::NotIdentical(
        Term::var("x"),
        Term::var("y"),
    ));
    let nn = Constraint::Not(Box::new(Constraint::Not(Box::new(c.clone()))));
    assert_eq!(nn.simplify(), c);
}

#[test]
fn constraint_or_is_satisfiable_when_one_branch_is() {
    let unsat = Constraint::Atomic(AtomicConstraint::NotIdentical(
        Term::var("x"),
        Term::var("x"),
    ));
    let sat = Constraint::Atomic(AtomicConstraint::NotIdentical(
        Term::var("x"),
        Term::var("y"),
    ));
    let or = unsat.or(sat);
    assert!(
        or.is_satisfiable(),
        "disjunction should be satisfiable if any branch is"
    );
}

#[test]
fn constraint_and_negation_do_not_intersect() {
    let c = Constraint::Atomic(AtomicConstraint::NotIdentical(
        Term::var("x"),
        Term::var("y"),
    ));
    assert!(
        !c.intersects(&c.clone().not()),
        "constraint and its negation should have empty intersection"
    );
}
