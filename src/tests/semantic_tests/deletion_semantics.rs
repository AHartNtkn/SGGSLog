use super::*;

// =============================================================================
// SGGS DELETION / DISPOSABILITY SEMANTICS
// =============================================================================
//
// Reference: bonacina2016.pdf, Definition 6 (Disposable clause)
// Quote: "A non-empty clause A ⊲ C[L] in Γ is disposable if
// pcgi(A ⊲ L, Γ) = ccgi(A ⊲ L, Γ) = ∅."

use crate::constraint::Constraint;
use crate::sggs::{is_disposable, sggs_deletion, ConstrainedClause, InitialInterpretation, Trail};

fn unit(lit: Literal) -> ConstrainedClause {
    ConstrainedClause::with_constraint(Clause::new(vec![lit]), Constraint::True, 0)
}

#[test]
fn disposable_when_satisfied_by_left_prefix() {
    // Example 2 (Bonacina 2016).
    // Quote: "In P(x), ¬Q(x), P(x), the second P(x) is disposable."
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
    trail.push(unit(Literal::neg("Q", vec![Term::var("x")])));
    trail.push(unit(Literal::pos("P", vec![Term::var("x")])));

    let idx = 2;
    assert!(
        is_disposable(&trail.clauses()[idx], &trail),
        "clause satisfied by left prefix should be disposable"
    );
}

#[test]
fn not_disposable_when_complementary_instances_exist() {
    // Example 2 (Bonacina 2016).
    // Quote: "In ¬P(x), ¬Q(x), P(x), clause P(x) is not disposable."
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    trail.push(unit(Literal::neg("P", vec![Term::var("x")])));
    trail.push(unit(Literal::neg("Q", vec![Term::var("x")])));
    trail.push(unit(Literal::pos("P", vec![Term::var("x")])));

    let idx = 2;
    assert!(
        !is_disposable(&trail.clauses()[idx], &trail),
        "clause with complementary instances should not be disposable"
    );
}

#[test]
fn deletion_removes_disposable_clause() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let c1 = unit(Literal::pos("P", vec![Term::var("x")]));
    let c2 = unit(Literal::neg("Q", vec![Term::var("x")]));
    let c3 = unit(Literal::pos("P", vec![Term::var("x")]));
    trail.push(c1.clone());
    trail.push(c2.clone());
    trail.push(c3.clone());

    assert!(is_disposable(&trail.clauses()[2], &trail));
    sggs_deletion(&mut trail);
    assert_eq!(trail.len(), 2, "deletion should remove disposable clause");
    assert!(trail
        .clauses()
        .iter()
        .any(|c| c.selected_literal() == c1.selected_literal()));
    assert!(trail
        .clauses()
        .iter()
        .any(|c| c.selected_literal() == c2.selected_literal()));
}

#[test]
fn disposable_when_constraint_false() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let clause = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
        Constraint::False,
        0,
    );
    trail.push(clause);
    assert!(
        is_disposable(&trail.clauses()[0], &trail),
        "unsatisfiable constraint should make clause disposable"
    );
}

#[test]
fn deletion_removes_all_disposable_clauses() {
    let mut trail = Trail::new(InitialInterpretation::AllNegative);
    let c1 = unit(Literal::pos("P", vec![Term::var("x")]));
    let c2 = unit(Literal::neg("Q", vec![Term::var("x")]));
    let c3 = unit(Literal::pos("P", vec![Term::var("x")])); // disposable
    let c4 = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("R", vec![Term::var("y")])]),
        Constraint::False,
        0,
    ); // disposable
    trail.push(c1.clone());
    trail.push(c2.clone());
    trail.push(c3);
    trail.push(c4);

    sggs_deletion(&mut trail);
    assert_eq!(trail.len(), 2, "all disposable clauses should be removed");
    assert!(trail
        .clauses()
        .iter()
        .any(|c| c.selected_literal() == c1.selected_literal()));
    assert!(trail
        .clauses()
        .iter()
        .any(|c| c.selected_literal() == c2.selected_literal()));
}
