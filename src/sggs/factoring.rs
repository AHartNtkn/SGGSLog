//! SGGS-Factoring for conflict solving.

use super::ConstrainedClause;

/// SGGS-Factoring: factor a clause by unifying a non-selected literal with the selected literal.
///
/// This is used during conflict solving to avoid losing assignments after a move.
/// Returns the factored clause if applicable.
pub fn sggs_factoring(
    _clause: &ConstrainedClause,
    _other_lit_idx: usize,
) -> Option<ConstrainedClause> {
    todo!("sggs_factoring implementation")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::Constraint;
    use crate::syntax::{Clause, Literal, Term};
    use std::collections::HashSet;

    #[test]
    fn test_factoring_unifies_selected_with_other_literal() {
        // Source: SGGSdpFOL, rule factor (Fig. 2) and standard factoring.
        let clause = ConstrainedClause::with_constraint(
            Clause::new(vec![
                Literal::pos("P", vec![Term::var("X")]),
                Literal::pos("P", vec![Term::constant("a")]),
                Literal::pos("R", vec![Term::var("X")]),
            ]),
            Constraint::True,
            0,
        );

        let factored = sggs_factoring(&clause, 1).expect("expected factoring");
        let expected: HashSet<_> = vec![
            Literal::pos("P", vec![Term::constant("a")]),
            Literal::pos("R", vec![Term::constant("a")]),
        ]
        .into_iter()
        .collect();
        let got: HashSet<_> = factored.clause.literals.clone().into_iter().collect();
        assert_eq!(got, expected);
        assert_eq!(
            factored.selected_literal(),
            &Literal::pos("P", vec![Term::constant("a")])
        );
    }

    #[test]
    fn test_factoring_not_applicable_when_no_unifier() {
        let clause = ConstrainedClause::with_constraint(
            Clause::new(vec![
                Literal::pos("P", vec![Term::var("X")]),
                Literal::pos("Q", vec![Term::constant("a")]),
            ]),
            Constraint::True,
            0,
        );

        assert!(sggs_factoring(&clause, 1).is_none());
    }
}
