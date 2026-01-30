//! SGGS-Extension inference rule.

use super::{ConstrainedClause, Trail};
use crate::theory::Theory;

/// Result of attempting SGGS-Extension.
#[derive(Debug)]
pub enum ExtensionResult {
    /// Successfully extended trail
    Extended(ConstrainedClause),
    /// No extension possible (trail is complete)
    NoExtension,
    /// Found conflict during extension
    Conflict(ConstrainedClause),
}

/// Attempt SGGS-Extension.
///
/// Finds a clause C in the theory where I-true literals of C unify with
/// I-false selected literals on the trail, and generates an instance to add.
pub fn sggs_extension(
    _trail: &Trail,
    _theory: &Theory,
) -> ExtensionResult {
    todo!("sggs_extension implementation")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::Constraint;
    use crate::sggs::{ConstrainedClause, InitialInterpretation, Trail};
    use crate::syntax::{Clause, Literal, Term};
    use crate::theory::Theory;
    use std::collections::HashSet;

    fn unit(lit: Literal) -> ConstrainedClause {
        ConstrainedClause::with_constraint(Clause::new(vec![lit]), Constraint::True, 0)
    }

    #[test]
    fn test_extension_non_conflicting_instance_added() {
        // Source: SGGSdpFOL.pdf, Definition 1 (SGGS-extension scheme).
        // With I = all-negative, I-true literals are negative, I-false are positive.
        // Clause C = not P(x) or Q(x), with side premise selecting P(a), yields C[a/x].
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));

        let mut theory = Theory::new();
        let clause = Clause::new(vec![
            Literal::neg("P", vec![Term::var("x")]),
            Literal::pos("Q", vec![Term::var("x")]),
        ]);
        theory.add_clause(clause);

        match sggs_extension(&trail, &theory) {
            ExtensionResult::Extended(cc) => {
                let got: HashSet<_> = cc.clause.literals.iter().cloned().collect();
                let expected: HashSet<_> = vec![
                    Literal::neg("P", vec![Term::constant("a")]),
                    Literal::pos("Q", vec![Term::constant("a")]),
                ]
                .into_iter()
                .collect();
                assert_eq!(got, expected);

                // With I all-negative, selected literal must be I-false (positive).
                let interp = InitialInterpretation::AllNegative;
                assert!(interp.is_false(cc.selected_literal()));
                assert_eq!(
                    cc.selected_literal(),
                    &Literal::pos("Q", vec![Term::constant("a")])
                );
            }
            other => panic!("Expected extension, got {:?}", other),
        }
    }

    #[test]
    fn test_extension_all_true_conflict() {
        // Source: paper6.pdf, Definition 1 (SGGS-extension):
        // if the extension clause is I-all-true, it is a conflict clause.
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));

        let mut theory = Theory::new();
        let clause = Clause::new(vec![
            Literal::neg("P", vec![Term::var("x")]),
        ]);
        theory.add_clause(clause);

        match sggs_extension(&trail, &theory) {
            ExtensionResult::Conflict(cc) => {
                assert_eq!(
                    cc.clause.literals,
                    vec![Literal::neg("P", vec![Term::constant("a")])]
                );
            }
            other => panic!("Expected conflict extension, got {:?}", other),
        }
    }

    #[test]
    fn test_extension_with_no_i_true_literals() {
        // Source: SGGSdpFOL.pdf, Definition 1 (SGGS-extension scheme), n ≥ 0.
        // If a clause has no I-true literals, extension does not need side premises.
        // (Here we use a ground clause; the non-ground case is covered separately.)
        let trail = Trail::new(InitialInterpretation::AllNegative);

        let mut theory = Theory::new();
        theory.add_clause(Clause::new(vec![Literal::pos(
            "P",
            vec![Term::constant("a")],
        )]));

        match sggs_extension(&trail, &theory) {
            ExtensionResult::Extended(cc) => {
                assert_eq!(
                    cc.clause.literals,
                    vec![Literal::pos("P", vec![Term::constant("a")])]
                );
                assert_eq!(
                    cc.selected_literal(),
                    &Literal::pos("P", vec![Term::constant("a")])
                );
            }
            other => panic!("Expected extension with n=0, got {:?}", other),
        }
    }

    #[test]
    fn test_extension_with_no_i_true_literals_non_ground() {
        // Source: SGGSdpFOL.pdf, Definition 1 (SGGS-extension scheme), n ≥ 0.
        // With no I-true literals, the extension clause can be a non-ground instance.
        let trail = Trail::new(InitialInterpretation::AllNegative);

        let mut theory = Theory::new();
        let clause = Clause::new(vec![Literal::pos("P", vec![Term::var("X")])]);
        theory.add_clause(clause.clone());

        match sggs_extension(&trail, &theory) {
            ExtensionResult::Extended(cc) => {
                assert_eq!(cc.clause.literals.len(), 1);
                let lit = cc.selected_literal();
                assert!(lit.positive);
                assert!(
                    crate::unify::unify_literals(lit, &clause.literals[0]).is_success(),
                    "extended literal should be an instance of the original"
                );
            }
            other => panic!("Expected non-ground extension with n=0, got {:?}", other),
        }
    }
}
