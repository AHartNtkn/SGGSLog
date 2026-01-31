//! SGGS-Resolution for conflict explanation.

use super::{ConstrainedClause, Trail};

/// Result of conflict explanation via resolution.
#[derive(Debug)]
pub enum ResolutionResult {
    /// Derived empty clause (theory is unsatisfiable)
    EmptyClause,
    /// Resolution step produced new clause
    Resolvent(ConstrainedClause),
}

/// SGGS-Resolution: resolve conflict clause with justifications.
///
/// When a conflict clause has I-false literals, we resolve them away
/// using justifications from the trail's disjoint prefix.
pub fn sggs_resolution(_conflict: &ConstrainedClause, _trail: &Trail) -> ResolutionResult {
    todo!("sggs_resolution implementation")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::Constraint;
    use crate::sggs::{ConstrainedClause, InitialInterpretation, Trail};
    use crate::syntax::{Clause, Literal, Term};

    fn unit(lit: Literal) -> ConstrainedClause {
        ConstrainedClause::with_constraint(Clause::new(vec![lit]), Constraint::True, 0)
    }

    #[test]
    fn test_resolution_resolvent_definition_2() {
        // Source: SGGSdpFOL.pdf, Definition 2 (SGGS-Resolution).
        // Resolve A | C[L] with B | D[M], where M is I-all-true and precedes.
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        let left = unit(Literal::neg("P", vec![Term::constant("a")]));
        trail.push(left.clone()); // I-all-true clause in dp(Γ)

        let conflict_clause = ConstrainedClause::with_constraint(
            Clause::new(vec![
                Literal::pos("P", vec![Term::constant("a")]),
                Literal::pos("Q", vec![Term::constant("a")]),
            ]),
            Constraint::True,
            0,
        );
        trail.push(conflict_clause.clone());

        match sggs_resolution(&conflict_clause, &trail) {
            ResolutionResult::Resolvent(resolvent) => {
                assert_eq!(
                    resolvent.clause.literals,
                    vec![Literal::pos("Q", vec![Term::constant("a")])]
                );
            }
            ResolutionResult::EmptyClause => panic!("Expected non-empty resolvent"),
        }
    }

    #[test]
    fn test_resolution_empty_clause() {
        // Source: SGGSdpFOL.pdf, Definition 2 (SGGS-Resolution).
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        let left = unit(Literal::neg("P", vec![Term::constant("a")]));
        trail.push(left);

        let conflict_clause = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::constant("a")])]),
            Constraint::True,
            0,
        );
        trail.push(conflict_clause.clone());

        match sggs_resolution(&conflict_clause, &trail) {
            ResolutionResult::EmptyClause => {}
            other => panic!("Expected empty clause, got {:?}", other),
        }
    }
}
