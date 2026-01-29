//! SGGS trail (clause sequence) for model representation.

use super::constrained::ConstrainedClause;
use super::interpretation::InitialInterpretation;
use crate::syntax::Literal;
use crate::theory::Theory;

/// The SGGS trail (clause sequence).
///
/// A trail Γ = C₁[L₁], ..., Cₙ[Lₙ] represents a candidate partial model.
/// Each clause has a selected literal that contributes to the interpretation.
#[derive(Debug, Clone)]
pub struct Trail {
    clauses: Vec<ConstrainedClause>,
    initial_interp: InitialInterpretation,
}

/// The interpretation induced by a trail.
pub struct TrailInterpretation<'a> {
    trail: &'a Trail,
}

impl Trail {
    /// Create an empty trail with the given initial interpretation.
    pub fn new(interp: InitialInterpretation) -> Self {
        todo!("Trail::new implementation")
    }

    /// Get the number of clauses in the trail.
    pub fn len(&self) -> usize {
        todo!("Trail::len implementation")
    }

    /// Check if the trail is empty.
    pub fn is_empty(&self) -> bool {
        todo!("Trail::is_empty implementation")
    }

    /// Add a clause to the trail.
    pub fn push(&mut self, clause: ConstrainedClause) {
        todo!("Trail::push implementation")
    }

    /// Get a prefix of this trail.
    pub fn prefix(&self, len: usize) -> Trail {
        todo!("Trail::prefix implementation")
    }

    /// Get the interpretation induced by this trail.
    pub fn interpretation(&self) -> TrailInterpretation {
        todo!("Trail::interpretation implementation")
    }

    /// Compute the length of the disjoint prefix.
    pub fn disjoint_prefix_length(&self) -> usize {
        todo!("Trail::disjoint_prefix_length implementation")
    }

    /// Check if this trail is complete for the theory.
    pub fn is_complete(&self, theory: &Theory) -> bool {
        todo!("Trail::is_complete implementation")
    }

    /// Find a conflict clause in the trail.
    pub fn find_conflict(&self) -> Option<usize> {
        todo!("Trail::find_conflict implementation")
    }

    /// Get the clauses in this trail.
    pub fn clauses(&self) -> &[ConstrainedClause] {
        &self.clauses
    }
}

impl<'a> TrailInterpretation<'a> {
    /// Is literal uniformly true in I[Γ]?
    pub fn is_uniformly_true(&self, lit: &Literal) -> bool {
        todo!("TrailInterpretation::is_uniformly_true implementation")
    }

    /// Is literal uniformly false in I[Γ]?
    pub fn is_uniformly_false(&self, lit: &Literal) -> bool {
        todo!("TrailInterpretation::is_uniformly_false implementation")
    }

    /// Get I-false selected literals for extension.
    pub fn i_false_selected(&self) -> Vec<(usize, &'a Literal)> {
        todo!("TrailInterpretation::i_false_selected implementation")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::Constraint;
    use crate::sggs::ConstrainedClause;
    use crate::syntax::{Clause, Literal, Term};

    fn unit(lit: Literal) -> ConstrainedClause {
        ConstrainedClause::with_constraint(Clause::new(vec![lit]), Constraint::True, 0)
    }

    #[test]
    fn test_disjoint_prefix_length_example_1() {
        // Source: bonacina2016.pdf, Example 1 and Definition 5 (disjoint prefix).
        // For Gamma = P(a,x), P(b,y), not P(z,z), P(u,v), dp(Gamma) = first two clauses.
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos(
            "P",
            vec![Term::constant("a"), Term::var("x")],
        )));
        trail.push(unit(Literal::pos(
            "P",
            vec![Term::constant("b"), Term::var("y")],
        )));
        trail.push(unit(Literal::neg(
            "P",
            vec![Term::var("z"), Term::var("z")],
        )));
        trail.push(unit(Literal::pos(
            "P",
            vec![Term::var("u"), Term::var("v")],
        )));

        assert_eq!(trail.disjoint_prefix_length(), 2);
    }

    #[test]
    fn test_induced_interpretation_example_4() {
        // Source: bonacina2016.pdf, Example 4 and Definition 7 (induced interpretation).
        // With I all-negative, after [P(x)] we have P(a) true; after adding [Q(y)] we have Q(a) true;
        // after adding [R(f(z),g(z))] we have R(f(a),g(a)) true.
        let mut trail = Trail::new(InitialInterpretation::AllNegative);

        // C1 = [P(x)]
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));

        // C2 = not P(f(y)) or [Q(y)]
        let c2 = Clause::new(vec![
            Literal::neg(
                "P",
                vec![Term::app("f", vec![Term::var("y")])],
            ),
            Literal::pos("Q", vec![Term::var("y")]),
        ]);
        trail.push(ConstrainedClause::with_constraint(c2, Constraint::True, 1));

        // C3 = not P(f(z)) or not Q(g(z)) or [R(f(z), g(z))]
        let c3 = Clause::new(vec![
            Literal::neg(
                "P",
                vec![Term::app("f", vec![Term::var("z")])],
            ),
            Literal::neg(
                "Q",
                vec![Term::app("g", vec![Term::var("z")])],
            ),
            Literal::pos(
                "R",
                vec![
                    Term::app("f", vec![Term::var("z")]),
                    Term::app("g", vec![Term::var("z")]),
                ],
            ),
        ]);
        trail.push(ConstrainedClause::with_constraint(c3, Constraint::True, 2));

        let p_a = Literal::pos("P", vec![Term::constant("a")]);
        let q_a = Literal::pos("Q", vec![Term::constant("a")]);
        let r_fa_ga = Literal::pos(
            "R",
            vec![
                Term::app("f", vec![Term::constant("a")]),
                Term::app("g", vec![Term::constant("a")]),
            ],
        );

        let prefix1 = trail.prefix(1);
        let interp1 = prefix1.interpretation();
        assert!(interp1.is_uniformly_true(&p_a));
        assert!(interp1.is_uniformly_false(&q_a));

        let prefix2 = trail.prefix(2);
        let interp2 = prefix2.interpretation();
        assert!(interp2.is_uniformly_true(&q_a));

        let prefix3 = trail.prefix(3);
        let interp3 = prefix3.interpretation();
        assert!(interp3.is_uniformly_true(&r_fa_ga));
    }
}
