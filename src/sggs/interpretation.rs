//! Initial interpretation for SGGS semantic guidance.

use crate::syntax::{Atom, Clause, Literal, Term};
use crate::unify::Substitution;
use std::collections::HashSet;

/// Three-valued truth value for semantic guidance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TruthValue {
    True,
    False,
    Unknown,
}

/// The initial interpretation I that guides SGGS.
///
/// SGGS is semantically guided: an initial interpretation I determines
/// which literals are "I-true" vs "I-false". This guides literal selection
/// and the direction of model construction.
#[derive(Debug, Clone)]
pub enum InitialInterpretation {
    /// I⁺: All atoms are true (all positive literals true, negative false)
    AllPositive,
    /// I⁻: All atoms are false (all positive literals false, negative true)
    AllNegative,
    /// Explicit interpretation with designated true/false atoms; others are Unknown by default.
    Explicit {
        true_atoms: HashSet<Atom>,
        false_atoms: HashSet<Atom>,
        default: TruthValue,
    },
}

impl Default for InitialInterpretation {
    fn default() -> Self {
        InitialInterpretation::AllNegative
    }
}

impl InitialInterpretation {
    /// Truth value of a ground literal in I (may be Unknown).
    pub fn truth_value(&self, lit: &Literal) -> TruthValue {
        todo!("InitialInterpretation::truth_value implementation")
    }

    /// Is this ground literal true in I?
    pub fn is_true(&self, lit: &Literal) -> bool {
        matches!(self.truth_value(lit), TruthValue::True)
    }

    /// Is this ground literal false in I?
    pub fn is_false(&self, lit: &Literal) -> bool {
        matches!(self.truth_value(lit), TruthValue::False)
    }

    /// Is this ground atom true in I?
    pub fn atom_is_true(&self, _atom: &Atom) -> bool {
        todo!("InitialInterpretation::atom_is_true implementation")
    }

    /// Attempt to compute a semantic falsifier for a clause in this interpretation.
    ///
    /// Returns a substitution that makes the clause false in I, if one is known.
    pub fn semantic_falsifier(&self, _clause: &Clause) -> Option<Substitution> {
        todo!("InitialInterpretation::semantic_falsifier implementation")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::{Atom, Literal, Term};

    #[test]
    fn test_all_negative_interpretation_polarity() {
        // Source: bonacina2016.pdf, Example 3: all-negative interpretation
        // makes negative literals true and positive literals false.
        let interp = InitialInterpretation::AllNegative;
        let pos = Literal::pos("p", vec![Term::constant("a")]);
        let neg = Literal::neg("p", vec![Term::constant("a")]);
        assert!(interp.is_false(&pos));
        assert!(interp.is_true(&neg));
    }

    #[test]
    fn test_all_positive_interpretation_polarity() {
        // Source: bonacina2016.pdf, discussion on sign-based I:
        // all-positive makes positive literals true.
        let interp = InitialInterpretation::AllPositive;
        let pos = Literal::pos("p", vec![Term::constant("a")]);
        let neg = Literal::neg("p", vec![Term::constant("a")]);
        assert!(interp.is_true(&pos));
        assert!(interp.is_false(&neg));
    }

    #[test]
    fn test_atom_truth_all_positive_and_negative() {
        let atom = Atom::new("p", vec![Term::constant("a")]);
        let pos = InitialInterpretation::AllPositive;
        let neg = InitialInterpretation::AllNegative;
        assert!(pos.atom_is_true(&atom));
        assert!(!neg.atom_is_true(&atom));
    }

    #[test]
    fn test_explicit_interpretation_unknown_default() {
        let interp = InitialInterpretation::Explicit {
            true_atoms: HashSet::new(),
            false_atoms: HashSet::new(),
            default: TruthValue::Unknown,
        };
        let lit = Literal::pos("p", vec![Term::constant("a")]);
        assert_eq!(interp.truth_value(&lit), TruthValue::Unknown);
    }

    #[test]
    fn test_explicit_interpretation_truth_tables() {
        let mut trues = HashSet::new();
        trues.insert(Atom::new("p", vec![Term::constant("a")]));
        let mut falses = HashSet::new();
        falses.insert(Atom::new("q", vec![Term::constant("b")]));

        let interp = InitialInterpretation::Explicit {
            true_atoms: trues,
            false_atoms: falses,
            default: TruthValue::Unknown,
        };

        let p_a = Literal::pos("p", vec![Term::constant("a")]);
        let not_p_a = Literal::neg("p", vec![Term::constant("a")]);
        let q_b = Literal::pos("q", vec![Term::constant("b")]);
        let not_q_b = Literal::neg("q", vec![Term::constant("b")]);

        assert_eq!(interp.truth_value(&p_a), TruthValue::True);
        assert_eq!(interp.truth_value(&not_p_a), TruthValue::False);
        assert_eq!(interp.truth_value(&q_b), TruthValue::False);
        assert_eq!(interp.truth_value(&not_q_b), TruthValue::True);
    }

    #[test]
    fn test_semantic_falsifier_for_ground_false_clause() {
        let mut falses = HashSet::new();
        falses.insert(Atom::new("p", vec![Term::constant("a")]));
        let interp = InitialInterpretation::Explicit {
            true_atoms: HashSet::new(),
            false_atoms: falses,
            default: TruthValue::Unknown,
        };

        let clause = Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
        let sigma = interp.semantic_falsifier(&clause);
        assert!(
            matches!(sigma, Some(_)),
            "ground false clause should have falsifier"
        );
    }

    #[test]
    fn test_semantic_falsifier_all_negative_is_most_general() {
        // Under I⁻, any all-positive clause is uniformly false; falsifier should be empty.
        let interp = InitialInterpretation::AllNegative;
        let clause = Clause::new(vec![
            Literal::pos("p", vec![Term::var("X")]),
            Literal::pos("q", vec![Term::var("X")]),
        ]);
        let sigma = interp
            .semantic_falsifier(&clause)
            .expect("expected falsifier");
        assert!(
            sigma.domain().is_empty(),
            "most general falsifier should be empty"
        );
    }

    #[test]
    fn test_semantic_falsifier_unknown_returns_none() {
        let interp = InitialInterpretation::Explicit {
            true_atoms: HashSet::new(),
            false_atoms: HashSet::new(),
            default: TruthValue::Unknown,
        };
        let clause = Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
        assert!(interp.semantic_falsifier(&clause).is_none());
    }

    #[test]
    fn test_semantic_falsifier_none_when_clause_satisfied() {
        // Under I⁻, a clause with an I-true literal is satisfied.
        let interp = InitialInterpretation::AllNegative;
        let clause = Clause::new(vec![Literal::neg("p", vec![Term::constant("a")])]);
        assert!(interp.semantic_falsifier(&clause).is_none());
    }
}
