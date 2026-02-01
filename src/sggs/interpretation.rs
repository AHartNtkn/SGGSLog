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
        match self {
            InitialInterpretation::AllPositive => {
                // All atoms are true in I+
                // Positive literal = atom, so true
                // Negative literal = not(atom), so false
                if lit.positive {
                    TruthValue::True
                } else {
                    TruthValue::False
                }
            }
            InitialInterpretation::AllNegative => {
                // All atoms are false in I-
                // Positive literal = atom, so false
                // Negative literal = not(atom), so true
                if lit.positive {
                    TruthValue::False
                } else {
                    TruthValue::True
                }
            }
            InitialInterpretation::Explicit { true_atoms, false_atoms, default } => {
                // Check if the atom is in true_atoms or false_atoms
                let atom = &lit.atom;
                if true_atoms.contains(atom) {
                    // Atom is true, so positive literal is true, negative is false
                    if lit.positive {
                        TruthValue::True
                    } else {
                        TruthValue::False
                    }
                } else if false_atoms.contains(atom) {
                    // Atom is false, so positive literal is false, negative is true
                    if lit.positive {
                        TruthValue::False
                    } else {
                        TruthValue::True
                    }
                } else {
                    // Use default for the atom
                    match default {
                        TruthValue::True => {
                            if lit.positive {
                                TruthValue::True
                            } else {
                                TruthValue::False
                            }
                        }
                        TruthValue::False => {
                            if lit.positive {
                                TruthValue::False
                            } else {
                                TruthValue::True
                            }
                        }
                        TruthValue::Unknown => TruthValue::Unknown,
                    }
                }
            }
        }
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
    pub fn atom_is_true(&self, atom: &Atom) -> bool {
        match self {
            InitialInterpretation::AllPositive => true,
            InitialInterpretation::AllNegative => false,
            InitialInterpretation::Explicit { true_atoms, false_atoms, default } => {
                if true_atoms.contains(atom) {
                    true
                } else if false_atoms.contains(atom) {
                    false
                } else {
                    matches!(default, TruthValue::True)
                }
            }
        }
    }

    /// Attempt to compute a semantic falsifier for a clause in this interpretation.
    ///
    /// Returns a substitution that makes the clause false in I, if one is known.
    /// For uniform interpretations (AllPositive/AllNegative), returns the empty
    /// substitution if all literals are uniformly false under I.
    /// For explicit interpretations, returns None if any literal's truth is Unknown.
    pub fn semantic_falsifier(&self, clause: &Clause) -> Option<Substitution> {
        // A clause is false in I if all its literals are false in I.
        // For uniform interpretations:
        // - AllNegative: positive literals are false, negative literals are true
        // - AllPositive: negative literals are false, positive literals are true
        //
        // The semantic falsifier is a substitution σ such that σ(clause) is false in I.
        // For uniformly false clauses, the most general falsifier is the empty substitution.

        match self {
            InitialInterpretation::AllNegative => {
                // All positive literals are false under I-.
                // If the clause has only positive literals, it's uniformly false.
                // If the clause has any negative literal, it has a true literal.
                if clause.literals.iter().all(|lit| lit.positive) {
                    // All literals are positive, hence all false under I-.
                    // The empty substitution is the most general falsifier.
                    Some(Substitution::empty())
                } else {
                    // There's a negative literal which is true under I-
                    None
                }
            }
            InitialInterpretation::AllPositive => {
                // All negative literals are false under I+.
                // If the clause has only negative literals, it's uniformly false.
                if clause.literals.iter().all(|lit| !lit.positive) {
                    // All literals are negative, hence all false under I+.
                    Some(Substitution::empty())
                } else {
                    // There's a positive literal which is true under I+
                    None
                }
            }
            InitialInterpretation::Explicit { true_atoms, false_atoms, default } => {
                // For explicit interpretation, we need all literals to be ground and false.
                // If any literal's truth is Unknown, we cannot determine a falsifier.
                for lit in &clause.literals {
                    // Literal must be ground for explicit evaluation
                    if !lit.is_ground() {
                        return None;
                    }
                    let atom = &lit.atom;
                    let atom_truth = if true_atoms.contains(atom) {
                        TruthValue::True
                    } else if false_atoms.contains(atom) {
                        TruthValue::False
                    } else {
                        *default
                    };

                    let lit_truth = match atom_truth {
                        TruthValue::True => {
                            if lit.positive { TruthValue::True } else { TruthValue::False }
                        }
                        TruthValue::False => {
                            if lit.positive { TruthValue::False } else { TruthValue::True }
                        }
                        TruthValue::Unknown => TruthValue::Unknown,
                    };

                    match lit_truth {
                        TruthValue::True => return None, // Clause is satisfied
                        TruthValue::Unknown => return None, // Cannot determine
                        TruthValue::False => continue, // This literal is false, check others
                    }
                }
                // All literals are false under this interpretation
                Some(Substitution::empty())
            }
        }
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

    #[test]
    fn test_semantic_falsifier_all_positive_all_negative_clause() {
        // Under I⁺, an all-negative clause is uniformly false; falsifier should be empty.
        let interp = InitialInterpretation::AllPositive;
        let clause = Clause::new(vec![Literal::neg("p", vec![Term::var("X")])]);
        let sigma = interp
            .semantic_falsifier(&clause)
            .expect("expected falsifier");
        assert!(sigma.domain().is_empty());
    }
}
