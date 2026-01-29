//! Initial interpretation for SGGS semantic guidance.

use crate::syntax::{Atom, Literal};

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
}

impl Default for InitialInterpretation {
    fn default() -> Self {
        InitialInterpretation::AllNegative
    }
}

impl InitialInterpretation {
    /// Is this ground literal true in I?
    pub fn is_true(&self, lit: &Literal) -> bool {
        todo!("InitialInterpretation::is_true implementation")
    }

    /// Is this ground literal false in I?
    pub fn is_false(&self, lit: &Literal) -> bool {
        todo!("InitialInterpretation::is_false implementation")
    }

    /// Is this ground atom true in I?
    pub fn atom_is_true(&self, _atom: &Atom) -> bool {
        todo!("InitialInterpretation::atom_is_true implementation")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::{Literal, Term};

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
}
