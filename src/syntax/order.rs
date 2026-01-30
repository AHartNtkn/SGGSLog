//! Atom ordering for restrained fragment checks.

use super::literal::Atom;

/// Comparison result for a quasi-order on atoms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtomCmp {
    Less,
    Equal,
    Greater,
    Incomparable,
}

impl AtomCmp {
    /// Returns true if this comparison is >= (greater or equal).
    pub fn ge(self) -> bool {
        matches!(self, AtomCmp::Greater | AtomCmp::Equal)
    }
}

/// Trait for a (quasi-)ordering on atoms.
///
/// The restrained fragment definition uses a quasi-ordering with the subterm property.
pub trait AtomOrder {
    fn cmp(&self, a: &Atom, b: &Atom) -> AtomCmp;
}
