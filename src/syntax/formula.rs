//! Formula syntax for first-order logic (surface syntax).

use super::literal::Atom;
use super::term::Var;

/// A first-order formula as written in the surface language.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    Atom(Atom),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Forall(Var, Box<Formula>),
    Exists(Var, Box<Formula>),
}

impl Formula {
    pub fn atom(atom: Atom) -> Self {
        Formula::Atom(atom)
    }

    pub fn negation(inner: Formula) -> Self {
        Formula::Not(Box::new(inner))
    }

    pub fn and(left: Formula, right: Formula) -> Self {
        Formula::And(Box::new(left), Box::new(right))
    }

    pub fn or(left: Formula, right: Formula) -> Self {
        Formula::Or(Box::new(left), Box::new(right))
    }

    pub fn implies(left: Formula, right: Formula) -> Self {
        Formula::Implies(Box::new(left), Box::new(right))
    }

    pub fn forall(var: Var, body: Formula) -> Self {
        Formula::Forall(var, Box::new(body))
    }

    pub fn exists(var: Var, body: Formula) -> Self {
        Formula::Exists(var, Box::new(body))
    }
}
