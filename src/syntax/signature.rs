//! Signature (user-visible symbols) for formulas and clauses.

use std::collections::HashSet;

use super::{Clause, Term};

/// Signature of a theory or input fragment.
///
/// Predicates are collected from atoms; constants are 0-ary function symbols.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Signature {
    pub predicates: HashSet<String>,
    pub functions: HashSet<String>,
    pub constants: HashSet<String>,
}

impl Signature {
    pub fn empty() -> Self {
        Signature::default()
    }

    /// Merge another signature into this one.
    pub fn extend(&mut self, other: &Signature) {
        self.predicates.extend(other.predicates.iter().cloned());
        self.functions.extend(other.functions.iter().cloned());
        self.constants.extend(other.constants.iter().cloned());
    }

    /// Collect symbols from a clause.
    pub fn from_clause(clause: &Clause) -> Signature {
        let mut sig = Signature::empty();
        for lit in &clause.literals {
            sig.predicates.insert(lit.atom.predicate.clone());
            for arg in &lit.atom.args {
                collect_term_symbols(arg, &mut sig);
            }
        }
        sig
    }
}

fn collect_term_symbols(term: &Term, sig: &mut Signature) {
    match term {
        Term::Var(_) => {}
        Term::Const(c) => {
            sig.constants.insert(c.name().to_string());
            // Treat constants as 0-ary function symbols as well.
            sig.functions.insert(c.name().to_string());
        }
        Term::App(sym, args) => {
            sig.functions.insert(sym.name.clone());
            for a in args {
                collect_term_symbols(a, sig);
            }
        }
    }
}
