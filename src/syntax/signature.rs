//! Signature (symbols) for formulas and clauses.

use std::collections::HashSet;

use super::{Clause, Term};

/// Predicate signature (name, arity, optional argument sorts).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PredSig {
    pub name: String,
    pub arity: usize,
    pub arg_sorts: Vec<Option<String>>,
}

/// Function symbol signature (name, arity, optional result sort).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FnSig {
    pub name: String,
    pub arity: usize,
    pub result_sort: Option<String>,
}

/// Constant signature (name, optional sort).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstSig {
    pub name: String,
    pub sort: Option<String>,
}

/// Signature of a theory or input fragment.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Signature {
    pub predicates: HashSet<PredSig>,
    pub functions: HashSet<FnSig>,
    pub constants: HashSet<ConstSig>,
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
            let arg_sorts = lit
                .atom
                .args
                .iter()
                .map(term_sort)
                .collect::<Vec<_>>();
            sig.predicates.insert(PredSig {
                name: lit.atom.predicate.clone(),
                arity: lit.atom.args.len(),
                arg_sorts,
            });
            for arg in &lit.atom.args {
                collect_term_symbols(arg, &mut sig);
            }
        }
        sig
    }

    /// True if any predicate with this name exists.
    pub fn contains_predicate_name(&self, name: &str) -> bool {
        self.predicates.iter().any(|p| p.name == name)
    }

    /// True if any function with this name exists.
    pub fn contains_function_name(&self, name: &str) -> bool {
        self.functions.iter().any(|f| f.name == name)
    }

    /// True if a function with this name and arity exists.
    pub fn contains_function(&self, name: &str, arity: usize) -> bool {
        self.functions
            .iter()
            .any(|f| f.name == name && f.arity == arity)
    }

    /// True if a predicate with this name and arity exists.
    pub fn contains_predicate(&self, name: &str, arity: usize) -> bool {
        self.predicates
            .iter()
            .any(|p| p.name == name && p.arity == arity)
    }

    /// True if any constant with this name exists.
    pub fn contains_constant_name(&self, name: &str) -> bool {
        self.constants.iter().any(|c| c.name == name)
    }

    /// True if the name is allowed as a 0-ary function (constant).
    pub fn allows_zero_ary_function(&self, name: &str) -> bool {
        self.functions.iter().any(|f| f.name == name && f.arity == 0)
            || self.constants.iter().any(|c| c.name == name)
    }
}

fn term_sort(term: &Term) -> Option<String> {
    match term {
        Term::Var(v) => v.sort().map(|s| s.to_string()),
        Term::Const(c) => c.sort().map(|s| s.to_string()),
        Term::App(sym, _) => sym.result_sort.clone(),
    }
}

fn collect_term_symbols(term: &Term, sig: &mut Signature) {
    match term {
        Term::Var(_) => {}
        Term::Const(c) => {
            sig.constants.insert(ConstSig {
                name: c.name().to_string(),
                sort: c.sort().map(|s| s.to_string()),
            });
            sig.functions.insert(FnSig {
                name: c.name().to_string(),
                arity: 0,
                result_sort: c.sort().map(|s| s.to_string()),
            });
        }
        Term::App(sym, args) => {
            sig.functions.insert(FnSig {
                name: sym.name.clone(),
                arity: sym.arity,
                result_sort: sym.result_sort.clone(),
            });
            for a in args {
                collect_term_symbols(a, sig);
            }
        }
    }
}

/// Signature of user-provided symbols (pre-normalization).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UserSignature {
    inner: Signature,
}

impl UserSignature {
    pub fn empty() -> Self {
        UserSignature {
            inner: Signature::empty(),
        }
    }

    pub fn from_signature(sig: Signature) -> Self {
        UserSignature { inner: sig }
    }

    pub fn signature(&self) -> &Signature {
        &self.inner
    }

    pub fn signature_mut(&mut self) -> &mut Signature {
        &mut self.inner
    }

    pub fn extend(&mut self, other: &Signature) {
        self.inner.extend(other);
    }

    pub fn contains_predicate_name(&self, name: &str) -> bool {
        self.inner.contains_predicate_name(name)
    }

    pub fn contains_function_name(&self, name: &str) -> bool {
        self.inner.contains_function_name(name)
    }

    pub fn contains_constant_name(&self, name: &str) -> bool {
        self.inner.contains_constant_name(name)
    }

    pub fn contains_function(&self, name: &str, arity: usize) -> bool {
        self.inner.contains_function(name, arity)
    }

    pub fn contains_predicate(&self, name: &str, arity: usize) -> bool {
        self.inner.contains_predicate(name, arity)
    }

    pub fn allows_zero_ary_function(&self, name: &str) -> bool {
        self.inner.allows_zero_ary_function(name)
    }

    pub fn insert_constant(&mut self, name: &str, sort: Option<&str>) {
        let sort = sort.map(|s| s.to_string());
        self.inner.constants.insert(ConstSig {
            name: name.to_string(),
            sort: sort.clone(),
        });
        self.inner.functions.insert(FnSig {
            name: name.to_string(),
            arity: 0,
            result_sort: sort,
        });
    }

    pub fn insert_function(&mut self, name: &str, arity: usize, result_sort: Option<&str>) {
        self.inner.functions.insert(FnSig {
            name: name.to_string(),
            arity,
            result_sort: result_sort.map(|s| s.to_string()),
        });
    }
}
