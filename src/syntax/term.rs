//! First-order terms: variables and function applications (including 0-ary constants).

use std::collections::HashSet;
use std::fmt;

use crate::unify::Substitution;

/// A variable in first-order logic.
/// Variables are implicitly universally quantified and represented by capitalized names.
/// Variables may optionally carry a sort annotation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Var {
    name: String,
    sort: Option<String>,
}

impl Var {
    pub fn new(name: impl Into<String>) -> Self {
        Var {
            name: name.into(),
            sort: None,
        }
    }

    pub fn new_with_sort(name: impl Into<String>, sort: impl Into<String>) -> Self {
        Var {
            name: name.into(),
            sort: Some(sort.into()),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn sort(&self) -> Option<&str> {
        self.sort.as_deref()
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// A function symbol with its arity and optional result sort.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FnSym {
    pub name: String,
    pub arity: usize,
    pub result_sort: Option<String>,
}

impl FnSym {
    pub fn new(name: impl Into<String>, arity: usize) -> Self {
        FnSym {
            name: name.into(),
            arity,
            result_sort: None,
        }
    }

    pub fn new_with_sort(
        name: impl Into<String>,
        arity: usize,
        result_sort: impl Into<String>,
    ) -> Self {
        FnSym {
            name: name.into(),
            arity,
            result_sort: Some(result_sort.into()),
        }
    }
}

/// A first-order term.
///
/// Terms are built from variables and function applications (constants are 0-ary applications).
/// In S-expression syntax:
/// - Variables: `X`, `Y`, `Person` (capitalized)
/// - Constants (0-ary functions): `socrates`, `nil` (lowercase)
/// - Applications: `(f x y)`, `(cons a b)`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// A variable
    Var(Var),
    /// Function application: f(t1, ..., tn)
    App(FnSym, Vec<Term>),
}

impl Term {
    /// Create a variable term.
    pub fn var(name: impl Into<String>) -> Self {
        Term::Var(Var::new(name))
    }

    /// Create a constant term.
    pub fn constant(name: impl Into<String>) -> Self {
        Term::App(FnSym::new(name, 0), Vec::new())
    }

    /// Create a sorted constant term (0-ary function).
    pub fn constant_with_sort(name: impl Into<String>, sort: impl Into<String>) -> Self {
        Term::App(FnSym::new_with_sort(name, 0, sort), Vec::new())
    }

    /// Create a function application term.
    pub fn app(name: impl Into<String>, args: Vec<Term>) -> Self {
        let arity = args.len();
        Term::App(FnSym::new(name, arity), args)
    }

    /// Create a function application term with a result sort.
    pub fn app_with_sort(
        name: impl Into<String>,
        result_sort: impl Into<String>,
        args: Vec<Term>,
    ) -> Self {
        let arity = args.len();
        Term::App(FnSym::new_with_sort(name, arity, result_sort), args)
    }

    /// Collect all variables occurring in this term.
    pub fn variables(&self) -> HashSet<Var> {
        match self {
            Term::Var(var) => {
                let mut set = HashSet::new();
                set.insert(var.clone());
                set
            }
            Term::App(_, args) => {
                let mut set = HashSet::new();
                for arg in args {
                    set.extend(arg.variables());
                }
                set
            }
        }
    }

    /// Check if this term contains no variables (is ground).
    pub fn is_ground(&self) -> bool {
        match self {
            Term::Var(_) => false,
            Term::App(_, args) => args.iter().all(|arg| arg.is_ground()),
        }
    }

    /// Apply a substitution to this term.
    pub fn apply_subst(&self, subst: &Substitution) -> Term {
        subst.apply_to_term(self)
    }

    /// Get the root symbol of this term (function name or constant name).
    /// Returns None for variables.
    pub fn root_symbol(&self) -> Option<&str> {
        match self {
            Term::Var(_) => None,
            Term::App(fn_sym, _) => Some(&fn_sym.name),
        }
    }

    /// Check if a variable occurs in this term (for occurs check in unification).
    pub fn occurs(&self, var: &Var) -> bool {
        match self {
            Term::Var(v) => v == var,
            Term::App(_, args) => args.iter().any(|arg| arg.occurs(var)),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(var) => write!(f, "{}", var),
            Term::App(fn_sym, args) => {
                if args.is_empty() {
                    // Constant (0-ary function)
                    write!(f, "{}", fn_sym.name)
                } else {
                    // Function application in S-expression format
                    write!(f, "({}", fn_sym.name)?;
                    for arg in args {
                        write!(f, " {}", arg)?;
                    }
                    write!(f, ")")
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::unify::Substitution;

    fn subst(pairs: Vec<(Var, Term)>) -> Substitution {
        let mut subst = Substitution::empty();
        for (v, t) in pairs {
            subst.bind(v, t);
        }
        subst
    }

    // === Construction tests ===

    #[test]
    fn test_var_construction() {
        let v = Var::new("X");
        assert_eq!(v.name(), "X");
        assert_eq!(v.sort(), None);
    }

    #[test]
    fn test_sorted_var_construction() {
        let v = Var::new_with_sort("X", "s1");
        assert_eq!(v.name(), "X");
        assert_eq!(v.sort(), Some("s1"));
    }

    #[test]
    fn test_app_construction() {
        let term = Term::app("f", vec![Term::var("X"), Term::constant("a")]);
        match term {
            Term::App(sym, args) => {
                assert_eq!(sym.name, "f");
                assert_eq!(sym.arity, 2);
                assert_eq!(sym.result_sort, None);
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected App term"),
        }
    }

    #[test]
    fn test_const_construction_as_zero_ary_app() {
        let c = Term::constant("socrates");
        match c {
            Term::App(sym, args) => {
                assert_eq!(sym.name, "socrates");
                assert_eq!(sym.arity, 0);
                assert!(args.is_empty());
            }
            _ => panic!("Expected 0-ary App term"),
        }
    }

    #[test]
    fn test_sorted_const_construction_as_zero_ary_app() {
        let c = Term::constant_with_sort("a", "s1");
        match c {
            Term::App(sym, args) => {
                assert_eq!(sym.name, "a");
                assert_eq!(sym.arity, 0);
                assert_eq!(sym.result_sort.as_deref(), Some("s1"));
                assert!(args.is_empty());
            }
            _ => panic!("Expected 0-ary App term"),
        }
    }

    // === Root symbol tests ===

    #[test]
    fn test_root_symbol_var_none() {
        let term = Term::var("X");
        assert_eq!(term.root_symbol(), None);
    }

    #[test]
    fn test_root_symbol_const_and_app() {
        let c = Term::constant("a");
        assert_eq!(c.root_symbol(), Some("a"));
        let app = Term::app("f", vec![Term::var("X")]);
        assert_eq!(app.root_symbol(), Some("f"));
    }

    // === Occurs tests ===

    #[test]
    fn test_occurs_direct_and_nested() {
        let v = Var::new("X");
        let term = Term::app("f", vec![Term::var("X"), Term::constant("a")]);
        assert!(term.occurs(&v));
        let nested = Term::app("g", vec![term.clone()]);
        assert!(nested.occurs(&v));
    }

    #[test]
    fn test_occurs_false_when_absent() {
        let v = Var::new("X");
        let term = Term::app("f", vec![Term::var("Y")]);
        assert!(!term.occurs(&v));
    }

    // === Substitution tests ===

    #[test]
    fn test_apply_subst_recursive() {
        let term = Term::app(
            "f",
            vec![Term::var("X"), Term::app("g", vec![Term::var("Y")])],
        );
        let subst = subst(vec![
            (Var::new("X"), Term::constant("a")),
            (Var::new("Y"), Term::constant("b")),
        ]);
        let applied = term.apply_subst(&subst);
        assert_eq!(
            applied,
            Term::app(
                "f",
                vec![
                    Term::constant("a"),
                    Term::app("g", vec![Term::constant("b")])
                ]
            )
        );
    }

    // === Variables tests ===

    #[test]
    fn test_variables_collects_all() {
        let term = Term::app(
            "f",
            vec![Term::var("X"), Term::app("g", vec![Term::var("Y")])],
        );
        let vars = term.variables();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&Var::new("X")));
        assert!(vars.contains(&Var::new("Y")));
    }

    #[test]
    fn test_app_with_sort_construction() {
        let term = Term::app_with_sort("f", "s2", vec![Term::var("X"), Term::constant("a")]);
        match term {
            Term::App(sym, args) => {
                assert_eq!(sym.name, "f");
                assert_eq!(sym.arity, 2);
                assert_eq!(sym.result_sort.as_deref(), Some("s2"));
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected App term"),
        }
    }

    #[test]
    fn test_nested_term_construction() {
        // (f (g X) a)
        let inner = Term::app("g", vec![Term::var("X")]);
        let outer = Term::app("f", vec![inner, Term::constant("a")]);

        match outer {
            Term::App(sym, args) => {
                assert_eq!(sym.name, "f");
                assert_eq!(args.len(), 2);
                match &args[0] {
                    Term::App(inner_sym, _) => assert_eq!(inner_sym.name, "g"),
                    _ => panic!("Expected inner App"),
                }
            }
            _ => panic!("Expected outer App"),
        }
    }

    // === Variables extraction tests ===

    #[test]
    fn test_var_variables_returns_self() {
        let term = Term::var("X");
        let vars = term.variables();
        assert_eq!(vars.len(), 1);
        assert!(vars.contains(&Var::new("X")));
    }

    #[test]
    fn test_const_variables_returns_empty() {
        let term = Term::constant("socrates");
        let vars = term.variables();
        assert!(vars.is_empty());
    }

    #[test]
    fn test_app_variables_collects_all() {
        // (f X Y)
        let term = Term::app("f", vec![Term::var("X"), Term::var("Y")]);
        let vars = term.variables();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&Var::new("X")));
        assert!(vars.contains(&Var::new("Y")));
    }

    #[test]
    fn test_nested_term_variables() {
        // (f (g X) Y)
        let inner = Term::app("g", vec![Term::var("X")]);
        let outer = Term::app("f", vec![inner, Term::var("Y")]);
        let vars = outer.variables();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&Var::new("X")));
        assert!(vars.contains(&Var::new("Y")));
    }

    #[test]
    fn test_duplicate_variables() {
        // (f X X)
        let term = Term::app("f", vec![Term::var("X"), Term::var("X")]);
        let vars = term.variables();
        assert_eq!(vars.len(), 1);
        assert!(vars.contains(&Var::new("X")));
    }

    // === Ground check tests ===

    #[test]
    fn test_var_is_not_ground() {
        let term = Term::var("X");
        assert!(!term.is_ground());
    }

    #[test]
    fn test_const_is_ground() {
        let term = Term::constant("socrates");
        assert!(term.is_ground());
    }

    #[test]
    fn test_app_with_var_is_not_ground() {
        let term = Term::app("f", vec![Term::var("X"), Term::constant("a")]);
        assert!(!term.is_ground());
    }

    #[test]
    fn test_app_all_const_is_ground() {
        let term = Term::app("f", vec![Term::constant("a"), Term::constant("b")]);
        assert!(term.is_ground());
    }

    #[test]
    fn test_nested_with_var_not_ground() {
        // (f (g X) a) - not ground because of X
        let inner = Term::app("g", vec![Term::var("X")]);
        let outer = Term::app("f", vec![inner, Term::constant("a")]);
        assert!(!outer.is_ground());
    }

    #[test]
    fn test_nested_all_const_is_ground() {
        // (f (g a) b) - ground
        let inner = Term::app("g", vec![Term::constant("a")]);
        let outer = Term::app("f", vec![inner, Term::constant("b")]);
        assert!(outer.is_ground());
    }

    // === Substitution application tests ===

    #[test]
    fn test_subst_on_var_bound() {
        let term = Term::var("X");
        let mut subst = Substitution::empty();
        subst.bind(Var::new("X"), Term::constant("socrates"));
        let result = term.apply_subst(&subst);
        assert_eq!(result, Term::constant("socrates"));
    }

    #[test]
    fn test_subst_on_var_unbound() {
        let term = Term::var("X");
        let subst = Substitution::empty();
        let result = term.apply_subst(&subst);
        assert_eq!(result, Term::var("X"));
    }

    #[test]
    fn test_subst_on_const() {
        let term = Term::constant("socrates");
        let mut subst = Substitution::empty();
        subst.bind(Var::new("X"), Term::constant("plato"));
        let result = term.apply_subst(&subst);
        assert_eq!(result, Term::constant("socrates"));
    }

    #[test]
    fn test_subst_recursive_in_app() {
        // (f X Y) with {X -> a, Y -> b} => (f a b)
        let term = Term::app("f", vec![Term::var("X"), Term::var("Y")]);
        let subst = subst(vec![
            (Var::new("X"), Term::constant("a")),
            (Var::new("Y"), Term::constant("b")),
        ]);
        let result = term.apply_subst(&subst);
        assert_eq!(
            result,
            Term::app("f", vec![Term::constant("a"), Term::constant("b")])
        );
    }

    #[test]
    fn test_subst_nested() {
        // (f (g X) Y) with {X -> a} => (f (g a) Y)
        let inner = Term::app("g", vec![Term::var("X")]);
        let outer = Term::app("f", vec![inner, Term::var("Y")]);
        let subst = subst(vec![(Var::new("X"), Term::constant("a"))]);
        let result = outer.apply_subst(&subst);

        let expected_inner = Term::app("g", vec![Term::constant("a")]);
        let expected = Term::app("f", vec![expected_inner, Term::var("Y")]);
        assert_eq!(result, expected);
    }

    // === Occurs check tests ===

    #[test]
    fn test_occurs_var_in_self() {
        let term = Term::var("X");
        assert!(term.occurs(&Var::new("X")));
    }

    #[test]
    fn test_occurs_var_not_in_const() {
        let term = Term::constant("socrates");
        assert!(!term.occurs(&Var::new("X")));
    }

    #[test]
    fn test_occurs_var_in_nested_app() {
        // (f (g X) a)
        let inner = Term::app("g", vec![Term::var("X")]);
        let outer = Term::app("f", vec![inner, Term::constant("a")]);
        assert!(outer.occurs(&Var::new("X")));
    }

    #[test]
    fn test_occurs_var_not_present() {
        let term = Term::app("f", vec![Term::var("X"), Term::constant("a")]);
        assert!(!term.occurs(&Var::new("Y")));
    }

    // === Root symbol tests ===

    #[test]
    fn test_root_of_var_is_none() {
        let term = Term::var("X");
        assert_eq!(term.root_symbol(), None);
    }

    #[test]
    fn test_root_of_const() {
        let term = Term::constant("socrates");
        assert_eq!(term.root_symbol(), Some("socrates"));
    }

    #[test]
    fn test_root_of_app() {
        let term = Term::app("f", vec![Term::var("X")]);
        assert_eq!(term.root_symbol(), Some("f"));
    }
}
