//! Theory: a set of clauses.

use crate::syntax::Clause;
use crate::parser::Statement;

/// A theory is a set of clauses.
#[derive(Debug, Clone, Default)]
pub struct Theory {
    clauses: Vec<Clause>,
}

/// Error during theory construction.
#[derive(Debug, Clone)]
pub struct ConversionError {
    pub message: String,
}

impl Theory {
    /// Create an empty theory.
    pub fn new() -> Self {
        todo!("Theory::new implementation")
    }

    /// Create a theory from parsed statements.
    pub fn from_statements(_stmts: &[Statement]) -> Result<Self, ConversionError> {
        todo!("Theory::from_statements implementation")
    }

    /// Add a clause to the theory.
    pub fn add_clause(&mut self, clause: Clause) {
        todo!("Theory::add_clause implementation")
    }

    /// Get the clauses in this theory.
    pub fn clauses(&self) -> &[Clause] {
        &self.clauses
    }

    /// Check if this theory is stratified.
    pub fn is_stratified(&self) -> bool {
        use std::collections::{HashMap, HashSet};
        use crate::syntax::Term;

        fn term_sort(term: &Term) -> Option<&str> {
            match term {
                Term::Var(v) => v.sort(),
                Term::Const(c) => c.sort(),
                Term::App(f, _) => f.result_sort.as_deref(),
            }
        }

        fn collect_edges(
            term: &Term,
            edges: &mut HashMap<String, HashSet<String>>,
            nodes: &mut HashSet<String>,
        ) -> Result<(), ()> {
            match term {
                Term::Var(v) => {
                    if let Some(s) = v.sort() {
                        nodes.insert(s.to_string());
                        Ok(())
                    } else {
                        Err(())
                    }
                }
                Term::Const(c) => {
                    if let Some(s) = c.sort() {
                        nodes.insert(s.to_string());
                        Ok(())
                    } else {
                        Err(())
                    }
                }
                Term::App(f, args) => {
                    let result = match f.result_sort.as_deref() {
                        Some(s) => s,
                        None => return Err(()),
                    };
                    nodes.insert(result.to_string());
                    for arg in args {
                        let arg_sort = term_sort(arg).ok_or(())?;
                        nodes.insert(arg_sort.to_string());
                        edges
                            .entry(arg_sort.to_string())
                            .or_default()
                            .insert(result.to_string());
                        collect_edges(arg, edges, nodes)?;
                    }
                    Ok(())
                }
            }
        }

        let mut edges: HashMap<String, HashSet<String>> = HashMap::new();
        let mut nodes: HashSet<String> = HashSet::new();
        let mut saw_function = false;
        let mut missing_sort = false;

        for clause in &self.clauses {
            for lit in &clause.literals {
                for term in &lit.atom.args {
                    if matches!(term, Term::App(_, _)) {
                        saw_function = true;
                    }
                    if collect_edges(term, &mut edges, &mut nodes).is_err() {
                        missing_sort = true;
                    }
                }
            }
        }

        // No function symbols: stratification holds vacuously.
        if !saw_function {
            return true;
        }
        if missing_sort {
            return false;
        }

        let mut state: HashMap<&String, u8> = HashMap::new();
        fn dfs(
            node: &String,
            edges: &HashMap<String, HashSet<String>>,
            state: &mut HashMap<&String, u8>,
        ) -> bool {
            match state.get(node) {
                Some(1) => return true,  // back-edge => cycle
                Some(2) => return false, // already processed
                _ => {}
            }
            state.insert(node, 1);
            if let Some(neigh) = edges.get(node) {
                for next in neigh {
                    if dfs(next, edges, state) {
                        return true;
                    }
                }
            }
            state.insert(node, 2);
            false
        }

        for node in &nodes {
            if dfs(node, &edges, &mut state) {
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::{Clause, Literal, Term, Var};

    #[test]
    fn test_stratified_signature_acyclic() {
        // Source: SGGSdpFOL.pdf, stratified signature definition (sort graph acyclic).
        // f: s1 -> s2 yields edge s1 -> s2; acyclic => stratified.
        let x = Term::Var(Var::new_with_sort("X", "s1"));
        let fx = Term::app_with_sort("f", "s2", vec![x]);
        let clause = Clause::new(vec![Literal::pos("P", vec![fx])]);

        let mut theory = Theory::new();
        theory.add_clause(clause);
        assert!(theory.is_stratified());
    }

    #[test]
    fn test_stratified_signature_self_cycle() {
        // Source: SGGSdpFOL.pdf, stratified signature definition:
        // if s has a non-trivial path to itself, signature is not stratified.
        let x = Term::Var(Var::new_with_sort("X", "s"));
        let fx = Term::app_with_sort("f", "s", vec![x]);
        let clause = Clause::new(vec![Literal::pos("P", vec![fx])]);

        let mut theory = Theory::new();
        theory.add_clause(clause);
        assert!(!theory.is_stratified());
    }

    #[test]
    fn test_stratified_signature_two_sort_cycle() {
        // Source: SGGSdpFOL.pdf, stratified signature definition (acyclic sort graph).
        // f: s1 -> s2 and g: s2 -> s1 yields a cycle => not stratified.
        let x = Term::Var(Var::new_with_sort("X", "s1"));
        let y = Term::Var(Var::new_with_sort("Y", "s2"));

        let fx = Term::app_with_sort("f", "s2", vec![x]);
        let gy = Term::app_with_sort("g", "s1", vec![y]);

        let c1 = Clause::new(vec![Literal::pos("P", vec![fx])]);
        let c2 = Clause::new(vec![Literal::pos("Q", vec![gy])]);

        let mut theory = Theory::new();
        theory.add_clause(c1);
        theory.add_clause(c2);
        assert!(!theory.is_stratified());
    }

    #[test]
    fn test_stratified_requires_sort_annotations() {
        // Without sorts the signature cannot be checked for stratification.
        let x = Term::var("X");
        let fx = Term::app("f", vec![x]);
        let clause = Clause::new(vec![Literal::pos("P", vec![fx])]);

        let mut theory = Theory::new();
        theory.add_clause(clause);
        assert!(!theory.is_stratified());
    }
}
