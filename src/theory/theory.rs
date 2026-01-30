//! Theory: a set of clauses.

use crate::normalize::clausify_statement;
use crate::parser::Statement;
use crate::syntax::{Atom, Clause, Signature};

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

/// A rewrite rule for restraining systems (L -> M on atoms).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RewriteRule {
    pub lhs: crate::syntax::Atom,
    pub rhs: crate::syntax::Atom,
}

/// A restraining system (RS, ES) as in SGGSdpFOL.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RestrainingSystem {
    pub rs: Vec<RewriteRule>,
    pub es: Vec<RewriteRule>,
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

    /// Compute the signature of this theory.
    pub fn signature(&self) -> Signature {
        let mut sig = Signature::empty();
        for clause in &self.clauses {
            sig.extend(&Signature::from_clause(clause));
        }
        sig
    }

    /// Check if every clause is ground-preserving.
    pub fn is_ground_preserving(&self) -> bool {
        self.clauses.iter().all(|c| c.is_ground_preserving())
    }

    /// Check if every clause is restrained.
    pub fn is_restrained<O: crate::syntax::AtomOrder>(&self, order: &O) -> bool {
        self.clauses.iter().all(|c| c.is_restrained(order))
    }

    /// Check if every clause is negatively restrained.
    pub fn is_negatively_restrained<O: crate::syntax::AtomOrder>(&self, order: &O) -> bool {
        self.clauses
            .iter()
            .all(|c| c.is_negatively_restrained(order))
    }

    /// Check if every clause is in the PVD fragment.
    pub fn is_pvd(&self) -> bool {
        self.clauses.iter().all(|c| c.is_pvd())
    }

    /// Check if every clause is sort-restrained for the given set of infinite sorts.
    pub fn is_sort_restrained<O: crate::syntax::AtomOrder>(
        &self,
        infinite_sorts: &std::collections::HashSet<String>,
        order: &O,
    ) -> bool {
        self.clauses
            .iter()
            .all(|c| c.is_sort_restrained(infinite_sorts, order))
    }

    /// Check if every clause is negatively sort-restrained for the given set of infinite sorts.
    pub fn is_sort_negatively_restrained<O: crate::syntax::AtomOrder>(
        &self,
        infinite_sorts: &std::collections::HashSet<String>,
        order: &O,
    ) -> bool {
        self.clauses
            .iter()
            .all(|c| c.is_sort_negatively_restrained(infinite_sorts, order))
    }

    /// Check if every clause is sort-refined PVD for the given set of infinite sorts.
    pub fn is_sort_refined_pvd(&self, infinite_sorts: &std::collections::HashSet<String>) -> bool {
        self.clauses
            .iter()
            .all(|c| c.is_sort_refined_pvd(infinite_sorts))
    }

    /// Check if this theory is in EPR (no function symbols of arity > 0).
    pub fn is_epr(&self) -> bool {
        use crate::syntax::Term;
        for clause in &self.clauses {
            for lit in &clause.literals {
                for term in &lit.atom.args {
                    let mut stack = vec![term];
                    while let Some(t) = stack.pop() {
                        if let Term::App(sym, args) = t {
                            if sym.arity > 0 {
                                return false;
                            }
                            for a in args {
                                stack.push(a);
                            }
                        }
                    }
                }
            }
        }
        true
    }

    /// Check if this theory is in the BDI fragment.
    pub fn is_bdi(&self) -> bool {
        todo!("Theory::is_bdi implementation")
    }

    /// Check if this theory is stratified.
    pub fn is_stratified(&self) -> bool {
        use crate::syntax::Term;
        use std::collections::{HashMap, HashSet};

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

        let mut state: HashMap<String, u8> = HashMap::new();
        fn dfs(
            node: &str,
            edges: &HashMap<String, HashSet<String>>,
            state: &mut HashMap<String, u8>,
        ) -> bool {
            match state.get(node) {
                Some(1) => return true,  // back-edge => cycle
                Some(2) => return false, // already processed
                _ => {}
            }
            state.insert(node.to_string(), 1);
            if let Some(neigh) = edges.get(node) {
                for next in neigh {
                    if dfs(next, edges, state) {
                        return true;
                    }
                }
            }
            state.insert(node.to_string(), 2);
            false
        }

        for node in &nodes {
            if dfs(node, &edges, &mut state) {
                return false;
            }
        }
        true
    }

    /// Check whether a restraining system is valid for this theory.
    pub fn is_restraining_system(&self, _system: &RestrainingSystem) -> bool {
        todo!("Theory::is_restraining_system implementation")
    }

    /// Compute the atom basis for this theory under a restraining system.
    pub fn basis(&self, _system: &RestrainingSystem) -> std::collections::HashSet<Atom> {
        todo!("Theory::basis implementation")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::{Atom, Clause, Literal, Term, Var};

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

    #[test]
    fn test_signature_collects_predicates_and_symbols() {
        let mut theory = Theory::new();
        theory.add_clause(Clause::new(vec![Literal::pos(
            "P",
            vec![Term::app("f", vec![Term::constant("a")])],
        )]));
        let sig = theory.signature();
        assert!(sig.predicates.contains("P"));
        assert!(sig.functions.contains("f"));
        assert!(sig.constants.contains("a"));
    }

    #[test]
    fn test_basis_for_ground_theory_is_self() {
        let mut theory = Theory::new();
        let c1 = Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
        let c2 = Clause::new(vec![Literal::neg("q", vec![Term::constant("b")])]);
        theory.add_clause(c1.clone());
        theory.add_clause(c2.clone());
        let system = RestrainingSystem::default();
        let basis = theory.basis(&system);
        assert!(basis.contains(&Atom::new("p", vec![Term::constant("a")])));
        assert!(basis.contains(&Atom::new("q", vec![Term::constant("b")])));
        assert_eq!(basis.len(), 2);
    }

    #[test]
    fn test_empty_system_restrains_ground_theory() {
        let mut theory = Theory::new();
        theory.add_clause(Clause::new(vec![Literal::pos(
            "p",
            vec![Term::constant("a")],
        )]));
        let system = RestrainingSystem::default();
        assert!(theory.is_restraining_system(&system));
    }

    #[test]
    fn test_restraining_system_requires_rule_for_non_ground_positive() {
        // Source: SGGSdpFOL Definition 15 (Restraining system):
        // for every non-ground L in C+, there exists ¬M in C- with (M -> L) in RS or (M ~ L) in ES.
        // Clause: ¬P(f(x)) ∨ P(x). Positive literal P(x) is non-ground.
        // System is restraining if it contains rule P(f(x)) -> P(x).
        let mut theory = Theory::new();
        let clause = Clause::new(vec![
            Literal::neg("P", vec![Term::app("f", vec![Term::var("x")])]),
            Literal::pos("P", vec![Term::var("x")]),
        ]);
        theory.add_clause(clause);

        let mut system = RestrainingSystem::default();
        system.rs.push(RewriteRule {
            lhs: Atom::new("P", vec![Term::app("f", vec![Term::var("x")])]),
            rhs: Atom::new("P", vec![Term::var("x")]),
        });

        assert!(theory.is_restraining_system(&system));
    }

    #[test]
    fn test_restraining_system_fails_without_rule() {
        // Source: SGGSdpFOL Definition 15 (Restraining system).
        let mut theory = Theory::new();
        let clause = Clause::new(vec![
            Literal::neg("P", vec![Term::app("f", vec![Term::var("x")])]),
            Literal::pos("P", vec![Term::var("x")]),
        ]);
        theory.add_clause(clause);
        let system = RestrainingSystem::default();
        assert!(!theory.is_restraining_system(&system));
    }

    #[test]
    fn test_restraining_system_accepts_equation() {
        // Source: SGGSdpFOL Definition 15 (Restraining system), equations in ES.
        // Clause: ¬P(y,x) ∨ P(x,y). Equation P(x,y) ~ P(y,x) suffices.
        let mut theory = Theory::new();
        let clause = Clause::new(vec![
            Literal::neg("P", vec![Term::var("y"), Term::var("x")]),
            Literal::pos("P", vec![Term::var("x"), Term::var("y")]),
        ]);
        theory.add_clause(clause);

        let mut system = RestrainingSystem::default();
        system.es.push(RewriteRule {
            lhs: Atom::new("P", vec![Term::var("x"), Term::var("y")]),
            rhs: Atom::new("P", vec![Term::var("y"), Term::var("x")]),
        });
        assert!(theory.is_restraining_system(&system));
    }

    #[test]
    fn test_restraining_system_matches_alpha_equivalent_rule() {
        // Source: SGGSdpFOL Definition 15 (Restraining system), rules up to renaming.
        let mut theory = Theory::new();
        let clause = Clause::new(vec![
            Literal::neg("P", vec![Term::app("f", vec![Term::var("y")])]),
            Literal::pos("P", vec![Term::var("y")]),
        ]);
        theory.add_clause(clause);

        let mut system = RestrainingSystem::default();
        system.rs.push(RewriteRule {
            lhs: Atom::new("P", vec![Term::app("f", vec![Term::var("x")])]),
            rhs: Atom::new("P", vec![Term::var("x")]),
        });
        assert!(
            theory.is_restraining_system(&system),
            "rule should match modulo variable renaming"
        );
    }

    #[test]
    fn test_restraining_system_requires_rules_for_all_non_ground_positive_literals() {
        // If a clause has multiple non-ground positive literals, each must be restrained.
        // Source: SGGSdpFOL.pdf, Definition 15 (Restraining system).
        let mut theory = Theory::new();
        let clause = Clause::new(vec![
            Literal::neg("P", vec![Term::var("x")]),
            Literal::pos("Q", vec![Term::var("x")]),
            Literal::pos("R", vec![Term::var("x")]),
        ]);
        theory.add_clause(clause);

        let mut system = RestrainingSystem::default();
        system.rs.push(RewriteRule {
            lhs: Atom::new("P", vec![Term::var("x")]),
            rhs: Atom::new("Q", vec![Term::var("x")]),
        });

        assert!(
            !theory.is_restraining_system(&system),
            "missing rule for R(x) should fail restraining check"
        );
    }

    #[test]
    fn test_restraining_system_rule_must_match_negative_literal() {
        // Rule must be induced by a negative literal in the same clause.
        // Source: SGGSdpFOL.pdf, Definition 15 (Restraining system).
        let mut theory = Theory::new();
        let clause = Clause::new(vec![
            Literal::neg("P", vec![Term::var("x")]),
            Literal::pos("Q", vec![Term::var("x")]),
        ]);
        theory.add_clause(clause);

        let mut system = RestrainingSystem::default();
        system.rs.push(RewriteRule {
            lhs: Atom::new("R", vec![Term::var("x")]),
            rhs: Atom::new("Q", vec![Term::var("x")]),
        });

        assert!(
            !theory.is_restraining_system(&system),
            "rule must be induced by a negative literal of the clause"
        );
    }

    #[test]
    fn test_basis_respects_rewrite_closure() {
        // Source: SGGSdpFOL Definition 7 (Basis for a restrained set).
        // If P(f(a)) occurs and RS has P(f(x)) -> P(x), basis includes P(a) and P(f(a)).
        let mut theory = Theory::new();
        theory.add_clause(Clause::new(vec![Literal::pos(
            "P",
            vec![Term::app("f", vec![Term::constant("a")])],
        )]));
        let mut system = RestrainingSystem::default();
        system.rs.push(RewriteRule {
            lhs: Atom::new("P", vec![Term::app("f", vec![Term::var("x")])]),
            rhs: Atom::new("P", vec![Term::var("x")]),
        });
        let basis = theory.basis(&system);
        assert!(basis.contains(&Atom::new(
            "P",
            vec![Term::app("f", vec![Term::constant("a")])]
        )));
        assert!(basis.contains(&Atom::new("P", vec![Term::constant("a")])));
        assert!(!basis.contains(&Atom::new(
            "P",
            vec![Term::app(
                "f",
                vec![Term::app("f", vec![Term::constant("a")])]
            )]
        )));
    }

    #[test]
    fn test_basis_rewrite_closure_multiple_steps() {
        // If P(f(f(a))) occurs and RS has P(f(x)) -> P(x),
        // basis should include P(f(f(a))), P(f(a)), and P(a).
        // Source: SGGSdpFOL.pdf, Definition 7 (Basis for restrained set).
        let mut theory = Theory::new();
        theory.add_clause(Clause::new(vec![Literal::pos(
            "P",
            vec![Term::app(
                "f",
                vec![Term::app("f", vec![Term::constant("a")])],
            )],
        )]));
        let mut system = RestrainingSystem::default();
        system.rs.push(RewriteRule {
            lhs: Atom::new("P", vec![Term::app("f", vec![Term::var("x")])]),
            rhs: Atom::new("P", vec![Term::var("x")]),
        });
        let basis = theory.basis(&system);
        assert!(basis.contains(&Atom::new(
            "P",
            vec![Term::app(
                "f",
                vec![Term::app("f", vec![Term::constant("a")])]
            )]
        )));
        assert!(basis.contains(&Atom::new(
            "P",
            vec![Term::app("f", vec![Term::constant("a")])]
        )));
        assert!(basis.contains(&Atom::new("P", vec![Term::constant("a")])));
    }
}
