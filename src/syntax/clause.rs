//! Clauses: disjunctions of literals in conjunctive normal form.

use std::collections::HashSet;

use crate::unify::Substitution;
use super::literal::Literal;
use super::order::AtomOrder;
use super::term::{Term, Var};

/// A clause is a disjunction of literals.
///
/// In CNF, a theory is a conjunction of clauses. Each clause represents
/// a disjunction: `L1 ∨ L2 ∨ ... ∨ Ln`.
///
/// Examples (in our syntax):
/// - Unit clause: `(human socrates)`
/// - Binary: `¬(human X) ∨ (mortal X)`
/// - Ternary: `(p X) ∨ (q X) ∨ (r X)`
/// - Empty clause: `⊥` (contradiction)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    pub literals: Vec<Literal>,
}

impl Clause {
    /// Create a clause from a vector of literals.
    pub fn new(literals: Vec<Literal>) -> Self {
        Clause { literals }
    }

    /// Create the empty clause (represents contradiction/false).
    pub fn empty() -> Self {
        Clause { literals: Vec::new() }
    }

    /// Check if this is the empty clause.
    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    /// Check if this is a unit clause (exactly one literal).
    pub fn is_unit(&self) -> bool {
        self.literals.len() == 1
    }

    /// Check if this is a Horn clause (at most one positive literal).
    pub fn is_horn(&self) -> bool {
        self.literals.iter().filter(|l| l.positive).count() <= 1
    }

    /// Collect all variables in this clause.
    pub fn variables(&self) -> HashSet<Var> {
        let mut vars = HashSet::new();
        for lit in &self.literals {
            vars.extend(lit.variables());
        }
        vars
    }

    /// Check if this clause is ground (contains no variables).
    pub fn is_ground(&self) -> bool {
        self.literals.iter().all(|l| l.is_ground())
    }

    /// Apply a substitution to this clause.
    pub fn apply_subst(&self, subst: &Substitution) -> Clause {
        Clause {
            literals: self.literals.iter().map(|l| l.apply_subst(subst)).collect(),
        }
    }

    /// Get all positive literals in this clause.
    pub fn positive_literals(&self) -> Vec<&Literal> {
        self.literals.iter().filter(|l| l.positive).collect()
    }

    /// Get all negative literals in this clause.
    pub fn negative_literals(&self) -> Vec<&Literal> {
        self.literals.iter().filter(|l| !l.positive).collect()
    }

    /// Get the number of literals in this clause.
    pub fn len(&self) -> usize {
        self.literals.len()
    }

    /// Check if this clause is positively ground-preserving (BW20 Def. 4).
    /// A clause is positively ground-preserving if every variable that appears
    /// in a positive literal also appears in some negative literal.
    pub fn is_positively_ground_preserving(&self) -> bool {
        let pos_vars: HashSet<Var> = self.positive_literals()
            .iter()
            .flat_map(|l| l.variables())
            .collect();
        let neg_vars: HashSet<Var> = self.negative_literals()
            .iter()
            .flat_map(|l| l.variables())
            .collect();
        pos_vars.is_subset(&neg_vars)
    }

    /// Check if this clause is negatively ground-preserving (BW20 Def. 4).
    /// A clause is negatively ground-preserving if every variable that appears
    /// in a negative literal also appears in some positive literal.
    pub fn is_negatively_ground_preserving(&self) -> bool {
        let pos_vars: HashSet<Var> = self.positive_literals()
            .iter()
            .flat_map(|l| l.variables())
            .collect();
        let neg_vars: HashSet<Var> = self.negative_literals()
            .iter()
            .flat_map(|l| l.variables())
            .collect();
        neg_vars.is_subset(&pos_vars)
    }

    /// Check if this clause is ground-preserving (positively or negatively).
    pub fn is_ground_preserving(&self) -> bool {
        self.is_positively_ground_preserving() || self.is_negatively_ground_preserving()
    }

    /// Check if this clause is restrained (BW20 Def. 6) under a given atom ordering.
    ///
    /// A clause is restrained if:
    /// 1. It is positively ground-preserving (Var(C+) ⊆ Var(C-))
    /// 2. Each non-ground positive literal is dominated by some negative literal
    pub fn is_restrained<O: AtomOrder>(&self, order: &O) -> bool {
        use super::order::AtomCmp;

        // Must be positively ground-preserving
        if !self.is_positively_ground_preserving() {
            return false;
        }

        let neg_lits = self.negative_literals();

        // Each non-ground positive literal must be dominated by some negative literal
        for pos_lit in self.positive_literals() {
            if pos_lit.is_ground() {
                continue; // Ground literals don't need to be dominated
            }

            // Find a dominating negative literal
            // Equal atoms satisfy the dominance condition (an atom dominates itself)
            let dominated = neg_lits.iter().any(|neg_lit| {
                matches!(order.cmp(&neg_lit.atom, &pos_lit.atom), AtomCmp::Greater | AtomCmp::Equal)
            });

            if !dominated {
                return false;
            }
        }

        true
    }

    /// Check if this clause is negatively restrained (dual of BW20 Def. 6)
    /// under a given atom ordering.
    ///
    /// A clause is negatively restrained if:
    /// 1. It is negatively ground-preserving (Var(C-) ⊆ Var(C+))
    /// 2. Each non-ground negative literal is dominated by some positive literal
    pub fn is_negatively_restrained<O: AtomOrder>(&self, order: &O) -> bool {
        use super::order::AtomCmp;

        // Must be negatively ground-preserving
        if !self.is_negatively_ground_preserving() {
            return false;
        }

        let pos_lits = self.positive_literals();

        // Each non-ground negative literal must be dominated by some positive literal
        for neg_lit in self.negative_literals() {
            if neg_lit.is_ground() {
                continue; // Ground literals don't need to be dominated
            }

            // Find a dominating positive literal
            // Equal atoms satisfy the dominance condition (an atom dominates itself)
            let dominated = pos_lits.iter().any(|pos_lit| {
                matches!(order.cmp(&pos_lit.atom, &neg_lit.atom), AtomCmp::Greater | AtomCmp::Equal)
            });

            if !dominated {
                return false;
            }
        }

        true
    }

    /// Check if this clause is in the PVD fragment (Positive Variable Depth).
    ///
    /// A clause is PVD if:
    /// 1. It is positively ground-preserving
    /// 2. For each variable X in positive literals, depth_X(C+) <= depth_X(C-)
    pub fn is_pvd(&self) -> bool {
        // Must be positively ground-preserving
        if !self.is_positively_ground_preserving() {
            return false;
        }

        // Get variables from positive literals
        let pos_vars: HashSet<Var> = self.positive_literals()
            .iter()
            .flat_map(|l| l.variables())
            .collect();

        // For each variable in positive literals, check depth constraint
        for var in pos_vars {
            let pos_depth = self.max_var_depth_in_literals(&var, true);
            let neg_depth = self.max_var_depth_in_literals(&var, false);

            // Depth in positive must not exceed depth in negative
            if pos_depth > neg_depth {
                return false;
            }
        }

        true
    }

    /// Compute the maximum depth at which a variable occurs in literals of given polarity.
    fn max_var_depth_in_literals(&self, var: &Var, positive: bool) -> usize {
        self.literals
            .iter()
            .filter(|l| l.positive == positive)
            .flat_map(|l| l.atom.args.iter())
            .map(|t| var_depth_in_term(var, t, 0))
            .max()
            .unwrap_or(0)
    }

    /// Check if this clause is sort-restrained for a given set of infinite sorts.
    ///
    /// Like restrained, but the dominance requirement only applies to variables
    /// of infinite sorts. Variables of finite sorts are not considered.
    pub fn is_sort_restrained<O: AtomOrder>(
        &self,
        infinite_sorts: &HashSet<String>,
        order: &O,
    ) -> bool {
        use super::order::AtomCmp;

        // Get variables from positive literals that have infinite sorts
        let pos_vars: HashSet<Var> = self.positive_literals()
            .iter()
            .flat_map(|l| l.variables())
            .filter(|v| v.sort().map_or(true, |s| infinite_sorts.contains(s)))
            .collect();

        // Get variables from negative literals that have infinite sorts
        let neg_vars: HashSet<Var> = self.negative_literals()
            .iter()
            .flat_map(|l| l.variables())
            .filter(|v| v.sort().map_or(true, |s| infinite_sorts.contains(s)))
            .collect();

        // Must be "sort ground-preserving": infinite-sort vars in C+ ⊆ infinite-sort vars in C-
        if !pos_vars.is_subset(&neg_vars) {
            return false;
        }

        let neg_lits = self.negative_literals();

        // Each positive literal with non-ground infinite-sort variables must be dominated
        for pos_lit in self.positive_literals() {
            // Check if this literal has any non-ground infinite-sort variables
            let has_infinite_var = pos_lit.variables().iter().any(|v| {
                v.sort().map_or(true, |s| infinite_sorts.contains(s))
            });

            if !has_infinite_var || pos_lit.is_ground() {
                continue;
            }

            // Find a dominating negative literal
            // Equal atoms satisfy the dominance condition (an atom dominates itself)
            let dominated = neg_lits.iter().any(|neg_lit| {
                matches!(order.cmp(&neg_lit.atom, &pos_lit.atom), AtomCmp::Greater | AtomCmp::Equal)
            });

            if !dominated {
                return false;
            }
        }

        true
    }

    /// Check if this clause is negatively sort-restrained for a given set of infinite sorts.
    pub fn is_sort_negatively_restrained<O: AtomOrder>(
        &self,
        infinite_sorts: &HashSet<String>,
        order: &O,
    ) -> bool {
        use super::order::AtomCmp;

        // Get variables from positive literals that have infinite sorts
        let pos_vars: HashSet<Var> = self.positive_literals()
            .iter()
            .flat_map(|l| l.variables())
            .filter(|v| v.sort().map_or(true, |s| infinite_sorts.contains(s)))
            .collect();

        // Get variables from negative literals that have infinite sorts
        let neg_vars: HashSet<Var> = self.negative_literals()
            .iter()
            .flat_map(|l| l.variables())
            .filter(|v| v.sort().map_or(true, |s| infinite_sorts.contains(s)))
            .collect();

        // Must be "sort negatively ground-preserving": infinite-sort vars in C- ⊆ infinite-sort vars in C+
        if !neg_vars.is_subset(&pos_vars) {
            return false;
        }

        let pos_lits = self.positive_literals();

        // Each negative literal with non-ground infinite-sort variables must be dominated
        for neg_lit in self.negative_literals() {
            let has_infinite_var = neg_lit.variables().iter().any(|v| {
                v.sort().map_or(true, |s| infinite_sorts.contains(s))
            });

            if !has_infinite_var || neg_lit.is_ground() {
                continue;
            }

            // Find a dominating positive literal
            // Equal atoms satisfy the dominance condition (an atom dominates itself)
            let dominated = pos_lits.iter().any(|pos_lit| {
                matches!(order.cmp(&pos_lit.atom, &neg_lit.atom), AtomCmp::Greater | AtomCmp::Equal)
            });

            if !dominated {
                return false;
            }
        }

        true
    }

    /// Check if this clause is sort-refined PVD for a given set of infinite sorts.
    ///
    /// Like PVD, but the depth constraint only applies to variables of infinite sorts.
    pub fn is_sort_refined_pvd(&self, infinite_sorts: &HashSet<String>) -> bool {
        // Get variables from positive literals that have infinite sorts
        let pos_vars: HashSet<Var> = self.positive_literals()
            .iter()
            .flat_map(|l| l.variables())
            .filter(|v| v.sort().map_or(true, |s| infinite_sorts.contains(s)))
            .collect();

        // Get variables from negative literals that have infinite sorts
        let neg_vars: HashSet<Var> = self.negative_literals()
            .iter()
            .flat_map(|l| l.variables())
            .filter(|v| v.sort().map_or(true, |s| infinite_sorts.contains(s)))
            .collect();

        // Must be "sort positively ground-preserving" for infinite sorts
        if !pos_vars.is_subset(&neg_vars) {
            return false;
        }

        // For each infinite-sort variable in positive literals, check depth constraint
        for var in pos_vars {
            let pos_depth = self.max_var_depth_in_literals(&var, true);
            let neg_depth = self.max_var_depth_in_literals(&var, false);

            if pos_depth > neg_depth {
                return false;
            }
        }

        true
    }
}

/// Compute the depth of a variable occurrence in a term.
/// Returns 0 if the variable doesn't occur in the term.
fn var_depth_in_term(var: &Var, term: &Term, current_depth: usize) -> usize {
    match term {
        Term::Var(v) if v == var => current_depth,
        Term::Var(_) => 0,
        Term::App(_, args) => {
            args.iter()
                .map(|t| var_depth_in_term(var, t, current_depth + 1))
                .max()
                .unwrap_or(0)
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
    use crate::syntax::term::Term;

    // === Construction tests ===

    #[test]
    fn test_clause_construction() {
        let lit1 = Literal::pos("p", vec![]);
        let lit2 = Literal::neg("q", vec![]);
        let clause = Clause::new(vec![lit1, lit2]);
        assert_eq!(clause.literals.len(), 2);
    }

    // === Empty clause tests ===

    #[test]
    fn test_empty_clause() {
        let empty = Clause::empty();
        assert!(empty.is_empty());
        assert_eq!(empty.literals.len(), 0);
    }

    #[test]
    fn test_non_empty_clause_not_empty() {
        let clause = Clause::new(vec![Literal::pos("p", vec![])]);
        assert!(!clause.is_empty());
    }

    // === Unit clause tests ===

    #[test]
    fn test_unit_clause() {
        let clause = Clause::new(vec![Literal::pos("p", vec![])]);
        assert!(clause.is_unit());
    }

    #[test]
    fn test_empty_clause_not_unit() {
        let clause = Clause::empty();
        assert!(!clause.is_unit());
    }

    #[test]
    fn test_binary_clause_not_unit() {
        let clause = Clause::new(vec![Literal::pos("p", vec![]), Literal::neg("q", vec![])]);
        assert!(!clause.is_unit());
    }

    // === Horn clause tests ===

    #[test]
    fn test_horn_clause_one_positive() {
        // ¬p ∨ ¬q ∨ r (one positive literal)
        let clause = Clause::new(vec![
            Literal::neg("p", vec![]),
            Literal::neg("q", vec![]),
            Literal::pos("r", vec![]),
        ]);
        assert!(clause.is_horn());
    }

    #[test]
    fn test_horn_clause_zero_positive() {
        // ¬p ∨ ¬q (goal clause, zero positive)
        let clause = Clause::new(vec![Literal::neg("p", vec![]), Literal::neg("q", vec![])]);
        assert!(clause.is_horn());
    }

    #[test]
    fn test_non_horn_multiple_positive() {
        // p ∨ q (two positive literals)
        let clause = Clause::new(vec![Literal::pos("p", vec![]), Literal::pos("q", vec![])]);
        assert!(!clause.is_horn());
    }

    #[test]
    fn test_empty_clause_is_horn() {
        let clause = Clause::empty();
        assert!(clause.is_horn()); // 0 positive literals, so Horn
    }

    // === Variables tests ===

    #[test]
    fn test_clause_variables() {
        let clause = Clause::new(vec![
            Literal::pos("p", vec![Term::var("X")]),
            Literal::neg("q", vec![Term::var("Y")]),
        ]);
        let vars = clause.variables();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&Var::new("X")));
        assert!(vars.contains(&Var::new("Y")));
    }

    #[test]
    fn test_clause_shared_variables() {
        // Variables appearing in multiple literals counted once
        let clause = Clause::new(vec![
            Literal::pos("p", vec![Term::var("X")]),
            Literal::neg("q", vec![Term::var("X")]),
        ]);
        let vars = clause.variables();
        assert_eq!(vars.len(), 1);
    }

    // === Ground tests ===

    #[test]
    fn test_clause_is_ground() {
        let ground = Clause::new(vec![Literal::pos("p", vec![Term::constant("a")])]);
        assert!(ground.is_ground());
    }

    #[test]
    fn test_clause_not_ground() {
        let nonground = Clause::new(vec![Literal::pos("p", vec![Term::var("X")])]);
        assert!(!nonground.is_ground());
    }

    #[test]
    fn test_empty_clause_is_ground() {
        let empty = Clause::empty();
        assert!(empty.is_ground());
    }

    // === Substitution tests ===

    #[test]
    fn test_clause_subst_application() {
        let clause = Clause::new(vec![
            Literal::pos("p", vec![Term::var("X")]),
            Literal::neg("q", vec![Term::var("Y")]),
        ]);
        let subst = subst(vec![
            (Var::new("X"), Term::constant("a")),
            (Var::new("Y"), Term::constant("b")),
        ]);

        let result = clause.apply_subst(&subst);
        assert_eq!(result.literals.len(), 2);
        assert_eq!(result.literals[0].atom.args[0], Term::constant("a"));
        assert_eq!(result.literals[1].atom.args[0], Term::constant("b"));
    }

    // === Positive/Negative literals extraction ===

    #[test]
    fn test_positive_literals_extraction() {
        let clause = Clause::new(vec![
            Literal::pos("p", vec![]),
            Literal::neg("q", vec![]),
            Literal::pos("r", vec![]),
        ]);
        let positive = clause.positive_literals();
        assert_eq!(positive.len(), 2);
        assert!(positive.iter().all(|l| l.positive));
    }

    #[test]
    fn test_negative_literals_extraction() {
        let clause = Clause::new(vec![
            Literal::pos("p", vec![]),
            Literal::neg("q", vec![]),
            Literal::neg("r", vec![]),
        ]);
        let negative = clause.negative_literals();
        assert_eq!(negative.len(), 2);
        assert!(negative.iter().all(|l| !l.positive));
    }

    #[test]
    fn test_positive_literals_empty_when_none() {
        let clause = Clause::new(vec![Literal::neg("p", vec![]), Literal::neg("q", vec![])]);
        let positive = clause.positive_literals();
        assert!(positive.is_empty());
    }
}
