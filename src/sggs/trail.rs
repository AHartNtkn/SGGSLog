//! SGGS trail (clause sequence) for model representation.

use super::constrained::ConstrainedClause;
use super::interpretation::InitialInterpretation;
use crate::constraint::{AtomicConstraint, Constraint};
use crate::syntax::Literal;
use crate::theory::Theory;
use crate::unify::Substitution;

/// Apply a substitution to a constraint (transforming all terms within).
fn apply_subst_to_constraint(constraint: &Constraint, subst: &Substitution) -> Constraint {
    match constraint {
        Constraint::True => Constraint::True,
        Constraint::False => Constraint::False,
        Constraint::Atomic(atomic) => {
            Constraint::Atomic(apply_subst_to_atomic(atomic, subst))
        }
        Constraint::And(left, right) => {
            let left_new = apply_subst_to_constraint(left, subst);
            let right_new = apply_subst_to_constraint(right, subst);
            Constraint::And(Box::new(left_new), Box::new(right_new))
        }
        Constraint::Or(left, right) => {
            let left_new = apply_subst_to_constraint(left, subst);
            let right_new = apply_subst_to_constraint(right, subst);
            Constraint::Or(Box::new(left_new), Box::new(right_new))
        }
        Constraint::Not(inner) => {
            let inner_new = apply_subst_to_constraint(inner, subst);
            Constraint::Not(Box::new(inner_new))
        }
    }
}

/// Apply a substitution to an atomic constraint.
fn apply_subst_to_atomic(atomic: &AtomicConstraint, subst: &Substitution) -> AtomicConstraint {
    match atomic {
        AtomicConstraint::Identical(t1, t2) => {
            AtomicConstraint::Identical(
                subst.apply_to_term(t1),
                subst.apply_to_term(t2),
            )
        }
        AtomicConstraint::NotIdentical(t1, t2) => {
            AtomicConstraint::NotIdentical(
                subst.apply_to_term(t1),
                subst.apply_to_term(t2),
            )
        }
        AtomicConstraint::RootEquals(t, s) => {
            AtomicConstraint::RootEquals(
                subst.apply_to_term(t),
                s.clone(),
            )
        }
        AtomicConstraint::RootNotEquals(t, s) => {
            AtomicConstraint::RootNotEquals(
                subst.apply_to_term(t),
                s.clone(),
            )
        }
    }
}

/// The SGGS trail (clause sequence).
///
/// A trail Γ = C₁[L₁], ..., Cₙ[Lₙ] represents a candidate partial model.
/// Each clause has a selected literal that contributes to the interpretation.
#[derive(Debug, Clone)]
pub struct Trail {
    clauses: Vec<ConstrainedClause>,
    initial_interp: InitialInterpretation,
}

/// Error when validating a clause against SGGS trail invariants.
#[derive(Debug, Clone)]
pub struct TrailError {
    pub message: String,
}

impl std::fmt::Display for TrailError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for TrailError {}

/// The interpretation induced by a trail.
pub struct TrailInterpretation<'a> {
    trail: &'a Trail,
}

/// The partial interpretation I^p induced by a trail.
pub struct PartialInterpretation<'a> {
    trail: &'a Trail,
}

impl Trail {
    /// Create an empty trail with the given initial interpretation.
    pub fn new(interp: InitialInterpretation) -> Self {
        Trail {
            clauses: Vec::new(),
            initial_interp: interp,
        }
    }

    /// Get the number of clauses in the trail.
    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    /// Check if the trail is empty.
    pub fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }

    /// Add a clause to the trail.
    pub fn push(&mut self, clause: ConstrainedClause) {
        self.clauses.push(clause);
    }

    /// Remove a clause at the given index from the trail and return it.
    pub fn remove_clause(&mut self, idx: usize) -> ConstrainedClause {
        self.clauses.remove(idx)
    }

    /// Insert a clause at the given index in the trail.
    pub fn insert_clause(&mut self, idx: usize, clause: ConstrainedClause) {
        self.clauses.insert(idx, clause);
    }

    /// Add a clause to the trail after validating SGGS invariants.
    /// The main invariant: if a clause has I-false literals, one must be selected.
    pub fn push_checked(&mut self, clause: ConstrainedClause) -> Result<(), TrailError> {
        // Check that the selected literal is I-false if there are I-false literals
        let selected = clause.selected_literal();
        let selected_is_i_false = self.initial_interp.is_false(selected);

        // Check if there are any I-false literals in the clause
        let has_i_false = clause.clause.literals.iter()
            .any(|lit| self.initial_interp.is_false(lit));

        if has_i_false && !selected_is_i_false {
            return Err(TrailError {
                message: "Selected literal must be I-false when I-false literals exist".to_string(),
            });
        }

        self.clauses.push(clause);
        Ok(())
    }

    /// Get a prefix of this trail.
    pub fn prefix(&self, len: usize) -> Trail {
        Trail {
            clauses: self.clauses[..len.min(self.clauses.len())].to_vec(),
            initial_interp: self.initial_interp.clone(),
        }
    }

    /// Get the interpretation induced by this trail.
    pub fn interpretation(&self) -> TrailInterpretation {
        TrailInterpretation { trail: self }
    }

    /// Get the partial interpretation I^p induced by this trail.
    pub fn partial_interpretation(&self) -> PartialInterpretation {
        PartialInterpretation { trail: self }
    }

    /// Compute the length of the disjoint prefix.
    /// The disjoint prefix is the maximal prefix where no two selected literals
    /// have overlapping constrained ground instances (atoms unify regardless of polarity).
    pub fn disjoint_prefix_length(&self) -> usize {
        use crate::unify::{unify_many, UnifyResult};

        for i in 1..self.clauses.len() {
            let lit_i = self.clauses[i].selected_literal();

            // Check if lit_i's atom can unify with any selected literal's atom in clauses 0..i
            for j in 0..i {
                let lit_j = self.clauses[j].selected_literal();

                // Check if the atoms have the same predicate (regardless of polarity)
                if lit_i.atom.predicate == lit_j.atom.predicate &&
                   lit_i.atom.args.len() == lit_j.atom.args.len() {
                    // Try to unify the argument lists
                    let pairs: Vec<_> = lit_i.atom.args.iter()
                        .zip(lit_j.atom.args.iter())
                        .map(|(a, b)| (a.clone(), b.clone()))
                        .collect();
                    let result = unify_many(&pairs);
                    if let UnifyResult::Success(mgu) = result {
                        // Apply the MGU to both constraints and check intersection
                        let c_i = apply_subst_to_constraint(&self.clauses[i].constraint, &mgu);
                        let c_j = apply_subst_to_constraint(&self.clauses[j].constraint, &mgu);
                        // Check if the constrained instances overlap after applying the unifier
                        if c_i.intersects(&c_j) {
                            return i;
                        }
                    }
                }
            }
        }
        self.clauses.len()
    }

    /// Check if this trail is complete for the theory.
    /// A trail is complete if I[Γ] satisfies all clauses in the theory.
    pub fn is_complete(&self, theory: &Theory) -> bool {
        let interp = self.interpretation();

        for clause in theory.clauses() {
            // Check if this clause is satisfied by I[Γ]
            // A clause is satisfied if at least one literal is uniformly true
            let satisfied = clause.literals.iter()
                .any(|lit| interp.is_uniformly_true(lit));
            if !satisfied {
                return false;
            }
        }
        true
    }

    /// Find a conflict clause in the trail.
    /// A conflict clause has all literals uniformly false in the prefix
    /// interpretation (BEFORE that clause is added).
    ///
    /// A clause with an I-false selected literal is NOT a conflict unless
    /// its selected literal is blocked by an EARLIER SELECTED LITERAL on the trail.
    pub fn find_conflict(&self) -> Option<usize> {
        for idx in 0..self.clauses.len() {
            let clause = &self.clauses[idx];
            let selected = clause.selected_literal();

            // Check against the prefix interpretation (before this clause)
            let prefix = self.prefix(idx);
            let interp = prefix.interpretation();

            // A clause with an I-false selected literal is NOT a conflict
            // unless its selected literal is blocked by an earlier selected literal.
            // Check if any earlier selected literal makes the complement of this selected true.
            if self.initial_interp.is_false(selected) {
                // Check if selected literal is blocked by an earlier I-true selected literal
                // (i.e., an earlier clause selected the complement of this selected)
                let complement = selected.negated();
                let mut is_blocked = false;
                for earlier_clause in prefix.clauses.iter() {
                    let earlier_selected = earlier_clause.selected_literal();
                    // An I-true selected literal that matches complement blocks this selected
                    if self.initial_interp.is_true(earlier_selected) {
                        if complement.positive == earlier_selected.positive
                            && complement.atom.predicate == earlier_selected.atom.predicate
                        {
                            if crate::unify::unify_literals(&complement, earlier_selected).is_success() {
                                is_blocked = true;
                                break;
                            }
                        }
                    }
                }
                if !is_blocked {
                    // Selected literal has proper instances - not a conflict
                    continue;
                }
            }

            // Check if all literals are uniformly false in the prefix interpretation
            if clause.is_conflict(&interp) {
                return Some(idx);
            }
        }
        None
    }

    /// Check whether a ground literal is a proper instance of the selected literal
    /// of the clause at the given index (Definitions 6-7).
    /// A proper instance is one that is not complementary (not already satisfied
    /// by earlier clauses in the prefix).
    pub fn is_proper_selected_instance(&self, clause_idx: usize, lit: &Literal) -> bool {
        if clause_idx >= self.clauses.len() {
            return false;
        }

        let clause = &self.clauses[clause_idx];
        let selected = clause.selected_literal();

        // Check that lit matches the selected literal's polarity and predicate
        if lit.positive != selected.positive || lit.atom.predicate != selected.atom.predicate {
            return false;
        }

        // Check that lit is ground
        if !lit.is_ground() {
            return false;
        }

        // Check that the constraint is satisfiable for this instance
        if !clause.constraint.is_satisfiable() {
            return false;
        }

        // Check that this is not a complementary instance
        // (not already true in I^p(Γ|clause_idx-1))
        let prefix = self.prefix(clause_idx);
        let partial = prefix.partial_interpretation();

        // For a positive literal, check if the negation is in the partial interpretation
        // For a negative literal, check if the positive version is in the partial interpretation
        let complement = lit.negated();
        !partial.contains_ground(&complement)
    }

    /// Check whether a ground literal is a complementary instance of the selected literal
    /// of the clause at the given index (Definition 8).
    /// A complementary instance is one that is already satisfied by earlier clauses.
    pub fn is_complementary_selected_instance(&self, clause_idx: usize, lit: &Literal) -> bool {
        if clause_idx >= self.clauses.len() {
            return false;
        }

        let clause = &self.clauses[clause_idx];
        let selected = clause.selected_literal();

        // Check that lit matches the selected literal's polarity and predicate
        if lit.positive != selected.positive || lit.atom.predicate != selected.atom.predicate {
            return false;
        }

        // Check that lit is ground
        if !lit.is_ground() {
            return false;
        }

        // Check that the constraint is satisfiable for this instance
        if !clause.constraint.is_satisfiable() {
            return false;
        }

        // Complementary means the negation is already in I^p(Γ|clause_idx-1)
        let prefix = self.prefix(clause_idx);
        let partial = prefix.partial_interpretation();
        let complement = lit.negated();
        partial.contains_ground(&complement)
    }

    /// Get the clauses in this trail.
    pub fn clauses(&self) -> &[ConstrainedClause] {
        &self.clauses
    }

    /// Access the initial interpretation guiding this trail.
    pub fn initial_interpretation(&self) -> &InitialInterpretation {
        &self.initial_interp
    }
}

impl<'a> TrailInterpretation<'a> {
    /// Is literal uniformly true in I[Γ]?
    ///
    /// A literal is uniformly true in I[Γ] if:
    /// 1. It is true in I (the initial interpretation), or
    /// 2. It is an instance of a selected I-false literal on the trail
    ///    (contributing to the model construction)
    pub fn is_uniformly_true(&self, lit: &Literal) -> bool {
        // First check if it's true in the initial interpretation
        if self.trail.initial_interp.is_true(lit) {
            // But we need to check if the trail has made its complement true
            // For each I-false selected literal on the trail, check if lit
            // is complementary to any of them
            for clause in &self.trail.clauses {
                let selected = clause.selected_literal();
                // Selected literal is I-false; it contributes to the model
                if self.trail.initial_interp.is_false(selected) {
                    // Check if lit is the complement of a selected literal
                    if lit.is_complementary(selected) {
                        // The selected literal (negation of lit) is now true
                        // So lit is false
                        if clause.constraint.is_satisfiable() {
                            return false;
                        }
                    }
                }
            }
            return true;
        }

        // lit is I-false in I. Check if any selected literal makes it true.
        // A selected I-false literal L makes L true.
        for clause in &self.trail.clauses {
            let selected = clause.selected_literal();
            if self.trail.initial_interp.is_false(selected) {
                // This selected literal contributes to the model.
                // Check if lit is an instance of selected
                if lit.positive == selected.positive &&
                   lit.atom.predicate == selected.atom.predicate {
                    // Check if lit unifies with selected under the constraint
                    if clause.constraint.is_satisfiable() {
                        // For uniform truth, the selected literal covers lit
                        // We need to check if lit is a ground instance of selected
                        if lit.is_ground() {
                            if crate::unify::unify_literals(lit, selected).is_success() {
                                return true;
                            }
                        } else {
                            // Non-ground lit: uniformly true if all ground instances are covered
                            // Conservative: return true if selected is more general
                            if crate::unify::unify_literals(lit, selected).is_success() {
                                return true;
                            }
                        }
                    }
                }
            }
        }
        false
    }

    /// Is literal uniformly false in I[Γ]?
    ///
    /// A literal is uniformly false in I[Γ] if its negation is uniformly true.
    pub fn is_uniformly_false(&self, lit: &Literal) -> bool {
        // A literal is uniformly false if it's not uniformly true
        // and its complement is uniformly true
        let negated = lit.negated();
        self.is_uniformly_true(&negated)
    }

    /// Get I-false selected literals for extension.
    /// Returns pairs of (clause index, selected literal) for clauses where
    /// the selected literal is I-false.
    pub fn i_false_selected(&self) -> Vec<(usize, &'a Literal)> {
        let mut result = Vec::new();
        for (idx, clause) in self.trail.clauses.iter().enumerate() {
            let selected = clause.selected_literal();
            if self.trail.initial_interp.is_false(selected) {
                result.push((idx, selected));
            }
        }
        result
    }
}

impl<'a> PartialInterpretation<'a> {
    /// Check whether a ground literal is in I^p(Γ).
    ///
    /// I^p(Γ) contains literals that are:
    /// 1. Proper instances of selected literals (pcgi)
    /// 2. NOT complementary instances (ccgi)
    ///
    /// A ground literal L is a proper instance of selected literal S if:
    /// - L unifies with S
    /// - The constraint is satisfied for the matching substitution
    /// - L is not complementary to any earlier selected literal
    ///
    /// Additionally, if L is covered by a "specific" clause (one with constants),
    /// then ALL constants in L must appear in the trail's Herbrand universe.
    /// This prevents "gap" literals that would be partially defined.
    pub fn contains_ground(&self, lit: &Literal) -> bool {
        use crate::unify::UnifyResult;

        if !lit.is_ground() {
            return false;
        }

        let complement = lit.negated();

        // Collect constants that appear in the trail's clause literals
        let trail_constants = self.collect_trail_constants();
        let lit_constants = self.collect_literal_constants(lit);

        // Check if the literal has a MIX of known and unknown constants.
        // If lit has constants, some must be in the trail and some not - that's a "gap".
        // Literals that are either ALL known or ALL fresh are OK.
        if !lit_constants.is_empty() && !trail_constants.is_empty() {
            let known_count = lit_constants.iter().filter(|c| trail_constants.contains(*c)).count();
            let unknown_count = lit_constants.len() - known_count;

            // If there's a mix (some known, some unknown), exclude this literal
            if known_count > 0 && unknown_count > 0 {
                return false;
            }
        }

        // Walk through the trail in order, looking for a clause where lit is a pcgi.
        for (idx, clause) in self.trail.clauses.iter().enumerate() {
            let selected = clause.selected_literal();

            // Check if lit matches the selected literal's pattern
            if lit.positive == selected.positive &&
               lit.atom.predicate == selected.atom.predicate {
                // Try to unify lit with selected
                if let UnifyResult::Success(mgu) = crate::unify::unify_literals(lit, selected) {
                    // Apply the MGU to the constraint and check satisfiability
                    let applied_constraint = apply_subst_to_constraint(&clause.constraint, &mgu);
                    if !applied_constraint.simplify().is_satisfiable() {
                        continue;
                    }

                    // This clause matches lit. Get the prefix interpretation.
                    let prefix = self.trail.prefix(idx);
                    let prefix_partial = prefix.partial_interpretation();

                    // Check if this is a proper instance (not complementary)
                    // i.e., the complement is not already in the partial interpretation
                    if !prefix_partial.contains_ground(&complement) {
                        // This is a proper instance from this clause
                        return true;
                    }
                    // Otherwise it's complementary, continue checking other clauses
                }
            }
        }
        false
    }

    /// Collect all constants that appear in the trail's clause literals.
    fn collect_trail_constants(&self) -> std::collections::HashSet<String> {
        use crate::syntax::Term;

        let mut constants = std::collections::HashSet::new();

        fn collect_from_term(term: &Term, constants: &mut std::collections::HashSet<String>) {
            match term {
                Term::Var(_) => {}
                Term::App(fn_sym, args) => {
                    if args.is_empty() {
                        // This is a constant
                        constants.insert(fn_sym.name.clone());
                    } else {
                        for arg in args {
                            collect_from_term(arg, constants);
                        }
                    }
                }
            }
        }

        for clause in self.trail.clauses.iter() {
            for lit in &clause.clause.literals {
                for arg in &lit.atom.args {
                    collect_from_term(arg, &mut constants);
                }
            }
        }

        constants
    }

    /// Collect all constants in a literal.
    fn collect_literal_constants(&self, lit: &Literal) -> std::collections::HashSet<String> {
        use crate::syntax::Term;

        let mut constants = std::collections::HashSet::new();

        fn collect_from_term(term: &Term, constants: &mut std::collections::HashSet<String>) {
            match term {
                Term::Var(_) => {}
                Term::App(fn_sym, args) => {
                    if args.is_empty() {
                        constants.insert(fn_sym.name.clone());
                    } else {
                        for arg in args {
                            collect_from_term(arg, constants);
                        }
                    }
                }
            }
        }

        for arg in &lit.atom.args {
            collect_from_term(arg, &mut constants);
        }

        constants
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::Constraint;
    use crate::sggs::ConstrainedClause;
    use crate::syntax::{Clause, Literal, Term};

    fn unit(lit: Literal) -> ConstrainedClause {
        ConstrainedClause::with_constraint(Clause::new(vec![lit]), Constraint::True, 0)
    }

    #[test]
    fn test_disjoint_prefix_length_example_1() {
        // Source: bonacina2016.pdf, Example 1 and Definition 5 (disjoint prefix).
        // For Gamma = P(a,x), P(b,y), not P(z,z), P(u,v), dp(Gamma) = first two clauses.
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos(
            "P",
            vec![Term::constant("a"), Term::var("x")],
        )));
        trail.push(unit(Literal::pos(
            "P",
            vec![Term::constant("b"), Term::var("y")],
        )));
        trail.push(unit(Literal::neg(
            "P",
            vec![Term::var("z"), Term::var("z")],
        )));
        trail.push(unit(Literal::pos(
            "P",
            vec![Term::var("u"), Term::var("v")],
        )));

        assert_eq!(trail.disjoint_prefix_length(), 2);
    }

    #[test]
    fn test_induced_interpretation_example_4() {
        // Source: bonacina2016.pdf, Example 4 and Definition 7 (induced interpretation).
        // With I all-negative, after [P(x)] we have P(a) true; after adding [Q(y)] we have Q(a) true;
        // after adding [R(f(z),g(z))] we have R(f(a),g(a)) true.
        let mut trail = Trail::new(InitialInterpretation::AllNegative);

        // C1 = [P(x)]
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));

        // C2 = not P(f(y)) or [Q(y)]
        let c2 = Clause::new(vec![
            Literal::neg("P", vec![Term::app("f", vec![Term::var("y")])]),
            Literal::pos("Q", vec![Term::var("y")]),
        ]);
        trail.push(ConstrainedClause::with_constraint(c2, Constraint::True, 1));

        // C3 = not P(f(z)) or not Q(g(z)) or [R(f(z), g(z))]
        let c3 = Clause::new(vec![
            Literal::neg("P", vec![Term::app("f", vec![Term::var("z")])]),
            Literal::neg("Q", vec![Term::app("g", vec![Term::var("z")])]),
            Literal::pos(
                "R",
                vec![
                    Term::app("f", vec![Term::var("z")]),
                    Term::app("g", vec![Term::var("z")]),
                ],
            ),
        ]);
        trail.push(ConstrainedClause::with_constraint(c3, Constraint::True, 2));

        let p_a = Literal::pos("P", vec![Term::constant("a")]);
        let q_a = Literal::pos("Q", vec![Term::constant("a")]);
        let r_fa_ga = Literal::pos(
            "R",
            vec![
                Term::app("f", vec![Term::constant("a")]),
                Term::app("g", vec![Term::constant("a")]),
            ],
        );

        let prefix1 = trail.prefix(1);
        let interp1 = prefix1.interpretation();
        assert!(interp1.is_uniformly_true(&p_a));
        assert!(interp1.is_uniformly_false(&q_a));

        let prefix2 = trail.prefix(2);
        let interp2 = prefix2.interpretation();
        assert!(interp2.is_uniformly_true(&q_a));

        let prefix3 = trail.prefix(3);
        let interp3 = prefix3.interpretation();
        assert!(interp3.is_uniformly_true(&r_fa_ga));
    }

    #[test]
    fn test_trail_new_len_empty() {
        let trail = Trail::new(InitialInterpretation::AllNegative);
        assert_eq!(trail.len(), 0);
        assert!(trail.is_empty());
    }

    #[test]
    fn test_trail_push_and_prefix_roundtrip() {
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));
        trail.push(unit(Literal::pos("Q", vec![Term::constant("b")])));

        assert_eq!(trail.len(), 2);
        let prefix = trail.prefix(1);
        assert_eq!(prefix.len(), 1);
        assert_eq!(
            prefix.clauses()[0].selected_literal(),
            trail.clauses()[0].selected_literal()
        );
    }

    #[test]
    fn test_find_conflict_clause_index() {
        // A conflict clause is one where all literals are uniformly false.
        // Under I⁻, ¬P(a) is I-true. If we first make P(a) true by selecting it,
        // then ¬P(a) becomes uniformly false (its complement is now true).
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::constant("a")]))); // Makes P(a) true

        // ¬P(a) is I-true under I⁻, but P(a) is now true in I[Γ].
        // So ¬P(a) is uniformly false → this is a conflict.
        let conflict = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::neg("P", vec![Term::constant("a")])]),
            Constraint::True,
            0,
        );
        trail.push(conflict);

        assert_eq!(trail.find_conflict(), Some(1));
    }
}
