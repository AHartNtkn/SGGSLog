//! SGGS-Extension inference rule.

use super::{ConstrainedClause, Trail};
use crate::constraint::Constraint;
use crate::syntax::{Clause, Literal, Term};
use crate::theory::Theory;
use crate::unify::{unify_literals, Substitution, UnifyResult};

/// Result of attempting SGGS-Extension.
#[derive(Debug)]
pub enum ExtensionResult {
    /// Successfully extended trail
    Extended(ConstrainedClause),
    /// Critical extension: replace a clause at the given index
    Critical {
        replace_index: usize,
        clause: ConstrainedClause,
    },
    /// No extension possible (trail is complete)
    NoExtension,
    /// Found conflict during extension
    Conflict(ConstrainedClause),
}

/// Attempt SGGS-Extension.
///
/// Finds a clause C in the theory where I-true literals of C unify with
/// I-false selected literals on the trail, and generates an instance to add.
pub fn sggs_extension(trail: &Trail, theory: &Theory) -> ExtensionResult {
    let init_interp = trail.initial_interpretation();
    let dp_len = trail.disjoint_prefix_length();

    // Precondition: Γ = dp(Γ) (trail must be disjoint)
    if dp_len != trail.len() {
        return ExtensionResult::NoExtension;
    }

    // Precondition: No conflict clause exists
    if trail.find_conflict().is_some() {
        return ExtensionResult::NoExtension;
    }

    // Try each clause in the theory
    for input_clause in theory.clauses() {
        // Handle empty clause specially - it's an immediate contradiction
        if input_clause.is_empty() {
            // An empty clause means the theory is unsatisfiable
            // We return it as a conflict with no selected literal (index 0 is a dummy)
            return ExtensionResult::Conflict(ConstrainedClause::with_constraint(
                Clause::empty(),
                Constraint::True,
                0, // Dummy index - empty clause has no literals
            ));
        }

        // Identify I-true literals (n ≥ 0) and I-false literals
        let i_true_indices: Vec<usize> = input_clause
            .literals
            .iter()
            .enumerate()
            .filter(|(_, lit)| init_interp.is_true(lit))
            .map(|(idx, _)| idx)
            .collect();

        let i_false_indices: Vec<usize> = input_clause
            .literals
            .iter()
            .enumerate()
            .filter(|(_, lit)| init_interp.is_false(lit))
            .map(|(idx, _)| idx)
            .collect();

        // Try ALL possible side premise combinations for I-true literals.
        // This ensures we don't miss valid extensions when one combination is redundant.
        let all_side_premise_results =
            find_all_side_premises(trail, input_clause, &i_true_indices, dp_len);

        if all_side_premise_results.is_empty() {
            continue;
        }

        // For I-all-true clauses (no I-false literals), this will be a conflict
        let is_all_i_true = i_false_indices.is_empty();

        // Try each side premise combination until we find a non-redundant one
        for side_premise_result in all_side_premise_results {
            let alpha = side_premise_result.substitution;
            let constraint = side_premise_result.constraint;
            let side_premise_predicates = side_premise_result.side_premise_predicates;

            // Apply substitution to clause
            let extended_lits: Vec<Literal> = input_clause
                .literals
                .iter()
                .map(|lit| lit.apply_subst(&alpha))
                .collect();

            // Check if extended clause would be redundant (already covered by trail)
            if is_redundant_extension(&extended_lits, trail, &constraint) {
                continue; // Try next side premise combination
            }

            // Find the selected literal
            let selected_idx = if is_all_i_true {
                // For I-all-true conflict clauses, select the first literal
                0
            } else {
                // Find I-false literal with proper instances
                match find_selected_literal(&extended_lits, trail, &constraint, init_interp) {
                    Some(idx) => idx,
                    None => continue, // Try next side premise combination
                }
            };

            let extended_clause = ConstrainedClause::with_constraint(
                Clause::new(extended_lits.clone()),
                constraint.clone(),
                selected_idx,
            );

            // Check if this is a critical extension first.
            // A critical extension happens when the selected literal is blocked
            // by an I-all-true clause in dp(Γ) that should be replaced.
            // The blocker must be on a DIFFERENT predicate than the side premises,
            // otherwise it's a true conflict (not replaceable).
            if let Some(blocker_idx) =
                find_blocking_clause(trail, &extended_clause, dp_len, &side_premise_predicates)
            {
                return ExtensionResult::Critical {
                    replace_index: blocker_idx,
                    clause: extended_clause,
                };
            }

            // Check if this is a conflict clause (all literals uniformly false in I[Γ])
            // This happens for I-all-true extension clauses that conflict with the trail.
            if is_conflict_extended(&extended_lits, trail) {
                return ExtensionResult::Conflict(extended_clause);
            }

            return ExtensionResult::Extended(extended_clause);
        }
    }

    ExtensionResult::NoExtension
}

/// Result of finding side premises - includes predicates used for critical extension check.
#[derive(Debug)]
struct SidePremiseResult {
    substitution: Substitution,
    constraint: Constraint,
    /// Predicates used by side premises (for critical extension detection)
    side_premise_predicates: std::collections::HashSet<String>,
}

/// Find side premises in dp(Γ) for I-true literals.
/// Returns (substitution, combined constraint, predicates) if all I-true literals can be matched.
///
/// For each I-true literal L in the clause, we find a side premise whose
/// I-false selected literal M unifies with the complement of L.
/// This captures the relationship: L is I-true, its complement ~L unifies with M (I-false selected).
///
/// When there are no I-true literals (n=0), this returns an empty substitution unless
/// the interpretation is Explicit, in which case we try to find a semantic falsifier.
/// Find ALL possible side premise combinations for a clause.
/// Returns a vector of all valid combinations, trying older premises first.
fn find_all_side_premises(
    trail: &Trail,
    clause: &Clause,
    i_true_indices: &[usize],
    dp_len: usize,
) -> Vec<SidePremiseResult> {
    let init_interp = trail.initial_interpretation();

    // If no I-true literals, return a single result with empty substitution
    if i_true_indices.is_empty() {
        let mut combined_subst = Substitution::empty();
        // Try to find a semantic falsifier for non-ground clauses
        if !clause.is_ground() {
            if let Some(falsifier) = find_explicit_semantic_falsifier(clause, init_interp) {
                combined_subst = falsifier;
            }
        }
        return vec![SidePremiseResult {
            substitution: combined_subst,
            constraint: Constraint::True,
            side_premise_predicates: std::collections::HashSet::new(),
        }];
    }

    // Collect all valid premise indices for each I-true literal
    let mut premise_options: Vec<Vec<usize>> = Vec::new();
    for &lit_idx in i_true_indices {
        let i_true_lit = &clause.literals[lit_idx];
        let complement = i_true_lit.negated();

        let mut valid_premises = Vec::new();
        // Search FORWARD (oldest first) to prefer earlier extensions
        for premise_idx in 0..dp_len {
            let premise = &trail.clauses()[premise_idx];
            let selected = premise.selected_literal();

            if !init_interp.is_false(selected) {
                continue;
            }

            if complement.positive != selected.positive
                || complement.atom.predicate != selected.atom.predicate
            {
                continue;
            }

            if unify_literals(&complement, selected).is_success() {
                valid_premises.push(premise_idx);
            }
        }

        if valid_premises.is_empty() {
            return vec![]; // No valid premises for this I-true literal
        }
        premise_options.push(valid_premises);
    }

    // Generate all combinations (Cartesian product)
    let mut results = Vec::new();
    generate_premise_combinations(
        trail,
        clause,
        i_true_indices,
        &premise_options,
        0,
        &mut vec![],
        &mut results,
    );
    results
}

/// Recursively generate all premise combinations.
fn generate_premise_combinations(
    trail: &Trail,
    clause: &Clause,
    i_true_indices: &[usize],
    premise_options: &[Vec<usize>],
    depth: usize,
    current_combo: &mut Vec<usize>,
    results: &mut Vec<SidePremiseResult>,
) {
    if depth == premise_options.len() {
        // Build the result from this combination
        if let Some(result) = build_side_premise_result(trail, clause, i_true_indices, current_combo)
        {
            results.push(result);
        }
        return;
    }

    for &premise_idx in &premise_options[depth] {
        // Check that this premise isn't already used
        if current_combo.contains(&premise_idx) {
            continue;
        }
        current_combo.push(premise_idx);
        generate_premise_combinations(
            trail,
            clause,
            i_true_indices,
            premise_options,
            depth + 1,
            current_combo,
            results,
        );
        current_combo.pop();
    }
}

/// Build a SidePremiseResult from a specific combination of premises.
fn build_side_premise_result(
    trail: &Trail,
    clause: &Clause,
    i_true_indices: &[usize],
    premise_indices: &[usize],
) -> Option<SidePremiseResult> {
    let mut combined_subst = Substitution::empty();
    let mut combined_constraint = Constraint::True;
    let mut side_premise_predicates = std::collections::HashSet::new();

    for (i, &lit_idx) in i_true_indices.iter().enumerate() {
        let i_true_lit = clause.literals[lit_idx].apply_subst(&combined_subst);
        let complement = i_true_lit.negated();

        let premise_idx = premise_indices[i];
        let premise = &trail.clauses()[premise_idx];
        let selected = premise.selected_literal();

        if let UnifyResult::Success(sigma) = unify_literals(&complement, selected) {
            side_premise_predicates.insert(selected.atom.predicate.clone());
            combined_subst = combined_subst.compose(&sigma);
            combined_constraint = combined_constraint.and(premise.constraint.clone());
        } else {
            return None; // Unification failed with applied substitution
        }
    }

    Some(SidePremiseResult {
        substitution: combined_subst,
        constraint: combined_constraint.simplify(),
        side_premise_predicates,
    })
}

/// Find a semantic falsifier for a non-ground clause using explicit false atoms.
///
/// This tries to match non-ground literals in the clause with known false atoms
/// to find a grounding substitution.
fn find_explicit_semantic_falsifier(
    clause: &Clause,
    interp: &super::InitialInterpretation,
) -> Option<Substitution> {
    use super::InitialInterpretation;

    match interp {
        InitialInterpretation::Explicit { false_atoms, .. } => {
            // For each non-ground literal in the clause, try to unify with a known false atom.
            // We want to find a substitution that grounds the literal to an I-false instance.
            for lit in &clause.literals {
                // Skip ground literals (they don't need a falsifier)
                if lit.is_ground() {
                    continue;
                }

                // For positive literals, we try to unify with a known false atom
                // (a positive literal is I-false when its atom is in false_atoms)
                if lit.positive {
                    for false_atom in false_atoms {
                        if false_atom.predicate != lit.atom.predicate {
                            continue;
                        }

                        // Try to unify the literal's atom with the false atom
                        let target_lit = Literal {
                            positive: true,
                            atom: false_atom.clone(),
                        };
                        if let UnifyResult::Success(sigma) = unify_literals(lit, &target_lit) {
                            return Some(sigma);
                        }
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Check if extension would be redundant (clause already satisfied by trail).
///
/// A clause is redundant if ANY of its I-false literals is already covered by
/// the partial interpretation I^p(Γ), because that makes the clause true in I[Γ].
///
/// For ground literals, we check `contains_ground`.
/// For non-ground literals, we check if there's a selected literal on the trail
/// that subsumes (is at least as general as) the candidate literal.
fn is_redundant_extension(
    extended_lits: &[Literal],
    trail: &Trail,
    _constraint: &Constraint,
) -> bool {
    let init_interp = trail.initial_interpretation();

    for lit in extended_lits {
        if init_interp.is_false(lit) {
            // Check if this I-false literal is already covered
            if is_literal_covered(lit, trail) {
                return true;
            }
        }
    }

    // No I-false literal is covered, so clause is not satisfied
    false
}

/// Check if a literal is already covered by the trail's partial interpretation.
///
/// A literal is covered if:
/// 1. For ground literals: it's in the partial interpretation
/// 2. For non-ground literals: there exists a selected literal on the trail
///    that is at least as general (subsumes all ground instances)
fn is_literal_covered(lit: &Literal, trail: &Trail) -> bool {
    // For ground literals, use the existing contains_ground check
    if lit.is_ground() {
        return trail.partial_interpretation().contains_ground(lit);
    }

    // For non-ground literals, check if any selected literal on the trail
    // subsumes this literal (i.e., is at least as general)
    for clause in trail.clauses() {
        let selected = clause.selected_literal();

        // Must have same predicate and polarity
        if lit.positive != selected.positive || lit.atom.predicate != selected.atom.predicate {
            continue;
        }

        // Check if selected subsumes lit (selected is at least as general)
        // This means: lit is an instance of selected
        // i.e., there exists σ such that σ(selected) = lit
        if is_instance_of(lit, selected) {
            return true;
        }
    }

    false
}

/// Check if `specific` is an instance of `general`.
///
/// Returns true if there exists a substitution σ such that σ(general) = specific.
/// This means `general` is at least as general as `specific`.
pub(crate) fn is_instance_of(specific: &Literal, general: &Literal) -> bool {
    if specific.positive != general.positive || specific.atom.predicate != general.atom.predicate {
        return false;
    }

    if specific.atom.args.len() != general.atom.args.len() {
        return false;
    }

    // Use one-way matching: try to find σ such that σ(general) = specific
    // without binding any variables from specific.
    match_terms_one_way(&general.atom.args, &specific.atom.args)
}

/// One-way matching: find σ such that σ(pattern) = target, where σ only binds
/// variables from pattern, not from target.
fn match_terms_one_way(pattern: &[Term], target: &[Term]) -> bool {
    use std::collections::HashMap;

    if pattern.len() != target.len() {
        return false;
    }

    // Build a substitution that maps pattern variables to target terms
    let mut subst: HashMap<String, &Term> = HashMap::new();

    for (p, t) in pattern.iter().zip(target.iter()) {
        if !match_term_one_way(p, t, &mut subst) {
            return false;
        }
    }

    true
}

/// Match a single term (pattern against target).
fn match_term_one_way<'a>(
    pattern: &Term,
    target: &'a Term,
    subst: &mut std::collections::HashMap<String, &'a Term>,
) -> bool {
    match pattern {
        Term::Var(v) => {
            // Pattern variable: check if already bound
            let key = v.name().to_string();
            if let Some(existing) = subst.get(&key) {
                // Must match the same target term
                *existing == target
            } else {
                // Bind the pattern variable to the target term
                subst.insert(key, target);
                true
            }
        }
        Term::App(fn_sym, args) => {
            // Pattern is a function application
            match target {
                Term::Var(_) => {
                    // Target is a variable - pattern is more specific, so not a match
                    // (we can't instantiate a function to a variable)
                    false
                }
                Term::App(target_fn, target_args) => {
                    // Both are function applications - must have same symbol and arity
                    if fn_sym.name != target_fn.name || args.len() != target_args.len() {
                        return false;
                    }
                    // Recursively match arguments
                    for (p, t) in args.iter().zip(target_args.iter()) {
                        if !match_term_one_way(p, t, subst) {
                            return false;
                        }
                    }
                    true
                }
            }
        }
    }
}

/// Find the selected literal index (first I-false literal with proper instances).
///
/// Priority order:
/// 1. I-false literals that are NOT already in the partial interpretation (fresh)
///    AND have proper instances (complement not in partial)
/// 2. I-false literals with proper instances (even if already in partial)
/// 3. First I-false literal (fallback)
///
/// This ordering prevents selecting the same literal that's already on the trail,
/// which would create a duplicate and cause an Extension→Deletion infinite loop.
fn find_selected_literal(
    extended_lits: &[Literal],
    trail: &Trail,
    constraint: &Constraint,
    init_interp: &super::InitialInterpretation,
) -> Option<usize> {
    let partial = trail.partial_interpretation();

    // Find I-false literals
    let i_false_indices: Vec<usize> = extended_lits
        .iter()
        .enumerate()
        .filter(|(_, lit)| init_interp.is_false(lit))
        .map(|(idx, _)| idx)
        .collect();

    // Priority 1: Find an I-false literal that is FRESH (not already in partial)
    // and has proper instances. This contributes new information to the model.
    for &idx in &i_false_indices {
        let lit = &extended_lits[idx];
        // Check if this literal is NOT already selected on the trail
        if !partial.contains_ground(lit) {
            // Also verify it has proper instances (complement not blocking it)
            if has_proper_instances(lit, trail, constraint) {
                return Some(idx);
            }
        }
    }

    // Priority 2: Find any I-false literal with proper instances
    // (This handles cases where all literals are in partial but have proper instances)
    for &idx in &i_false_indices {
        let lit = &extended_lits[idx];
        if has_proper_instances(lit, trail, constraint) {
            return Some(idx);
        }
    }

    // Priority 3: Fallback to first I-false (shouldn't normally reach here)
    i_false_indices.first().copied()
}

/// Check if a literal has proper constrained ground instances.
///
/// A literal has proper instances if its complement is not uniformly true
/// in the trail interpretation. For ground literals, we check contains_ground.
/// For non-ground literals, we check if the complement unifies with any
/// selected literal on the trail (which would block all instances).
fn has_proper_instances(lit: &Literal, trail: &Trail, _constraint: &Constraint) -> bool {
    let complement = lit.negated();

    // For ground literals, check if complement is in partial interpretation
    if lit.is_ground() {
        let partial = trail.partial_interpretation();
        return !partial.contains_ground(&complement);
    }

    // For non-ground literals, check if complement unifies with any selected literal
    // on the trail. If it does, the selected literal blocks all ground instances.
    for clause in trail.clauses() {
        let selected = clause.selected_literal();

        // Check if complement could unify with the selected literal
        if complement.positive == selected.positive
            && complement.atom.predicate == selected.atom.predicate
        {
            // Try to unify the complement with the selected literal
            if let UnifyResult::Success(_) = unify_literals(&complement, selected) {
                // The complement unifies with a selected literal, so all instances
                // of this literal are blocked (no proper instances)
                return false;
            }
        }
    }

    // No blocking selected literal found
    true
}

/// Check if extended clause would be a conflict.
///
/// An extended clause is a conflict if ALL its literals are uniformly false in I[Γ].
/// This can happen in two ways:
/// 1. The clause is I-all-true (all literals I-true under I), and their complements
///    are selected on the trail making them false in I[Γ].
/// 2. Each literal's complement is uniformly true in I[Γ] (selected on trail).
fn is_conflict_extended(extended_lits: &[Literal], trail: &Trail) -> bool {
    let init_interp = trail.initial_interpretation();
    let trail_interp = trail.interpretation();
    let partial = trail.partial_interpretation();

    // Check if ALL literals are uniformly false in I[Γ]
    for lit in extended_lits {
        // A literal is uniformly false in I[Γ] if:
        // 1. It's I-true and its complement is uniformly true in I[Γ] (selected)
        // 2. It's I-false and its complement is in I^p(Γ) (selected makes complement true)

        let complement = lit.negated();

        if init_interp.is_true(lit) {
            // I-true literal: needs complement to be uniformly true
            if !trail_interp.is_uniformly_true(&complement) {
                return false;
            }
        } else {
            // I-false literal: needs complement to be in I^p(Γ)
            if !partial.contains_ground(&complement) {
                return false;
            }
        }
    }

    true
}

/// Find a blocking clause for a critical extension.
///
/// A blocking clause is an I-all-true clause in dp(Γ) whose selected literal
/// complements the extended clause's selected literal.
///
/// For a CRITICAL extension (not a conflict), the blocker must be on a DIFFERENT
/// predicate than the side premises used in the extension. If the blocker is on
/// the same predicate as a side premise, it's a true conflict, not replaceable.
fn find_blocking_clause(
    trail: &Trail,
    extended: &ConstrainedClause,
    dp_len: usize,
    side_premise_predicates: &std::collections::HashSet<String>,
) -> Option<usize> {
    let init_interp = trail.initial_interpretation();
    let selected = extended.selected_literal();

    // Look for I-all-true clauses in dp(Γ) that block the selected literal
    for idx in 0..dp_len {
        let clause = &trail.clauses()[idx];
        let clause_selected = clause.selected_literal();

        // Check if clause is I-all-true and blocks selected literal
        if init_interp.is_true(clause_selected) {
            // Check if clause's selected literal complements extended's selected
            if selected.positive != clause_selected.positive
                && selected.atom.predicate == clause_selected.atom.predicate
            {
                if let UnifyResult::Success(_) =
                    unify_literals(&selected.negated(), clause_selected)
                {
                    // Check if constraints intersect
                    if extended.constraint.intersects(&clause.constraint) {
                        // Only a critical extension if blocker is on DIFFERENT predicate
                        // than the side premises. Otherwise it's a true conflict.
                        if !side_premise_predicates.contains(&clause_selected.atom.predicate) {
                            return Some(idx);
                        }
                    }
                }
            }
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::Constraint;
    use crate::sggs::{ConstrainedClause, InitialInterpretation, Trail};
    use crate::syntax::{Clause, Literal, Term};
    use crate::theory::Theory;
    use std::collections::HashSet;

    fn unit(lit: Literal) -> ConstrainedClause {
        ConstrainedClause::with_constraint(Clause::new(vec![lit]), Constraint::True, 0)
    }

    #[test]
    fn test_extension_non_conflicting_instance_added() {
        // Source: SGGSdpFOL.pdf, Definition 1 (SGGS-extension scheme).
        // With I = all-negative, I-true literals are negative, I-false are positive.
        // Clause C = not P(x) or Q(x), with side premise selecting P(a), yields C[a/x].
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));

        let mut theory = Theory::new();
        let clause = Clause::new(vec![
            Literal::neg("P", vec![Term::var("x")]),
            Literal::pos("Q", vec![Term::var("x")]),
        ]);
        theory.add_clause(clause);

        match sggs_extension(&trail, &theory) {
            ExtensionResult::Extended(cc) => {
                let got: HashSet<_> = cc.clause.literals.iter().cloned().collect();
                let expected: HashSet<_> = vec![
                    Literal::neg("P", vec![Term::constant("a")]),
                    Literal::pos("Q", vec![Term::constant("a")]),
                ]
                .into_iter()
                .collect();
                assert_eq!(got, expected);

                // With I all-negative, selected literal must be I-false (positive).
                let interp = InitialInterpretation::AllNegative;
                assert!(interp.is_false(cc.selected_literal()));
                assert_eq!(
                    cc.selected_literal(),
                    &Literal::pos("Q", vec![Term::constant("a")])
                );
            }
            other => panic!("Expected extension, got {:?}", other),
        }
    }

    #[test]
    fn test_extension_all_true_conflict() {
        // Source: paper6.pdf, Definition 1 (SGGS-extension):
        // if the extension clause is I-all-true, it is a conflict clause.
        let mut trail = Trail::new(InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));

        let mut theory = Theory::new();
        let clause = Clause::new(vec![Literal::neg("P", vec![Term::var("x")])]);
        theory.add_clause(clause);

        match sggs_extension(&trail, &theory) {
            ExtensionResult::Conflict(cc) => {
                let got: HashSet<_> = cc.clause.literals.clone().into_iter().collect();
                let expected: HashSet<_> = vec![Literal::neg("P", vec![Term::constant("a")])]
                    .into_iter()
                    .collect();
                assert_eq!(got, expected);
            }
            other => panic!("Expected conflict extension, got {:?}", other),
        }
    }

    #[test]
    fn test_extension_with_no_i_true_literals() {
        // Source: SGGSdpFOL.pdf, Definition 1 (SGGS-extension scheme), n ≥ 0.
        // If a clause has no I-true literals, extension does not need side premises.
        // (Here we use a ground clause; the non-ground case is covered separately.)
        let trail = Trail::new(InitialInterpretation::AllNegative);

        let mut theory = Theory::new();
        theory.add_clause(Clause::new(vec![Literal::pos(
            "P",
            vec![Term::constant("a")],
        )]));

        match sggs_extension(&trail, &theory) {
            ExtensionResult::Extended(cc) => {
                let got: HashSet<_> = cc.clause.literals.clone().into_iter().collect();
                let expected: HashSet<_> = vec![Literal::pos("P", vec![Term::constant("a")])]
                    .into_iter()
                    .collect();
                assert_eq!(got, expected);
                assert_eq!(
                    cc.selected_literal(),
                    &Literal::pos("P", vec![Term::constant("a")])
                );
            }
            other => panic!("Expected extension with n=0, got {:?}", other),
        }
    }

    #[test]
    fn test_extension_with_no_i_true_literals_non_ground() {
        // Source: SGGSdpFOL.pdf, Definition 1 (SGGS-extension scheme), n ≥ 0.
        // With no I-true literals, the extension uses a most-general semantic falsifier.
        // Source: bonacina2016.pdf, Definition 12.
        // Quote: "There is a most general semantic falsifier β of (C\\{L1,…,Ln})α"
        // and "As a special case, when n=0, there are no side premises ... (α is empty and β is not)."
        // Under I⁻, this should not over-instantiate variables.
        let trail = Trail::new(InitialInterpretation::AllNegative);

        let mut theory = Theory::new();
        let clause = Clause::new(vec![Literal::pos("P", vec![Term::var("X")])]);
        theory.add_clause(clause.clone());

        match sggs_extension(&trail, &theory) {
            ExtensionResult::Extended(cc) => {
                assert_eq!(cc.clause.literals.len(), 1);
                let lit = cc.selected_literal();
                assert!(lit.positive);
                assert!(
                    crate::unify::unify_literals(lit, &clause.literals[0]).is_success(),
                    "extended literal should be an instance of the original"
                );
                assert!(
                    !lit.is_ground(),
                    "most-general falsifier should not ground variables"
                );
            }
            other => panic!("Expected non-ground extension with n=0, got {:?}", other),
        }
    }

    #[test]
    fn test_extension_all_positive_selects_i_false_literal() {
        // With I = all-positive, negative literals are I-false.
        // Use a side premise with selected ¬P(a) and a clause P(x) ∨ ¬R(x).
        let mut trail = Trail::new(InitialInterpretation::AllPositive);
        trail.push(unit(Literal::neg("P", vec![Term::constant("a")])));

        let mut theory = Theory::new();
        let clause = Clause::new(vec![
            Literal::pos("P", vec![Term::var("x")]),
            Literal::neg("R", vec![Term::var("x")]),
        ]);
        theory.add_clause(clause);

        match sggs_extension(&trail, &theory) {
            ExtensionResult::Extended(cc) => {
                let got: HashSet<_> = cc.clause.literals.iter().cloned().collect();
                let expected: HashSet<_> = vec![
                    Literal::pos("P", vec![Term::constant("a")]),
                    Literal::neg("R", vec![Term::constant("a")]),
                ]
                .into_iter()
                .collect();
                assert_eq!(got, expected);
                assert_eq!(
                    cc.selected_literal(),
                    &Literal::neg("R", vec![Term::constant("a")])
                );
            }
            other => panic!("Expected extension under I⁺, got {:?}", other),
        }
    }

    #[test]
    fn test_extension_uses_explicit_semantic_falsifier() {
        // Explicit interpretation with a known false atom should drive semantic falsifier.
        let mut falses = std::collections::HashSet::new();
        falses.insert(crate::syntax::Atom::new("p", vec![Term::constant("b")]));
        let interp = InitialInterpretation::Explicit {
            true_atoms: std::collections::HashSet::new(),
            false_atoms: falses,
            default: crate::sggs::TruthValue::Unknown,
        };
        let trail = Trail::new(interp);

        let mut theory = Theory::new();
        let clause = Clause::new(vec![Literal::pos("p", vec![Term::var("X")])]);
        theory.add_clause(clause);

        match sggs_extension(&trail, &theory) {
            ExtensionResult::Extended(cc) => {
                assert_eq!(
                    cc.selected_literal(),
                    &Literal::pos("p", vec![Term::constant("b")])
                );
            }
            other => panic!("Expected extension via semantic falsifier, got {:?}", other),
        }
    }

    #[test]
    fn test_extension_prefers_fresh_literal_over_already_selected() {
        // Scenario: Trail has (p∨q) with p selected
        // When trying to extend (p∨q) again, the clause should NOT be extended
        // because p is already in I^p(Γ), making the clause satisfied/redundant.
        let mut trail = Trail::new(InitialInterpretation::AllNegative);

        // Add (p∨q) with p selected (index 0)
        let first_clause = ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("p", vec![]), Literal::pos("q", vec![])]),
            Constraint::True,
            0, // p selected
        );
        trail.push(first_clause);

        // Now try to extend (p∨q) from theory
        let mut theory = Theory::new();
        theory.add_clause(Clause::new(vec![
            Literal::pos("p", vec![]),
            Literal::pos("q", vec![]),
        ]));

        // Debug: check partial interpretation state
        let partial = trail.partial_interpretation();
        let p = Literal::pos("p", vec![]);
        let q = Literal::pos("q", vec![]);
        eprintln!("p in partial: {}", partial.contains_ground(&p));
        eprintln!("q in partial: {}", partial.contains_ground(&q));

        // Since p is already selected on the trail, the clause (p∨q) is
        // satisfied in I[Γ] and should NOT be extended.
        match sggs_extension(&trail, &theory) {
            ExtensionResult::NoExtension => {
                // Correct! The clause is redundant because p is already satisfied.
            }
            other => panic!(
                "Expected NoExtension since clause is satisfied by p, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_extension_selects_fresh_literal_when_first_is_complementary() {
        // Scenario: Trail has ¬p selected, theory has (p∨q)
        // When extending, should select q because p is blocked by ¬p (no proper instances)
        let mut trail = Trail::new(InitialInterpretation::AllNegative);

        // Add unit clause ¬p with ¬p selected
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::neg("p", vec![])]),
            Constraint::True,
            0,
        ));

        // Theory has (p∨q)
        let mut theory = Theory::new();
        theory.add_clause(Clause::new(vec![
            Literal::pos("p", vec![]),
            Literal::pos("q", vec![]),
        ]));

        match sggs_extension(&trail, &theory) {
            ExtensionResult::Extended(cc) => {
                // p has no proper instances (blocked by ¬p), so q should be selected
                assert_eq!(
                    cc.selected_literal(),
                    &Literal::pos("q", vec![]),
                    "Should select q since p is blocked by ¬p"
                );
            }
            other => panic!("Expected Extended with q selected, got {:?}", other),
        }
    }
}
