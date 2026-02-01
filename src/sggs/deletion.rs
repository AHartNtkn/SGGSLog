//! SGGS-Deletion for removing disposable clauses.

use std::collections::{HashMap, HashSet};

use super::{ConstrainedClause, Trail};
use crate::constraint::Constraint;
use crate::syntax::Term;
use crate::unify::{unify_literals, Substitution, UnifyResult};

/// SGGS-Deletion: remove disposable clauses from trail.
///
/// A clause is disposable if all its atoms are satisfied by the
/// trail interpretation and removing it doesn't affect the model.
pub fn sggs_deletion(trail: &mut Trail) {
    // Find indices of disposable clauses (iterate in reverse to handle removal)
    let mut to_remove: Vec<usize> = Vec::new();

    for idx in 0..trail.clauses().len() {
        let clause = &trail.clauses()[idx];
        if is_disposable_at_index(clause, trail, idx) {
            to_remove.push(idx);
        }
    }

    // Remove disposable clauses from end to start to preserve indices
    for idx in to_remove.into_iter().rev() {
        trail.remove_clause(idx);
    }
}

/// Check if a clause is disposable.
///
/// A clause C at position j is disposable if:
/// 1. Its constraint is unsatisfiable (Gr(A ⊲ C) = ∅), or
/// 2. All proper ground instances of its selected literal are already
///    covered by selected literals earlier in the trail (positions 0..j-1).
pub fn is_disposable(clause: &ConstrainedClause, trail: &Trail) -> bool {
    // Find the clause's index in the trail
    let idx = trail.clauses().iter().position(|c| std::ptr::eq(c, clause));
    match idx {
        Some(idx) => is_disposable_at_index(clause, trail, idx),
        None => false,
    }
}

/// Check if a clause at a specific index is disposable.
fn is_disposable_at_index(clause: &ConstrainedClause, trail: &Trail, idx: usize) -> bool {
    // Case 1: Unsatisfiable constraint means no ground instances
    if !clause.constraint.is_satisfiable() {
        return true;
    }

    let selected = clause.selected_literal();

    // For a clause to have pcgi's, there must exist some ground instance whose
    // complement is NOT in I^p(prefix). We can't enumerate all instances,
    // so we use a conservative check: if the clause contributes nothing new
    // (all instances are ccgi), it's not disposable.
    //
    // A simple approximation: check if the complement pattern is covered by prefix.
    // If the negation of selected is fully covered by earlier clauses, then all
    // instances are ccgi and the clause has no pcgi's.
    let complement = selected.negated();
    let complement_fully_covered = is_fully_covered_by_prefix(&complement, trail, idx);

    if complement_fully_covered {
        // All instances of selected are ccgi (complement is in I^p for all)
        // A clause with no pcgi's is NOT disposable
        return false;
    }

    // Case 2: The clause has pcgi's. Check if they're all covered by earlier clauses.
    // This happens when an earlier clause's selected literal is MORE GENERAL and
    // covers all instances of the current selected literal.

    for earlier_idx in 0..idx {
        let earlier = &trail.clauses()[earlier_idx];
        let earlier_selected = earlier.selected_literal();

        // Same polarity and predicate required
        if selected.positive != earlier_selected.positive
            || selected.atom.predicate != earlier_selected.atom.predicate
        {
            continue;
        }

        // Check if earlier_selected is at least as general as selected.
        // earlier_selected is more general if selected is an instance of it.
        if is_instance_of(selected, earlier_selected) && earlier.constraint.is_satisfiable() {
            // Earlier clause's selected literal covers all instances of selected
            return true;
        }

        // Also check constraint subsumption:
        // If selected unifies with earlier_selected and the constraints entail,
        // then earlier subsumes clause.
        if let UnifyResult::Success(mgu) = unify_literals(selected, earlier_selected) {
            // Check if earlier's constraint (after MGU) entails clause's constraint
            if constraint_entails_after_subst(&earlier.constraint, &clause.constraint, &mgu) {
                return true;
            }
        }
    }

    // Case 3: Check if multiple earlier clauses together cover all ground instances.
    // This handles cases like P(a), P(f(x)) covering all instances of P(z) when
    // the signature only has constant 'a' and function 'f'.
    if earlier_clauses_cover_all(selected, trail, idx) {
        return true;
    }

    false
}

/// Check if `lit1` is an instance of `lit2` (lit2 is more general).
fn is_instance_of(lit1: &crate::syntax::Literal, lit2: &crate::syntax::Literal) -> bool {
    if lit1.positive != lit2.positive || lit1.atom.predicate != lit2.atom.predicate {
        return false;
    }

    // lit1 is an instance of lit2 if there exists σ such that σ(lit2) = lit1
    // and σ only binds variables from lit2 (not from lit1).
    if let UnifyResult::Success(mgu) = unify_literals(lit1, lit2) {
        let lit2_applied = lit2.apply_subst(&mgu);
        // Check if lit2 applied with mgu equals lit1
        if lit2_applied.atom == lit1.atom {
            // Now check if mgu only binds variables from lit2
            let lit1_vars = lit1.variables();
            // All MGU bindings should be for variables in lit2, not lit1
            // (Or they're identity bindings for lit1's vars)
            for v in mgu.domain() {
                if lit1_vars.contains(v) {
                    // lit1's variable is being bound - check if it's identity
                    if let Some(t) = mgu.lookup(v) {
                        match t {
                            crate::syntax::Term::Var(v2) if v2 == v => continue,
                            _ => return false,
                        }
                    }
                }
            }
            return true;
        }
    }
    false
}

/// Check if a literal is fully covered by clauses in the prefix.
fn is_fully_covered_by_prefix(
    lit: &crate::syntax::Literal,
    trail: &Trail,
    prefix_len: usize,
) -> bool {
    // A literal is fully covered if there exists an earlier clause whose
    // selected literal is at least as general (covers all instances).
    for idx in 0..prefix_len {
        let earlier = &trail.clauses()[idx];
        let earlier_selected = earlier.selected_literal();

        if lit.positive == earlier_selected.positive
            && lit.atom.predicate == earlier_selected.atom.predicate
        {
            // Check if earlier_selected covers all of lit's instances
            if is_instance_of(lit, earlier_selected) && earlier.constraint.is_satisfiable() {
                return true;
            }
        }
    }
    false
}

/// Check if earlier clauses together cover all ground instances of a literal.
///
/// This handles cases where no single earlier clause is more general, but
/// the combination covers everything. For example, P(a) and P(f(x)) together
/// cover all instances of P(z) when the signature only contains 'a' and 'f'.
fn earlier_clauses_cover_all(selected: &crate::syntax::Literal, trail: &Trail, idx: usize) -> bool {
    // Only handle single-argument predicates for now
    if selected.atom.args.len() != 1 {
        return false;
    }

    // Only relevant when selected has a variable argument
    let sel_arg = &selected.atom.args[0];
    if !matches!(sel_arg, Term::Var(_)) {
        return false;
    }

    // Collect patterns from earlier clauses with same predicate and polarity
    let mut pattern_roots: HashSet<String> = HashSet::new();
    let mut has_var_pattern = false;

    for earlier_idx in 0..idx {
        let earlier = &trail.clauses()[earlier_idx];
        let earlier_selected = earlier.selected_literal();

        if selected.positive != earlier_selected.positive
            || selected.atom.predicate != earlier_selected.atom.predicate
            || !earlier.constraint.is_satisfiable()
        {
            continue;
        }

        if earlier_selected.atom.args.len() != 1 {
            continue;
        }

        match &earlier_selected.atom.args[0] {
            Term::Var(_) => {
                has_var_pattern = true;
            }
            Term::App(sym, _) => {
                pattern_roots.insert(sym.name.clone());
            }
        }
    }

    // A variable pattern covers everything
    if has_var_pattern {
        return true;
    }

    // Check if pattern roots cover the entire signature
    let signature = extract_signature(trail);

    // Every constant must be covered
    for c in &signature.constants {
        if !pattern_roots.contains(c) {
            return false;
        }
    }

    // Every function symbol must be covered
    for f in signature.functions.keys() {
        if !pattern_roots.contains(f) {
            return false;
        }
    }

    // If signature is empty (no constants or functions), patterns don't cover anything
    if signature.constants.is_empty() && signature.functions.is_empty() {
        return false;
    }

    true
}

/// Signature extracted from trail: constants and function symbols.
struct Signature {
    constants: HashSet<String>,
    functions: HashMap<String, usize>, // name -> arity
}

/// Extract the signature (constants and function symbols) from the trail.
fn extract_signature(trail: &Trail) -> Signature {
    let mut constants = HashSet::new();
    let mut functions = HashMap::new();

    for clause in trail.clauses() {
        for lit in &clause.clause.literals {
            for arg in &lit.atom.args {
                collect_symbols(arg, &mut constants, &mut functions);
            }
        }
    }

    Signature {
        constants,
        functions,
    }
}

/// Recursively collect constants and function symbols from a term.
fn collect_symbols(
    term: &Term,
    constants: &mut HashSet<String>,
    functions: &mut HashMap<String, usize>,
) {
    match term {
        Term::Var(_) => {}
        Term::App(sym, args) => {
            if args.is_empty() {
                constants.insert(sym.name.clone());
            } else {
                functions.insert(sym.name.clone(), args.len());
            }
            for arg in args {
                collect_symbols(arg, constants, functions);
            }
        }
    }
}

/// Check if `earlier_constraint` entails `clause_constraint` after applying substitution.
///
/// This handles constraint subsumption for s-split representatives:
/// - `P(f(w), g(z)) | True` subsumes `P(x, y) | root(x) = f ∧ root(y) = g`
/// - After MGU {x -> f(w), y -> g(z)}, the constraint becomes `root(f(w)) = f ∧ root(g(z)) = g`
/// - This is trivially true because the root of f(w) IS f, and root of g(z) IS g.
fn constraint_entails_after_subst(
    earlier_constraint: &Constraint,
    clause_constraint: &Constraint,
    mgu: &Substitution,
) -> bool {
    // Apply substitution to both constraints
    let earlier_applied = earlier_constraint.apply_subst(mgu);
    let clause_applied = clause_constraint.apply_subst(mgu);

    // Simplify the clause constraint after substitution
    let clause_simplified = clause_applied.simplify_ground();

    // Check if earlier (after subst) entails clause (after subst and simplification)
    // For True entails anything trivially true, we return true
    if matches!(clause_simplified, Constraint::True) {
        return true;
    }

    // If earlier is True, it only entails True
    if matches!(earlier_applied, Constraint::True) {
        return matches!(clause_simplified, Constraint::True);
    }

    // General case: A |= B iff A ∧ ¬B is unsatisfiable
    let a_and_not_b = earlier_applied.and(!clause_simplified);
    !a_and_not_b.is_satisfiable()
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
    fn test_disposable_example_2_simple_sequences() {
        // Source: bonacina2016.pdf, Example 2 (disposable clauses in unit sequences).
        // Gamma = P(x), not Q(x), P(x): the second P(x) is disposable.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
        trail.push(unit(Literal::neg("Q", vec![Term::var("x")])));
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));

        let clause = &trail.clauses()[2];
        assert!(is_disposable(clause, &trail));
    }

    #[test]
    fn test_not_disposable_example_2_negative_prefix() {
        // Source: bonacina2016.pdf, Example 2.
        // Gamma = not P(x), not Q(x), P(x): P(x) is not disposable.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::neg("P", vec![Term::var("x")])));
        trail.push(unit(Literal::neg("Q", vec![Term::var("x")])));
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));

        let clause = &trail.clauses()[2];
        assert!(!is_disposable(clause, &trail));
    }

    #[test]
    fn test_not_disposable_example_2_duplicate_negative() {
        // Source: bonacina2016.pdf, Example 2.
        // Gamma = P(x), not P(x), not P(x): neither occurrence of not P(x) is disposable.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
        trail.push(unit(Literal::neg("P", vec![Term::var("x")])));
        trail.push(unit(Literal::neg("P", vec![Term::var("x")])));

        let clause1 = &trail.clauses()[1];
        let clause2 = &trail.clauses()[2];
        assert!(!is_disposable(clause1, &trail));
        assert!(!is_disposable(clause2, &trail));
    }

    #[test]
    fn test_disposable_example_2_signature_a_f() {
        // Source: bonacina2016.pdf, Example 2 (signature with one constant a and one function f).
        // In P(a), P(f(x)), P(z), the last P(z) is disposable.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));
        trail.push(unit(Literal::pos(
            "P",
            vec![Term::app("f", vec![Term::var("x")])],
        )));
        trail.push(unit(Literal::pos("P", vec![Term::var("z")])));

        let clause = &trail.clauses()[2];
        assert!(is_disposable(clause, &trail));
    }

    #[test]
    fn test_disposable_example_2_signature_a_f_reverse() {
        // Source: bonacina2016.pdf, Example 2.
        // In P(z), P(a), P(f(x)), then P(a) and P(f(x)) are disposable.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::var("z")])));
        trail.push(unit(Literal::pos("P", vec![Term::constant("a")])));
        trail.push(unit(Literal::pos(
            "P",
            vec![Term::app("f", vec![Term::var("x")])],
        )));

        let clause1 = &trail.clauses()[1];
        let clause2 = &trail.clauses()[2];
        assert!(is_disposable(clause1, &trail));
        assert!(is_disposable(clause2, &trail));
    }

    #[test]
    fn test_sggs_deletion_removes_disposable_clause() {
        // Source: bonacina2016.pdf, Example 2 (SGGS-deletion removes disposable clauses).
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
        trail.push(unit(Literal::neg("Q", vec![Term::var("x")])));
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));

        sggs_deletion(&mut trail);

        assert_eq!(trail.clauses().len(), 2);
        let count_p = trail
            .clauses()
            .iter()
            .filter(|c| c.selected_literal() == &Literal::pos("P", vec![Term::var("x")]))
            .count();
        let count_not_q = trail
            .clauses()
            .iter()
            .filter(|c| c.selected_literal() == &Literal::neg("Q", vec![Term::var("x")]))
            .count();
        assert_eq!(count_p, 1);
        assert_eq!(count_not_q, 1);
    }

    #[test]
    fn test_single_clause_not_disposable() {
        // By Def. 6, no clause in the disjoint prefix is disposable.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
        let clause = &trail.clauses()[0];
        assert!(!is_disposable(clause, &trail));
    }

    #[test]
    fn test_deletion_removes_unsatisfiable_constraint_clause() {
        // A clause with no constrained ground instances is disposable.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(ConstrainedClause::with_constraint(
            Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
            Constraint::False,
            0,
        ));

        sggs_deletion(&mut trail);
        assert!(trail.clauses().is_empty());
    }

    #[test]
    fn test_deletion_removes_all_disposable_clauses() {
        // Multiple disposable clauses should all be removed in one deletion pass.
        let mut trail = Trail::new(crate::sggs::InitialInterpretation::AllNegative);
        trail.push(unit(Literal::pos("P", vec![Term::var("x")])));
        trail.push(unit(Literal::neg("Q", vec![Term::var("x")])));
        trail.push(unit(Literal::pos("P", vec![Term::var("x")]))); // disposable
        trail.push(unit(Literal::pos("P", vec![Term::var("x")]))); // disposable

        sggs_deletion(&mut trail);

        let count_p = trail
            .clauses()
            .iter()
            .filter(|c| c.selected_literal() == &Literal::pos("P", vec![Term::var("x")]))
            .count();
        let count_not_q = trail
            .clauses()
            .iter()
            .filter(|c| c.selected_literal() == &Literal::neg("Q", vec![Term::var("x")]))
            .count();
        assert_eq!(count_p, 1, "only one P(x) should remain");
        assert_eq!(count_not_q, 1, "Q(x) clause should remain");
    }
}
