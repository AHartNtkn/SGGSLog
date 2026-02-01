//! Normalization (clausification) from surface formulas to clauses.

use crate::parser::Statement;
use crate::syntax::{Clause, Formula, Literal, Term, Var};
use std::collections::HashMap;

/// Error during normalization.
#[derive(Debug, Clone)]
pub struct NormalizeError {
    pub message: String,
}

impl std::fmt::Display for NormalizeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for NormalizeError {}

/// Skolem symbol generator.
struct SkolemGen {
    counter: usize,
}

impl SkolemGen {
    fn new() -> Self {
        SkolemGen { counter: 0 }
    }

    fn fresh_with_sort(&mut self, sort: Option<&str>) -> (String, Option<String>) {
        let name = format!("$sk{}", self.counter);
        self.counter += 1;
        (name, sort.map(|s| s.to_string()))
    }
}

/// Normalize a formula into a set of clauses (CNF + Skolemization).
pub fn clausify_formula(formula: &Formula) -> Result<Vec<Clause>, NormalizeError> {
    let mut skolem_gen = SkolemGen::new();
    clausify_formula_with_skolem(formula, &mut skolem_gen)
}

fn clausify_formula_with_skolem(
    formula: &Formula,
    skolem_gen: &mut SkolemGen,
) -> Result<Vec<Clause>, NormalizeError> {
    // Step 1: Eliminate implications
    let no_implies = eliminate_implications(formula);

    // Step 2: Push negations inward (NNF)
    let nnf = to_nnf(&no_implies);

    // Step 3: Skolemize (remove existentials)
    let skolemized = skolemize(&nnf, &[], skolem_gen, &HashMap::new());

    // Step 4: Drop universal quantifiers
    let quantifier_free = drop_universals(&skolemized);

    // Step 5: Convert to CNF
    let cnf = to_cnf(&quantifier_free);

    // Step 6: Extract clauses
    let clauses = extract_clauses(&cnf);

    Ok(clauses)
}

/// Eliminate implications: p → q ≡ ¬p ∨ q
fn eliminate_implications(formula: &Formula) -> Formula {
    match formula {
        Formula::Atom(atom) => Formula::Atom(atom.clone()),
        Formula::Not(inner) => Formula::negation(eliminate_implications(inner)),
        Formula::And(left, right) => {
            Formula::and(eliminate_implications(left), eliminate_implications(right))
        }
        Formula::Or(left, right) => {
            Formula::or(eliminate_implications(left), eliminate_implications(right))
        }
        Formula::Implies(left, right) => {
            // p → q ≡ ¬p ∨ q
            Formula::or(
                Formula::negation(eliminate_implications(left)),
                eliminate_implications(right),
            )
        }
        Formula::Forall(var, body) => Formula::forall(var.clone(), eliminate_implications(body)),
        Formula::Exists(var, body) => Formula::exists(var.clone(), eliminate_implications(body)),
    }
}

/// Convert to Negation Normal Form (push negations inward).
fn to_nnf(formula: &Formula) -> Formula {
    match formula {
        Formula::Atom(atom) => Formula::Atom(atom.clone()),
        Formula::Not(inner) => negate_nnf(inner),
        Formula::And(left, right) => Formula::and(to_nnf(left), to_nnf(right)),
        Formula::Or(left, right) => Formula::or(to_nnf(left), to_nnf(right)),
        Formula::Implies(_, _) => {
            // Should have been eliminated
            panic!("implications should be eliminated before NNF conversion")
        }
        Formula::Forall(var, body) => Formula::forall(var.clone(), to_nnf(body)),
        Formula::Exists(var, body) => Formula::exists(var.clone(), to_nnf(body)),
    }
}

/// Negate a formula and push negations inward.
fn negate_nnf(formula: &Formula) -> Formula {
    match formula {
        Formula::Atom(atom) => Formula::Not(Box::new(Formula::Atom(atom.clone()))),
        Formula::Not(inner) => to_nnf(inner), // Double negation elimination
        Formula::And(left, right) => {
            // De Morgan: ¬(p ∧ q) ≡ ¬p ∨ ¬q
            Formula::or(negate_nnf(left), negate_nnf(right))
        }
        Formula::Or(left, right) => {
            // De Morgan: ¬(p ∨ q) ≡ ¬p ∧ ¬q
            Formula::and(negate_nnf(left), negate_nnf(right))
        }
        Formula::Implies(_, _) => {
            panic!("implications should be eliminated before NNF conversion")
        }
        Formula::Forall(var, body) => {
            // ¬∀x.P ≡ ∃x.¬P
            Formula::exists(var.clone(), negate_nnf(body))
        }
        Formula::Exists(var, body) => {
            // ¬∃x.P ≡ ∀x.¬P
            Formula::forall(var.clone(), negate_nnf(body))
        }
    }
}

/// Skolemize: replace existentially quantified variables with Skolem terms.
fn skolemize(
    formula: &Formula,
    universal_vars: &[Var],
    skolem_gen: &mut SkolemGen,
    var_mapping: &HashMap<String, Term>,
) -> Formula {
    match formula {
        Formula::Atom(atom) => {
            let args = atom
                .args
                .iter()
                .map(|arg| apply_var_mapping(arg, var_mapping))
                .collect();
            Formula::Atom(crate::syntax::Atom::new(atom.predicate.clone(), args))
        }
        Formula::Not(inner) => {
            Formula::negation(skolemize(inner, universal_vars, skolem_gen, var_mapping))
        }
        Formula::And(left, right) => Formula::and(
            skolemize(left, universal_vars, skolem_gen, var_mapping),
            skolemize(right, universal_vars, skolem_gen, var_mapping),
        ),
        Formula::Or(left, right) => Formula::or(
            skolemize(left, universal_vars, skolem_gen, var_mapping),
            skolemize(right, universal_vars, skolem_gen, var_mapping),
        ),
        Formula::Implies(_, _) => panic!("implications should be eliminated before Skolemization"),
        Formula::Forall(var, body) => {
            // Add this variable to the universal scope
            let mut new_universals = universal_vars.to_vec();
            new_universals.push(var.clone());
            Formula::forall(
                var.clone(),
                skolemize(body, &new_universals, skolem_gen, var_mapping),
            )
        }
        Formula::Exists(var, body) => {
            // Replace with Skolem term
            // Filter out universals that are shadowed by this existential variable
            let effective_universals: Vec<&Var> = universal_vars
                .iter()
                .filter(|v| v.name() != var.name())
                .collect();

            let (sk_name, sk_sort) = skolem_gen.fresh_with_sort(var.sort());
            let sk_term = if effective_universals.is_empty() {
                // Skolem constant
                if let Some(sort) = sk_sort {
                    Term::constant_with_sort(sk_name, sort)
                } else {
                    Term::constant(sk_name)
                }
            } else {
                // Skolem function applied to universal variables (excluding shadowed ones)
                let args: Vec<Term> = effective_universals
                    .iter()
                    .map(|v| {
                        // Check if this var has been mapped
                        if let Some(mapped) = var_mapping.get(v.name()) {
                            mapped.clone()
                        } else {
                            Term::Var((*v).clone())
                        }
                    })
                    .collect();
                if let Some(sort) = sk_sort {
                    Term::app_with_sort(sk_name, sort, args)
                } else {
                    Term::app(sk_name, args)
                }
            };

            // Add mapping for this existential variable
            let mut new_mapping = var_mapping.clone();
            new_mapping.insert(var.name().to_string(), sk_term);

            skolemize(body, universal_vars, skolem_gen, &new_mapping)
        }
    }
}

/// Apply variable mappings to a term.
fn apply_var_mapping(term: &Term, var_mapping: &HashMap<String, Term>) -> Term {
    match term {
        Term::Var(v) => {
            if let Some(mapped) = var_mapping.get(v.name()) {
                mapped.clone()
            } else {
                Term::Var(v.clone())
            }
        }
        Term::App(fn_sym, args) => {
            let new_args = args
                .iter()
                .map(|arg| apply_var_mapping(arg, var_mapping))
                .collect();
            Term::App(fn_sym.clone(), new_args)
        }
    }
}

/// Drop universal quantifiers (they become implicit).
fn drop_universals(formula: &Formula) -> Formula {
    match formula {
        Formula::Atom(atom) => Formula::Atom(atom.clone()),
        Formula::Not(inner) => Formula::negation(drop_universals(inner)),
        Formula::And(left, right) => Formula::and(drop_universals(left), drop_universals(right)),
        Formula::Or(left, right) => Formula::or(drop_universals(left), drop_universals(right)),
        Formula::Implies(_, _) => panic!("implications should be eliminated"),
        Formula::Forall(_, body) => drop_universals(body),
        Formula::Exists(_, _) => panic!("existentials should be Skolemized"),
    }
}

/// Convert to Conjunctive Normal Form (CNF).
/// Uses distribution: p ∨ (q ∧ r) ≡ (p ∨ q) ∧ (p ∨ r)
fn to_cnf(formula: &Formula) -> Formula {
    match formula {
        Formula::Atom(_) | Formula::Not(_) => formula.clone(),
        Formula::And(left, right) => Formula::and(to_cnf(left), to_cnf(right)),
        Formula::Or(left, right) => {
            let left_cnf = to_cnf(left);
            let right_cnf = to_cnf(right);
            distribute_or(&left_cnf, &right_cnf)
        }
        Formula::Implies(_, _) => panic!("implications should be eliminated"),
        Formula::Forall(_, _) | Formula::Exists(_, _) => {
            panic!("quantifiers should be removed")
        }
    }
}

/// Distribute disjunction over conjunction.
fn distribute_or(left: &Formula, right: &Formula) -> Formula {
    match (left, right) {
        (Formula::And(a, b), _) => {
            // (a ∧ b) ∨ c ≡ (a ∨ c) ∧ (b ∨ c)
            Formula::and(distribute_or(a, right), distribute_or(b, right))
        }
        (_, Formula::And(a, b)) => {
            // c ∨ (a ∧ b) ≡ (c ∨ a) ∧ (c ∨ b)
            Formula::and(distribute_or(left, a), distribute_or(left, b))
        }
        _ => Formula::or(left.clone(), right.clone()),
    }
}

/// Extract clauses from a CNF formula.
fn extract_clauses(formula: &Formula) -> Vec<Clause> {
    match formula {
        Formula::And(left, right) => {
            let mut clauses = extract_clauses(left);
            clauses.extend(extract_clauses(right));
            clauses
        }
        _ => {
            // Single clause (disjunction of literals)
            let literals = extract_literals(formula);
            vec![Clause::new(literals)]
        }
    }
}

/// Extract literals from a disjunction.
fn extract_literals(formula: &Formula) -> Vec<Literal> {
    match formula {
        Formula::Atom(atom) => vec![Literal::positive(atom.clone())],
        Formula::Not(inner) => match inner.as_ref() {
            Formula::Atom(atom) => vec![Literal::negative(atom.clone())],
            _ => panic!("NNF should have negation only on atoms"),
        },
        Formula::Or(left, right) => {
            let mut literals = extract_literals(left);
            literals.extend(extract_literals(right));
            literals
        }
        Formula::And(_, _) => panic!("conjunction in disjunction context"),
        _ => panic!("unexpected formula in clause extraction"),
    }
}

/// Normalize a single statement into clauses.
pub fn clausify_statement(stmt: &Statement) -> Result<Vec<Clause>, NormalizeError> {
    let mut skolem_gen = SkolemGen::new();
    clausify_statement_with_skolem(stmt, &mut skolem_gen)
}

fn clausify_statement_with_skolem(
    stmt: &Statement,
    skolem_gen: &mut SkolemGen,
) -> Result<Vec<Clause>, NormalizeError> {
    match stmt {
        Statement::Clause(clause) => Ok(vec![clause.clone()]),
        Statement::Formula(formula) => clausify_formula_with_skolem(formula, skolem_gen),
        Statement::Query(_) => Err(NormalizeError {
            message: "cannot clausify a query statement".to_string(),
        }),
        Statement::Directive(_) => Err(NormalizeError {
            message: "cannot clausify a directive statement".to_string(),
        }),
    }
}

/// Normalize a list of statements into clauses.
///
/// This should use a single Skolem symbol generator across all statements.
pub fn clausify_statements(stmts: &[Statement]) -> Result<Vec<Clause>, NormalizeError> {
    let mut skolem_gen = SkolemGen::new();
    let mut all_clauses = Vec::new();

    for stmt in stmts {
        match stmt {
            Statement::Query(_) | Statement::Directive(_) => {
                // Skip queries and directives when clausifying statements
                continue;
            }
            _ => {
                let clauses = clausify_statement_with_skolem(stmt, &mut skolem_gen)?;
                all_clauses.extend(clauses);
            }
        }
    }

    Ok(all_clauses)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::Atom;

    fn atom(name: &str) -> Formula {
        Formula::atom(Atom::prop(name))
    }

    #[test]
    fn test_eliminate_implication() {
        let formula = Formula::implies(atom("p"), atom("q"));
        let result = eliminate_implications(&formula);

        match result {
            Formula::Or(left, right) => {
                assert!(matches!(left.as_ref(), Formula::Not(_)));
                assert!(matches!(right.as_ref(), Formula::Atom(_)));
            }
            _ => panic!("expected disjunction"),
        }
    }

    #[test]
    fn test_double_negation_elimination() {
        let formula = Formula::negation(Formula::negation(atom("p")));
        let result = to_nnf(&formula);
        assert!(matches!(result, Formula::Atom(_)));
    }

    #[test]
    fn test_demorgan_or() {
        // ¬(p ∨ q) should become ¬p ∧ ¬q
        let formula = Formula::negation(Formula::or(atom("p"), atom("q")));
        let result = to_nnf(&formula);

        match result {
            Formula::And(left, right) => {
                assert!(matches!(left.as_ref(), Formula::Not(_)));
                assert!(matches!(right.as_ref(), Formula::Not(_)));
            }
            _ => panic!("expected conjunction"),
        }
    }

    #[test]
    fn test_clausify_simple() {
        let formula = atom("p");
        let clauses = clausify_formula(&formula).unwrap();
        assert_eq!(clauses.len(), 1);
        assert_eq!(clauses[0].literals.len(), 1);
        assert!(clauses[0].literals[0].positive);
    }

    #[test]
    fn test_clausify_conjunction() {
        let formula = Formula::and(atom("p"), atom("q"));
        let clauses = clausify_formula(&formula).unwrap();
        assert_eq!(clauses.len(), 2);
    }

    #[test]
    fn test_clausify_disjunction() {
        let formula = Formula::or(atom("p"), atom("q"));
        let clauses = clausify_formula(&formula).unwrap();
        assert_eq!(clauses.len(), 1);
        assert_eq!(clauses[0].literals.len(), 2);
    }
}
