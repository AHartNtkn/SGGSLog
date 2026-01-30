use super::*;

// =============================================================================
// SGGS SPLITTING PROPERTIES
// =============================================================================
//
// Reference: [BP16a] Definitions 13-15 (partition and splitting)
use crate::constraint::Constraint;
use crate::sggs::ConstrainedClause;
use crate::unify::Substitution;
use std::collections::{HashMap, HashSet};

fn constraint_holds(c: &Constraint, subst: &Substitution) -> bool {
    match c {
        Constraint::True => true,
        Constraint::False => false,
        Constraint::Atomic(a) => a.evaluate(subst).unwrap_or(false),
        Constraint::And(a, b) => constraint_holds(a, subst) && constraint_holds(b, subst),
        Constraint::Or(a, b) => constraint_holds(a, subst) || constraint_holds(b, subst),
        Constraint::Not(a) => !constraint_holds(a, subst),
    }
}

fn ground_atoms_for_clause(clause: &ConstrainedClause, consts: &[Term]) -> HashSet<Atom> {
    let lit = clause.selected_literal();
    let vars: HashSet<Var> = lit.variables();
    let vars: Vec<Var> = vars.into_iter().collect();
    let mut atoms = HashSet::new();

    fn assign(
        idx: usize,
        vars: &[Var],
        consts: &[Term],
        lit: &Literal,
        constraint: &Constraint,
        atoms: &mut HashSet<Atom>,
        subst: &mut Substitution,
    ) {
        if idx == vars.len() {
            if constraint_holds(constraint, subst) {
                let inst = lit.apply_subst(&subst_to_map(subst));
                atoms.insert(inst.atom);
            }
            return;
        }
        let var = vars[idx].clone();
        for c in consts {
            let mut s = subst.clone();
            s.bind(var.clone(), c.clone());
            assign(idx + 1, vars, consts, lit, constraint, atoms, &mut s);
        }
    }

    fn subst_to_map(subst: &Substitution) -> HashMap<Var, Term> {
        let mut map = HashMap::new();
        for v in subst.domain() {
            if let Some(t) = subst.lookup(v) {
                map.insert(v.clone(), t.clone());
            }
        }
        map
    }

    let mut subst = Substitution::empty();
    assign(0, &vars, consts, lit, &clause.constraint, &mut atoms, &mut subst);
    atoms
}

#[test]
fn splitting_partition_is_complete_and_disjoint() {
    let clause = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos(
            "P",
            vec![Term::var("x"), Term::var("y")],
        )]),
        Constraint::True,
        0,
    );
    let other = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos(
            "P",
            vec![
                Term::app("f", vec![Term::var("w")]),
                Term::app("g", vec![Term::var("z")]),
            ],
        )]),
        Constraint::True,
        0,
    );

    let result = crate::sggs::sggs_splitting(&clause, &other).expect("expected split result");

    let consts = vec![Term::constant("a"), Term::constant("b")];
    let original = ground_atoms_for_clause(&clause, &consts);
    let mut union = HashSet::new();

    let mut parts_atoms = Vec::new();
    for part in &result.parts {
        let atoms = ground_atoms_for_clause(part, &consts);
        for a in &atoms {
            union.insert(a.clone());
        }
        parts_atoms.push(atoms);
    }

    assert_eq!(union, original, "split parts must cover original");

    for i in 0..parts_atoms.len() {
        for j in (i + 1)..parts_atoms.len() {
            let inter: HashSet<_> = parts_atoms[i].intersection(&parts_atoms[j]).collect();
            assert!(inter.is_empty(), "split parts must be disjoint");
        }
    }
}

#[test]
fn splitting_returns_none_for_disjoint_literals() {
    let clause = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x")])]),
        Constraint::True,
        0,
    );
    let other = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("Q", vec![Term::var("y")])]),
        Constraint::True,
        0,
    );

    assert!(crate::sggs::sggs_splitting(&clause, &other).is_none());
}

#[test]
fn splitting_representative_matches_intersection() {
    let clause = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::var("x"), Term::var("y")])]),
        Constraint::True,
        0,
    );
    let other = ConstrainedClause::with_constraint(
        Clause::new(vec![Literal::pos("P", vec![Term::constant("a"), Term::var("y")])]),
        Constraint::True,
        0,
    );

    let result = crate::sggs::sggs_splitting(&clause, &other).expect("expected split result");
    let consts = vec![Term::constant("a"), Term::constant("b")];
    let original = ground_atoms_for_clause(&clause, &consts);
    let other_atoms = ground_atoms_for_clause(&other, &consts);
    let expected_intersection: HashSet<_> = original
        .intersection(&other_atoms)
        .cloned()
        .collect();

    let mut found = false;
    for part in &result.parts {
        let atoms = ground_atoms_for_clause(part, &consts);
        if atoms == expected_intersection {
            found = true;
            break;
        }
    }
    assert!(found, "split should include representative of the intersection");
}
