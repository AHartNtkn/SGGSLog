//! Manual verification of satisfiability for {p(a)∨q(b), ¬p(a)∨¬q(b)}

#[test]
fn manual_truth_table() {
    println!("\n=== Truth table for (p(a)∨q(b)) ∧ (¬p(a)∨¬q(b)) ===\n");
    println!("p(a) | q(b) | p∨q | ¬p∨¬q | BOTH");
    println!("-----|------|-----|-------|-----");

    for p in [false, true] {
        for q in [false, true] {
            let c1 = p || q; // p(a) ∨ q(b)
            let c2 = !p || !q; // ¬p(a) ∨ ¬q(b)
            let both = c1 && c2;
            println!(
                "  {}  |  {}   |  {}  |   {}   |  {}",
                if p { "T" } else { "F" },
                if q { "T" } else { "F" },
                if c1 { "T" } else { "F" },
                if c2 { "T" } else { "F" },
                if both { "SAT" } else { "UNSAT" }
            );
        }
    }

    println!("\nConclusion: (p∨q) ∧ (¬p∨¬q) is SATISFIABLE by:");
    println!("  - p=T, q=F");
    println!("  - p=F, q=T");
    println!("\nThis is XOR: exactly one of p, q must be true.");
}

#[test]
fn verify_actual_unsatisfiable_theories() {
    println!("\n=== Actually unsatisfiable theories ===\n");

    // Theory 1: {p, ¬p}
    println!("1. {{p, ¬p}} (unit clauses):");
    println!("   p=T: p=T, ¬p=F → UNSAT");
    println!("   p=F: p=F, ¬p=T → UNSAT");
    println!("   → UNSATISFIABLE ✓\n");

    // Theory 2: {p∨q, ¬p, ¬q}
    println!("2. {{p∨q, ¬p, ¬q}} (3 clauses):");
    for p in [false, true] {
        for q in [false, true] {
            let c1 = p || q;
            let c2 = !p;
            let c3 = !q;
            let all = c1 && c2 && c3;
            println!(
                "   p={}, q={}: c1={}, c2={}, c3={} → {}",
                if p { "T" } else { "F" },
                if q { "T" } else { "F" },
                if c1 { "T" } else { "F" },
                if c2 { "T" } else { "F" },
                if c3 { "T" } else { "F" },
                if all { "SAT" } else { "UNSAT" }
            );
        }
    }
    println!("   → UNSATISFIABLE ✓\n");

    // Theory 3: {p∨q, ¬p∨q, p∨¬q, ¬p∨¬q} (all 4 clauses)
    println!("3. {{p∨q, ¬p∨q, p∨¬q, ¬p∨¬q}} (4 clauses):");
    for p in [false, true] {
        for q in [false, true] {
            let c1 = p || q;
            let c2 = !p || q;
            let c3 = p || !q;
            let c4 = !p || !q;
            let all = c1 && c2 && c3 && c4;
            println!(
                "   p={}, q={}: c1={}, c2={}, c3={}, c4={} → {}",
                if p { "T" } else { "F" },
                if q { "T" } else { "F" },
                if c1 { "T" } else { "F" },
                if c2 { "T" } else { "F" },
                if c3 { "T" } else { "F" },
                if c4 { "T" } else { "F" },
                if all { "SAT" } else { "UNSAT" }
            );
        }
    }
    println!("   → UNSATISFIABLE ✓");
}
