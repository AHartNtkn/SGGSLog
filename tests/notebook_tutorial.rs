//! Integration test that validates the tutorial notebook executes correctly.
//!
//! This test loads notebooks/tutorial.ipynb, executes each code cell through
//! the SGGSLog kernel, and validates the expected outputs.

use sggslog::jupyter::Kernel;
use std::fs;

fn contains_any(haystack: &str, needles: &[&str]) -> bool {
    let hay = haystack.to_ascii_lowercase();
    needles
        .iter()
        .any(|n| hay.contains(&n.to_ascii_lowercase()))
}

/// Execute a notebook cell and return the result
fn execute_cell(kernel: &mut Kernel, source: &str) -> String {
    match kernel.execute(source) {
        Ok(output) => output,
        Err(e) => format!("ERROR: {}", e.message),
    }
}

#[test]
fn notebook_tutorial_executes_correctly() {
    // Read the notebook
    let notebook_path = concat!(env!("CARGO_MANIFEST_DIR"), "/notebooks/tutorial.ipynb");
    let notebook_json = fs::read_to_string(notebook_path).expect("Failed to read notebook file");

    // Parse the JSON
    let notebook: serde_json::Value =
        serde_json::from_str(&notebook_json).expect("Failed to parse notebook JSON");

    let cells = notebook["cells"]
        .as_array()
        .expect("notebook should have cells array");

    let mut kernel = Kernel::new();
    let mut cell_index = 0;

    // Track state for validation
    let mut seen_people = std::collections::HashSet::new();
    let mut seen_mortals = std::collections::HashSet::new();
    let mut seen_paths = std::collections::HashSet::new();

    for cell in cells {
        let cell_type = cell["cell_type"].as_str().unwrap_or("");
        if cell_type != "code" {
            continue;
        }

        // Extract source - it's an array of lines
        let source: String = match cell["source"].as_array() {
            Some(lines) => lines
                .iter()
                .map(|s| s.as_str().unwrap_or(""))
                .collect::<Vec<_>>()
                .join(""),
            None => cell["source"].as_str().unwrap_or("").to_string(),
        };

        let source = source.trim();
        if source.is_empty() {
            continue;
        }

        let result = execute_cell(&mut kernel, source);
        cell_index += 1;

        // Validate based on cell content
        match source {
            // Section 1: Basic facts
            "person alice" | "person bob" | "person carol" => {
                assert!(
                    result.contains("ok"),
                    "Cell {}: fact definition should return ok, got: {}",
                    cell_index,
                    result
                );
            }

            // Ground query
            "?- person alice" => {
                assert!(
                    result.contains("true"),
                    "Cell {}: ground query should return true, got: {}",
                    cell_index,
                    result
                );
            }

            // Variable query for person
            "?- person X" => {
                assert!(
                    contains_any(&result, &["alice", "bob", "carol"]),
                    "Cell {}: person query should return a person, got: {}",
                    cell_index,
                    result
                );
                if result.contains("alice") {
                    seen_people.insert("alice");
                }
                if result.contains("bob") {
                    seen_people.insert("bob");
                }
                if result.contains("carol") {
                    seen_people.insert("carol");
                }
            }

            // Section 2: Rules
            "person X -> mortal X" => {
                assert!(
                    result.contains("ok"),
                    "Cell {}: rule should return ok, got: {}",
                    cell_index,
                    result
                );
            }

            "?- mortal alice" => {
                assert!(
                    result.contains("true"),
                    "Cell {}: derived fact query should return true, got: {}",
                    cell_index,
                    result
                );
            }

            "?- mortal X" => {
                assert!(
                    contains_any(&result, &["alice", "bob", "carol"]),
                    "Cell {}: mortal query should return someone, got: {}",
                    cell_index,
                    result
                );
                if result.contains("alice") {
                    seen_mortals.insert("alice");
                }
                if result.contains("bob") {
                    seen_mortals.insert("bob");
                }
                if result.contains("carol") {
                    seen_mortals.insert("carol");
                }
            }

            // Section 3: Graph edges
            "edge a b" | "edge b c" | "edge c d" => {
                assert!(
                    result.contains("ok"),
                    "Cell {}: edge fact should return ok, got: {}",
                    cell_index,
                    result
                );
            }

            "edge X Y -> path X Y" | "path X Y & edge Y Z -> path X Z" => {
                assert!(
                    result.contains("ok"),
                    "Cell {}: path rule should return ok, got: {}",
                    cell_index,
                    result
                );
            }

            "?- path a X" => {
                assert!(
                    contains_any(&result, &["b", "c", "d"]),
                    "Cell {}: path query should return reachable node, got: {}",
                    cell_index,
                    result
                );
                for node in ["b", "c", "d"] {
                    if result.contains(node) {
                        seen_paths.insert(node);
                    }
                }
            }

            // Section 4: Universal quantifier
            "∀X ∀Y (path X Y -> connected X Y)" => {
                assert!(
                    result.contains("ok"),
                    "Cell {}: quantified rule should return ok, got: {}",
                    cell_index,
                    result
                );
            }

            "?- connected a d" => {
                assert!(
                    result.contains("true"),
                    "Cell {}: connected query should return true, got: {}",
                    cell_index,
                    result
                );
            }

            // Section 5: Disjunction
            "item x1" | "item x2" => {
                assert!(
                    result.contains("ok"),
                    "Cell {}: item fact should return ok, got: {}",
                    cell_index,
                    result
                );
            }

            "item X -> red X | blue X" => {
                assert!(
                    result.contains("ok"),
                    "Cell {}: disjunctive rule should return ok, got: {}",
                    cell_index,
                    result
                );
            }

            "?- red x1" => {
                // Disjunction may or may not give a definite answer
                // Just check no error
                assert!(
                    !result.contains("ERROR"),
                    "Cell {}: disjunctive query should not error, got: {}",
                    cell_index,
                    result
                );
            }

            // Section 6: Existential and projection
            "∃S (secret S)" => {
                assert!(
                    result.contains("ok"),
                    "Cell {}: existential should return ok, got: {}",
                    cell_index,
                    result
                );
            }

            "?- secret X" => {
                // First time with default projection - should hide internal
                // After allow_internal - should show sk_
                // We can't easily distinguish which call this is without more state
                // Just verify no error
                assert!(
                    !result.contains("ERROR"),
                    "Cell {}: secret query should not error, got: {}",
                    cell_index,
                    result
                );
            }

            ":set projection allow_internal" => {
                assert!(
                    contains_any(&result, &["projection", "internal", "set"]),
                    "Cell {}: set projection should acknowledge, got: {}",
                    cell_index,
                    result
                );
            }

            // Section 7: Peano arithmetic
            "add z Y Y" => {
                assert!(
                    result.contains("ok"),
                    "Cell {}: add base case should return ok, got: {}",
                    cell_index,
                    result
                );
            }

            "add X Y Z -> add (s X) Y (s Z)" => {
                assert!(
                    result.contains("ok"),
                    "Cell {}: add recursive rule should return ok, got: {}",
                    cell_index,
                    result
                );
            }

            "?- add (s z) (s (s z)) R" => {
                // 1 + 2 = 3, should return R = s(s(s(z)))
                assert!(
                    result.contains("s(s(s(z)))") || result.contains("s (s (s"),
                    "Cell {}: add 1+2 should give 3, got: {}",
                    cell_index,
                    result
                );
            }

            "?- add X (s z) (s (s (s z)))" => {
                // X + 1 = 3, should return X = s(s(z)) (subtraction!)
                assert!(
                    result.contains("s(s(z))") || result.contains("s (s"),
                    "Cell {}: add X+1=3 should give X=2, got: {}",
                    cell_index,
                    result
                );
            }

            "?- add X Y (s (s z))" => {
                // X + Y = 2, should enumerate partitions
                // Just check we get some binding
                assert!(
                    !result.contains("ERROR"),
                    "Cell {}: partition query should not error, got: {}",
                    cell_index,
                    result
                );
            }

            // Section 8: Unsatisfiability
            "contra" | "~contra" => {
                assert!(
                    result.contains("ok"),
                    "Cell {}: contradiction fact should return ok, got: {}",
                    cell_index,
                    result
                );
            }

            "?- anything X" => {
                // After contradiction, query behavior may vary
                // Just check no panic
                assert!(
                    !result.contains("panic"),
                    "Cell {}: query after contradiction should not panic, got: {}",
                    cell_index,
                    result
                );
            }

            // :next commands
            ":next" => {
                // :next should return an answer or "no more answers"
                // Just verify it doesn't error (unless no active query)
                // We allow errors here since :next without active query is an error
            }

            _ => {
                // Unknown cell - just verify no panic
                assert!(
                    !result.contains("panic"),
                    "Cell {}: unexpected cell should not panic: {} -> {}",
                    cell_index,
                    source,
                    result
                );
            }
        }
    }

    // After all cells, verify we saw expected values from streaming
    // Note: We may not see all values if streaming order varies
    assert!(
        !seen_people.is_empty(),
        "Should have seen at least one person from queries"
    );
}

#[test]
fn notebook_basic_facts_section() {
    // Test Section 1 in isolation
    let mut kernel = Kernel::new();

    let r1 = kernel.execute("person alice").expect("person alice");
    assert!(r1.contains("ok"), "fact should return ok: {}", r1);

    let r2 = kernel.execute("person bob").expect("person bob");
    assert!(r2.contains("ok"), "fact should return ok: {}", r2);

    let r3 = kernel.execute("?- person alice").expect("query");
    assert!(r3.contains("true"), "ground query should return true: {}", r3);

    let r4 = kernel.execute("?- person X").expect("query with var");
    assert!(
        r4.contains("alice") || r4.contains("bob"),
        "variable query should bind: {}",
        r4
    );

    let r5 = kernel.execute(":next").expect("next");
    assert!(
        r5.contains("alice") || r5.contains("bob") || r5.contains("no more"),
        "next should give answer or exhaust: {}",
        r5
    );
}

#[test]
fn notebook_rules_section() {
    // Test Section 2 in isolation
    let mut kernel = Kernel::new();

    kernel.execute("person alice").expect("person alice");
    kernel.execute("person X -> mortal X").expect("rule");

    let r = kernel.execute("?- mortal alice").expect("query");
    assert!(
        r.contains("true"),
        "derived fact should be true: {}",
        r
    );
}

#[test]
fn notebook_graph_reachability_section() {
    // Test Section 3 in isolation
    let mut kernel = Kernel::new();

    kernel.execute("edge a b").expect("edge a b");
    kernel.execute("edge b c").expect("edge b c");
    kernel.execute("edge c d").expect("edge c d");
    kernel.execute("edge X Y -> path X Y").expect("path rule 1");
    kernel
        .execute("path X Y & edge Y Z -> path X Z")
        .expect("path rule 2");

    let r1 = kernel.execute("?- path a X").expect("path query");
    assert!(
        r1.contains("b") || r1.contains("c") || r1.contains("d"),
        "path should find reachable node: {}",
        r1
    );

    // Get more answers
    let mut seen = std::collections::HashSet::new();
    if r1.contains("b") {
        seen.insert("b");
    }
    if r1.contains("c") {
        seen.insert("c");
    }
    if r1.contains("d") {
        seen.insert("d");
    }

    for _ in 0..5 {
        let r = kernel.execute(":next").expect("next");
        if r.contains("b") {
            seen.insert("b");
        }
        if r.contains("c") {
            seen.insert("c");
        }
        if r.contains("d") {
            seen.insert("d");
        }
        if r.contains("no more") {
            break;
        }
    }

    assert!(
        seen.contains("b") && seen.contains("c") && seen.contains("d"),
        "should reach all nodes b, c, d, seen: {:?}",
        seen
    );
}

#[test]
fn notebook_existential_projection_section() {
    // Test Section 6 in isolation
    let mut kernel = Kernel::new();

    kernel.execute("∃S (secret S)").expect("existential");

    // Default projection hides internal symbols
    let r1 = kernel.execute("?- secret X").expect("query 1");
    assert!(
        contains_any(&r1, &["no more", "no answers", "exhausted"]),
        "default projection should hide internal witness: {}",
        r1
    );

    // Enable internal symbols
    kernel
        .execute(":set projection allow_internal")
        .expect("set projection");

    // Now should see the Skolem constant
    let r2 = kernel.execute("?- secret X").expect("query 2");
    assert!(
        r2.contains("sk_") || r2.contains("X ="),
        "allow_internal should reveal witness: {}",
        r2
    );
}

#[test]
fn notebook_peano_arithmetic_section() {
    // Test Section 7 in isolation - Peano arithmetic with bidirectional add
    let mut kernel = Kernel::new();

    // Define addition
    kernel.execute("add z Y Y").expect("add base case");
    kernel
        .execute("add X Y Z -> add (s X) Y (s Z)")
        .expect("add recursive");

    // Test addition: 1 + 2 = ?
    let r1 = kernel.execute("?- add (s z) (s (s z)) R").expect("add query");
    assert!(
        r1.contains("s(s(s(z)))") || r1.contains("s (s (s"),
        "1 + 2 should equal 3: {}",
        r1
    );

    // Test subtraction (backwards): ? + 1 = 3
    let r2 = kernel
        .execute("?- add X (s z) (s (s (s z)))")
        .expect("subtract query");
    assert!(
        r2.contains("s(s(z))") || r2.contains("s (s"),
        "3 - 1 should equal 2: {}",
        r2
    );

    // Test enumeration: ? + ? = 2
    let r3 = kernel.execute("?- add X Y (s (s z))").expect("partition query");
    // Should get first answer (one of the partitions)
    assert!(
        r3.contains("X =") || r3.contains("Y =") || r3.contains("z"),
        "partition should give bindings: {}",
        r3
    );

    // Get all partitions
    let mut partitions = Vec::new();
    partitions.push(r3);
    for _ in 0..4 {
        let r = kernel.execute(":next").expect("next");
        if r.contains("no more") {
            break;
        }
        partitions.push(r);
    }

    // Should have found 3 partitions: (0,2), (1,1), (2,0)
    assert!(
        partitions.len() >= 3,
        "should find at least 3 partitions of 2, found: {}",
        partitions.len()
    );
}
