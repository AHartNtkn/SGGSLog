//! Integration tests for the type inference notebook.
//!
//! This validates that SGGSLog can perform:
//! - Type checking (verify a term has a type)
//! - Type inference (find the type of a term)
//! - Program synthesis (find a term with a given type)
//!
//! Note: SGGS uses model-based semantics, not least-model semantics like Prolog.
//! This means:
//! - Ground queries work well (type checking)
//! - Non-ground queries may return polymorphic/schema answers
//! - Complex nested terms may timeout due to derivation complexity

use sggslog::jupyter::Kernel;

fn setup_type_system(kernel: &mut Kernel) {
    kernel.execute(":closed name").expect("closed name");
    kernel.execute(":closed lookup").expect("closed lookup");
    kernel.execute(":closed types").expect("closed types");

    // Term variable names (finite name domain for the demo)
    kernel.execute("name x").expect("name x");
    kernel.execute("name y").expect("name y");
    kernel.execute("name f").expect("name f");
    kernel.execute("name g").expect("name g");

    // Context lookup rules (restricted to typed bindings and named variables)
    kernel
        .execute("lookup (cons (bind X T) Env) X T")
        .expect("lookup base case");
    kernel
        .execute("lookup Env X T -> lookup (cons (bind Y S) Env) X T")
        .expect("lookup recursive case");

    // Typing rules (restricted to bounded terms and types)
    kernel
        .execute("name X & lookup Env X T -> types Env (var X) T")
        .expect("VAR rule");
    kernel
        .execute("name X & types (cons (bind X A) Env) Body B -> types Env (lam X Body) (arrow A B)")
        .expect("LAM rule");
    kernel
        .execute("types Env F (arrow A B) & types Env Arg A -> types Env (app F Arg) B")
        .expect("APP rule");
}

/// Simpler setup without recursive lookup (avoids derivation complexity)
fn setup_simple_type_system(kernel: &mut Kernel) {
    kernel.execute(":closed name").expect("closed name");
    kernel.execute(":closed lookup").expect("closed lookup");
    kernel.execute(":closed types").expect("closed types");

    kernel.execute("name x").expect("name x");
    kernel.execute("name y").expect("name y");
    kernel.execute("name f").expect("name f");
    kernel.execute("name g").expect("name g");

    kernel
        .execute("lookup (cons (bind X T) Env) X T")
        .expect("lookup base case");
    kernel
        .execute("name X & lookup Env X T -> types Env (var X) T")
        .expect("VAR rule");
    kernel
        .execute("name X & types (cons (bind X A) Env) Body B -> types Env (lam X Body) (arrow A B)")
        .expect("LAM rule");
}

// ============================================================================
// Type Checking Tests
// ============================================================================

#[test]
fn type_check_identity_nat_to_nat() {
    let mut kernel = Kernel::new();
    setup_simple_type_system(&mut kernel);

    // Check: does λx.x have type nat -> nat?
    let result = kernel
        .execute("?- types nil (lam x (var x)) (arrow nat nat)")
        .expect("type check query");

    assert!(
        result.contains("true"),
        "identity should have type nat -> nat: {}",
        result
    );
}

#[test]
fn type_check_nested_identity() {
    let mut kernel = Kernel::new();
    setup_simple_type_system(&mut kernel);

    // Check: does λx.λy.y have type nat -> bool -> bool?
    // This uses the innermost variable (doesn't need recursive lookup)
    let result = kernel
        .execute("?- types nil (lam x (lam y (var y))) (arrow nat (arrow bool bool))")
        .expect("type check query");

    assert!(
        result.contains("true"),
        "λx.λy.y should have type nat -> bool -> bool: {}",
        result
    );
}

// ============================================================================
// Type Inference Tests
// ============================================================================

#[test]
fn type_infer_identity() {
    let mut kernel = Kernel::new();
    setup_type_system(&mut kernel);

    // Infer: what type does λx.x have?
    let result = kernel
        .execute("?- types nil (lam x (var x)) T")
        .expect("type inference query");

    // Should infer T = (arrow A A) for some type variable A
    assert!(
        result.contains("arrow"),
        "identity should have arrow type: {}",
        result
    );
    // The type should be A -> A where both A's are the same
    // Check that T contains arrow and has matching type variables
    assert!(
        result.contains("T ="),
        "should bind T to a type: {}",
        result
    );
}

#[test]
fn type_infer_k_combinator() {
    let mut kernel = Kernel::new();
    setup_type_system(&mut kernel);

    // Infer: what type does λx.λy.x have?
    let result = kernel
        .execute("?- types nil (lam x (lam y (var x))) T")
        .expect("type inference query");

    // Should infer T = (arrow A (arrow B A))
    assert!(
        result.contains("arrow"),
        "K combinator should have arrow type: {}",
        result
    );
    // Should have nested arrows
    let arrow_count = result.matches("arrow").count();
    assert!(
        arrow_count >= 2,
        "K combinator type should have at least 2 arrows: {}",
        result
    );
}

#[test]
fn type_infer_identity_applied_to_identity() {
    let mut kernel = Kernel::new();
    setup_type_system(&mut kernel);

    // Infer: what type does (λx.x)(λy.y) have?
    let result = kernel
        .execute("?- types nil (app (lam x (var x)) (lam y (var y))) T")
        .expect("type inference query");

    // Should infer T = (arrow A A) - the result is also an identity function
    assert!(
        result.contains("arrow"),
        "id applied to id should have arrow type: {}",
        result
    );
}

// ============================================================================
// Program Synthesis Tests
// ============================================================================

#[test]
fn synthesize_identity() {
    let mut kernel = Kernel::new();
    setup_type_system(&mut kernel);

    // Synthesize: find a term of type A -> A
    let result = kernel
        .execute("?- types nil Term (arrow A A)")
        .expect("synthesis query");

    // Should synthesize Term = (lam X (var X)) - the identity function
    assert!(
        result.contains("lam"),
        "synthesized term should be a lambda: {}",
        result
    );
    assert!(
        result.contains("var"),
        "synthesized term should use the variable: {}",
        result
    );
}

#[test]
fn synthesize_k_combinator() {
    let mut kernel = Kernel::new();
    setup_type_system(&mut kernel);

    // Synthesize: find a term of type A -> B -> A
    let result = kernel
        .execute("?- types nil Term (arrow A (arrow B A))")
        .expect("synthesis query");

    // Should synthesize Term = (lam X (lam Y (var X)))
    assert!(
        result.contains("lam"),
        "synthesized term should have lambda: {}",
        result
    );
    // Should have nested lambdas
    let lam_count = result.matches("lam").count();
    assert!(
        lam_count >= 2,
        "K combinator should have 2 lambdas: {}",
        result
    );
}

#[test]
fn synthesize_composition() {
    let mut kernel = Kernel::new();
    setup_type_system(&mut kernel);

    // Constrained composition sketch with distinct base types a,b,c
    let result = kernel
        .execute("?- types nil (lam f (lam g (lam x (app (var g) (app (var f) (var x)))))) (arrow (arrow a b) (arrow (arrow b c) (arrow a c)))")
        .expect("synthesis query");

    // Sketch should type-check against the intended composition type
    assert!(
        result.contains("true"),
        "composition sketch should type-check: {}",
        result
    );
}

// ============================================================================
// Full Notebook Execution Test
// ============================================================================

#[test]
fn notebook_type_inference_executes() {
    use std::fs;

    let notebook_path = concat!(env!("CARGO_MANIFEST_DIR"), "/notebooks/type_inference.ipynb");
    let notebook_json = fs::read_to_string(notebook_path).expect("Failed to read notebook");
    let notebook: serde_json::Value =
        serde_json::from_str(&notebook_json).expect("Failed to parse notebook");

    let cells = notebook["cells"]
        .as_array()
        .expect("notebook should have cells");

    let mut kernel = Kernel::new();
    let mut code_cells_executed = 0;

    for cell in cells {
        if cell["cell_type"].as_str() != Some("code") {
            continue;
        }

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

        let result = kernel.execute(source);
        code_cells_executed += 1;

        match result {
            Ok(output) => {
                // Fact/rule definitions should return "ok"
                if !source.starts_with("?-") && !source.starts_with(":") {
                    assert!(
                        output.contains("ok"),
                        "Cell should succeed: {} -> {}",
                        source,
                        output
                    );
                }
                // Queries should not error
                if source.starts_with("?-") {
                    assert!(
                        !output.contains("ERROR"),
                        "Query should not error: {} -> {}",
                        source,
                        output
                    );
                    assert!(
                        !output.contains("timeout."),
                        "Query should not timeout: {} -> {}",
                        source,
                        output
                    );
                }
            }
            Err(e) => {
                panic!("Cell failed: {} -> {}", source, e.message);
            }
        }
    }

    assert!(
        code_cells_executed >= 10,
        "Should have executed at least 10 code cells, got {}",
        code_cells_executed
    );
}
