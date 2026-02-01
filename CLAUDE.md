# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

SGGSLog is a minimal but complete implementation of a logic programming language in Rust that executes according to Semantically Guided Goal-Sensitive Reasoning (SGGS).

## Module Structure

- **syntax**: First-order logic terms, literals, and clauses (`Term`, `Literal`, `Clause`)
- **unify**: Unification algorithm and substitutions (`Substitution`, `unify`, `unify_literals`)
- **constraint**: Constraints for SGGS constrained clauses (`AtomicConstraint`, `Constraint`)
- **sggs**: Core SGGS inference system including:
  - `Trail` and `TrailInterpretation` for the SGGS trail
  - `ConstrainedClause` for clauses with constraints
  - Inference rules: extension, resolution, splitting, left-split, deletion, factoring, move
  - `derive` for running complete derivations
- **parser**: Surface syntax parsing (`parse_file`, `parse_query`)
- **theory**: Theory management (`Theory`)
- **repl**: Interactive REPL (`Repl`)
- **jupyter**: Jupyter kernel support (`Kernel`)

## Build Commands

```bash
cargo build          # Build the project
cargo test           # Run all tests
cargo test name      # Run a single test
cargo test -- --nocapture  # Run tests with output
cargo check          # Type-check without building
cargo fmt            # Format code
cargo clippy         # Run linter
```

## Development Approach

Use strict TDD (Test-Driven Development):

1. **Write tests first** - Tests define expected behavior before implementation
2. **Stub interfaces for type checking** - Create function/struct signatures that compile but use `todo!()` or `unimplemented!()` for bodies
3. **Tests should fail initially** - A test that passes before implementation is suspect
4. **Implement to make tests pass** - Only write enough code to pass the failing test
5. **Refactor** - Clean up while keeping tests green

```rust
// Example stub pattern
pub fn unify(t1: &Term, t2: &Term) -> Option<Substitution> {
    todo!("unify implementation")
}
```

## Testing

Tests are organized as:
- Unit tests within each module (`src/*/mod.rs`)
- Semantic tests in `src/tests/`
- Integration tests in `tests/` (parser semantics, SGGS properties, theory semantics)

## Test Timing Expectations

**No tests are designed to be slow.** All tests use small theories and should complete in under a second when properly implemented.

### Tests That Fail Immediately (Not Slow)

Some tests fail instantly due to `todo!()` stubs in unimplemented methods:

- **Fragment detection methods** in `src/syntax/clause.rs`:
  `is_restrained`, `is_negatively_restrained`, `is_pvd`, `is_sort_restrained`, `is_sort_negatively_restrained`, `is_sort_refined_pvd`

- **Theory classification methods** in `src/theory/theory.rs`:
  `is_bdi`, `is_restraining_system`, `basis`

These cause `fragment_semantics` and related tests to panic with "not yet implemented". This is expected until implementation.

### Slow Tests Indicate Bugs

If any test takes more than a few seconds, it indicates a problem:
- **Infinite loop in derivation** - SGGS search not terminating
- **Missing termination condition** - Derivation continues beyond fixed point
- **Inefficient algorithm** - Exponential blowup in search

Tests with `timeout_ms: None` run derivations on decidable fragments that must terminate. If they hang, the fragment classification or derivation has a bug.

### Standard Test Timeout

Always use a 10-second timeout when running tests to catch infinite loops:

```bash
timeout 10 cargo test           # Run all tests
timeout 10 cargo test name      # Run specific test
```

Do not vary this timeout arbitrarily. 10 seconds is sufficient for any correctly-implemented test.

