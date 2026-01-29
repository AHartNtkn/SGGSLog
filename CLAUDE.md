# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

SGGSLog is a minimal but complete implementation of a logic programming language in Rust that executes according to Semantically Guided Goal-Sensitive Reasoning (SGGS).

## Target Architecture

- **Core**: SGGS inference engine in Rust
- **CLI**: Command-line interface for loading theories and making queries
- **Jupyter Kernel**: Interactive notebook support for theory definitions and queries

## Build Commands

```bash
# Build the project
cargo build

# Run tests
cargo test

# Run a single test
cargo test test_name

# Run tests with output
cargo test -- --nocapture

# Check without building
cargo check

# Format code
cargo fmt

# Run linter
cargo clippy
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

## Project Status

This project is in early development. The spec.md file contains the project requirements.
