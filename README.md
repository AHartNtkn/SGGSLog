# SGGSLog

A logic programming language that reasons using Semantically-Guided Goal-Sensitive (SGGS) inference.

Unlike Prolog, SGGSLog handles full first-order logic: universal and existential quantifiers, disjunction, and negation. It can prove theorems, detect unsatisfiability, and enumerate answers to queries—all without requiring mode declarations or stratification.

## Features

- **Compound terms**: Build structured data like `(s (s z))` for Peano numerals
- **Bidirectional relations**: Use the same definition for addition AND subtraction
- **Recursive definitions**: Compute transitive closure, reachability, arithmetic, and more
- **First-order quantifiers**: Use `∀` and `∃` for expressive specifications
- **Disjunctive reasoning**: Handle "or" natively without committing to a single branch
- **Answer streaming**: Get results one at a time with `:next`
- **Unsatisfiability detection**: Discover contradictions in your theory
- **Projection control**: Hide or reveal internal symbols (Skolem constants)

## Installation

Requires Rust 1.70 or later.

```bash
git clone https://github.com/your-username/sggslog.git
cd sggslog
cargo build --release
```

The binary will be at `target/release/sggslog`.

## Jupyter Kernel Installation

SGGSLog includes a Jupyter kernel for interactive notebook use.

```bash
cargo install --path .
jupyter kernelspec install --user sggslog
jupyter notebook notebooks/tutorial.ipynb
```

## Quick Start

Run the REPL:

```bash
cargo run
```

Try some commands:

```
SGGSLog - Semantically Guided Goal-Sensitive Logic Programming
Type :help for help, :quit to exit.

> person alice
ok.
> person bob
ok.
> ?- person X
X = alice
> :next
X = bob
> :next
no more answers.
```

## Language Syntax

### Terms and Predicates

- **Constants**: lowercase identifiers (`alice`, `bob`, `x1`)
- **Variables**: uppercase identifiers (`X`, `Y`, `Person`)
- **Compound terms**: `(f a b)` or `f a b` — function application is space-separated, not comma-separated

### Logical Operators

| Unicode | ASCII | Meaning |
|---------|-------|---------|
| `¬`     | `~`   | negation |
| `∧`     | `&`   | conjunction |
| `∨`     | `\|`  | disjunction |
| `→`     | `->`  | implication |
| `∀`     |       | universal quantifier |
| `∃`     |       | existential quantifier |

### Statements

**Ground facts**:
```
person alice
edge a b
```

**Rules** (implications):
```
person X -> mortal X
path X Y & edge Y Z -> path X Z
```

**Quantified formulas**:
```
∀X ∀Y (path X Y -> connected X Y)
∃S (secret S)
```

**Disjunctions**:
```
item X -> red X | blue X
```

**Negations**:
```
~human robot1
bird X & ~abnormal X -> flies X
```

### Queries

Start a query with `?-`:

```
?- person alice        // ground query: true or false
?- person X            // find bindings for X
?- path a Y & path Y b // conjunctive query
```

Use `:next` to get additional answers from the stream.

### Directives

| Command | Description |
|---------|-------------|
| `:quit` | Exit the REPL |
| `:help` | Show help |
| `:next` | Get next answer from current query |
| `:load "file.sggs"` | Load clauses from a file |
| `:set timeout_ms N` | Set query timeout in milliseconds |
| `:set projection allow_internal` | Show internal symbols in answers |
| `:set projection user` | Hide internal symbols (default) |

## Examples

### Graph Reachability

```
// Define edges
edge a b
edge b c
edge c d

// Path is transitive closure of edge
edge X Y -> path X Y
path X Y & edge Y Z -> path X Z

// Query: what can we reach from a?
?- path a X
```

Results: `X = b`, then `X = c`, then `X = d`.

### Peano Arithmetic

This is the classic logic programming example. Define addition once, use it for addition, subtraction, and enumeration:

```
// Natural numbers: z = 0, (s z) = 1, (s (s z)) = 2, ...
// Addition: (add X Y Z) means X + Y = Z

add z Y Y                           // 0 + Y = Y
add X Y Z -> add (s X) Y (s Z)      // if X + Y = Z then (X+1) + Y = (Z+1)

// Compute 1 + 2:
?- add (s z) (s (s z)) R
// R = (s (s (s z)))  (that's 3)

// Compute 3 - 1 (run addition backwards!):
?- add X (s z) (s (s (s z)))
// X = (s (s z))  (that's 2)

// Enumerate all ways to partition 2:
?- add X Y (s (s z))
// X = z, Y = (s (s z))         (0 + 2)
// X = (s z), Y = (s z)         (1 + 1)
// X = (s (s z)), Y = z         (2 + 0)
```

### Existential Witnesses

```
∃S (secret S)

// By default, internal witnesses are hidden
?- secret X
// no answers.

:set projection allow_internal
?- secret X
// X = sk_0
```

### Contradiction Detection

```
raining
~raining

?- anything
// The theory is unsatisfiable
```

## Tutorial

The tutorial notebook (`notebooks/tutorial.ipynb`) provides a complete walkthrough:

1. Basic facts and queries
2. Rules and implications
3. Recursive rules (graph reachability)
4. Universal and existential quantifiers
5. Disjunctive reasoning
6. Compound terms and Peano arithmetic
7. Bidirectional relations
8. Unsatisfiability detection

To run the tutorial, install the Jupyter kernel (see above) and open the notebook:
```bash
jupyter notebook notebooks/tutorial.ipynb
```

## Running Tests

```bash
cargo test              # Run all tests
cargo test --lib        # Library tests only
cargo test --test '*'   # Integration tests only
```

## Technical Background

SGGS (Semantically-Guided Goal-Sensitive) is a theorem proving method that:

- Maintains a *trail* of constrained clauses representing a partial model
- Uses an *initial interpretation* to guide search toward goal-relevant derivations
- Supports *model-based* reasoning where the trail can be queried for answers
- Handles full first-order logic with equality (in principle)

For more on SGGS, see:
- Bonacina & Plaisted, "Semantically-Guided Goal-Sensitive Reasoning" (2016)

## License

MIT
