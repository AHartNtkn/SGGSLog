The goal of this repo is to create a *minimal* but *complete* implementation of a logic programming language in Rust which executes acording to Semantically Guided Goal-Sensitive Reasoning (SGGS).

Parsing is limited to surface syntax. Normalization (CNF conversion, Skolemization, and related transformations) is a separate phase that operates on parsed formulas. CNF conversion may use definitional/Tseitin-style auxiliary predicates; the result must be a conservative extension over the user vocabulary (equisatisfiable, and preservable over original symbols).

The core interface should include a surface syntax for files declaring theories and for making queries to a CLI after importing or declaring the theory. This should also support a basic jupyter notebook kernel allowing this CLI and theory definitions to be used interactively in a notebook.

Surface syntax includes explicit clause statements prefixed with `clause`, whose body is a disjunction of literals.
Surface syntax allows predicate/function application without parentheses in files/REPL (e.g., `p a b` parses as `p(a,b)`), and supports ASCII/Unicode operator spellings (e.g., `~`/`¬`, `&`/`∧`, `|`/`∨`).
Surface syntax supports optional sort annotations on variables and function symbols using `:`, e.g., `X:s1`, `f:s2 X:s1`.
Single-line comments begin with `//` and continue to end of line.

Execution should start from the all-negative initial interpretation by default. Other interpretations may be used internally for confluence testing but are not an end-user feature.

The SGGS inference system follows the papers’ rules (extension, splitting, deletion, move, resolution, factoring, left-split). SGGS-sorting is a bookkeeping heuristic and is not part of the required API.
Scheduling among applicable SGGS inferences is nondeterministic; test expectations must not assume a fixed order.

Termination guarantees are part of the API only for SGGS-decidable fragments (e.g., stratified/Datalog, restrained, sort-restrained, sort-refined PVD, EPR, BDI), not globally.

String literals in directives are simple double-quoted paths; escape sequences are not required by the API.

Variable names are scoped per clause; reusing the same variable name across different clauses is allowed and carries no cross-clause identity.
Constants are represented as 0-ary function symbols in the internal term language. Skolem constants are likewise represented as 0-ary functions. The public signature surface treats constants as 0-ary functions (there is no separate constant symbol category).

Queries are answered against the SGGS-constructed model (not by refutation), and user-visible answers are deduplicated (including duplicates arising from alpha-equivalent clauses). Query answers are streamed: a query returns the first answer (if any), and subsequent answers are retrieved explicitly via `:next`. When no more answers remain, the user is told the query is exhausted. `answer_query` returns unprojected answers; projection is applied only by `answer_query_projected`.
Unsatisfiable queries produce no answers and are immediately exhausted. If the theory is unsatisfiable, queries likewise yield no answers and are immediately exhausted (no model is exposed).

Projection of answers is part of the external API. By default, only user-provided term symbols may appear in answers; internal symbols (e.g., Skolem symbols) are filtered by discarding any answer that contains them (answers are not rewritten). A projection mode that allows internal symbols is supported. When projection is `only_user_symbols`, streamed answers are restricted to terms built from the user signature. Projection applies to substitutions over terms; predicate symbols in queries are not projected.

Negative-only queries (variables appearing only in negated literals) are allowed. When projection is `only_user_symbols`, such queries stream answers over the user signature (and may be infinite).

Directives include `:load "path"`, `:set key value`, `:next` (to retrieve the next answer to the most recent query), and `:quit` (to exit the session). Supported keys include `timeout_ms` and `projection` (values: `only_user_symbols` or `allow_internal`). `initial_interp` is not supported for end users. If `:next` is issued with no active query, the session reports an error.
`timeout_ms` is a best-effort wall-clock budget for derivation and query evaluation; if it is `0`, the operation times out immediately.
