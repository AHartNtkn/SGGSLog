The goal of this repo is to create a *minimal* but *complete* implementation of a logic programming language in Rust which executes acording to Semantically Guided Goal-Sensitive Reasoning (SGGS).

Parsing is limited to surface syntax. Normalization (CNF conversion, Skolemization, and related transformations) is a separate phase that operates on parsed formulas.

The core interface should include a surface syntax for files declaring theories and for making queries to a CLI after importing or declaring the theory. This should also support a basic jupyter notebook kernel allowing this CLI and theory definitions to be used interactively in a notebook.

Execution should start from the all-negative initial interpretation by default. Other interpretations may be used internally for confluence testing but are not an end-user feature.

The SGGS inference system follows the papers’ rules (extension, splitting, deletion, move, resolution, factoring, left-split). SGGS-sorting is a bookkeeping heuristic and is not part of the required API.

String literals in directives are simple double-quoted paths; escape sequences are not required by the API.

Variable names are scoped per clause; reusing the same variable name across different clauses is allowed and carries no cross-clause identity.

Restraining-system checks are structural (rule coverage); termination/ES finiteness conditions from SGGSdpFOL are out of scope for this minimal implementation.
