# AGENTS.md

## Scope
This repo implements SGGS as specified by SGGS papers and `spec.md`. The goal is to align tests and code strictly with SGGS requirements.

## Behavior Requirements for Assistants
- **Do not** ask whether to deviate from SGGS behavior or to adopt alternative assumptions.
- **Do not** propose design changes that contradict SGGS.
- Treat SGGS papers and `spec.md` as the source of truth for required behavior.
- Only flag tests/specs when they **conflict** with SGGS requirements or with `spec.md`.
- If you identify gaps, frame them as: **missing SGGS-required coverage** or **extra assumptions not required by SGGS**.
- Minimize questions. Ask only if you are blocked from proceeding.
- Keep responses concise and action-oriented.
- Never mention implementation complexity or refactor size; the user only cares about the final result.
- Do not ask for permission or confirmation to proceed with requested work; proceed directly.
- Do not implement any TODOs. Your only job is to ensure the spec implied by the existing tests and API stubs is correct and good; never implement the specified behavior.
