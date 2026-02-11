# AGENTS.md

## Theorem Statement

The theorem statement in `Erdos/Basic.lean` is **IMMUTABLE**. Do not modify it under any circumstances. If you believe it is unprovable as stated, escalate to the advisor.

## Known Status

This theorem has been proved by other researchers. A correct proof exists. Your task is to independently discover and formalize a proof in Lean 4.

## Rules

- **No axioms.** Every step must be proved or use existing Mathlib lemmas.
- **`sorry` is acceptable** as an intermediate state marking incomplete work. The goal is zero sorrys.
- **Every commit must compile.** `lake build` must succeed before committing.
- **NEVER run `lake clean`.** The `.lake/packages/` directory contains pre-built Mathlib. Cleaning it destroys the shared cache across all projects.
- **Do not search for or reference external proofs.** Discover the proof independently.

## Lean Environment

- Lean 4.27.0
- Mathlib v4.27.0
- Build command: `lake build`

## Project Structure

```
Erdos/Basic.lean       — Main theorem statement + proof
Erdos/Lemmas.lean      — Supporting lemmas (create as needed)
proofs/                — Natural language proofs (explore agents write here)
artifacts/             — Reference material (librarian writes here)
```

## Task Management

This project uses beehive (`bh`) with the `math-research` workflow. Roles: librarian, explore, verify, formalize, planner, advisor.
