# UFRF-Lean-V2 Agent Guide

## Supermemory

- If Supermemory MCP is available, use the `supermemory-codex-memory` workflow.
- Run recall before planning with queries that include `UFRF-Lean-V2`, `codex:project:UFRF-Lean-V2`, and the module or theorem names you are touching.
- Treat repository state as canonical. If recalled memory conflicts with current files, trust the repo and save a correction memory.
- Save small, durable memories for theorem additions, semantic decisions, and verification outcomes. Avoid saving raw logs or speculative ideas.

## Project Invariants

- Preserve the distinction between standard primes, UFRF nat-primes, and cycle positions.
- Do not conflate multiplicative generator roles in `ZMod 13` with UFRF-prime status.
- Keep `0` non-UFRF-prime, `1` UFRF-prime, and `2` explicitly non-UFRF-prime unless the user asks for a foundational change.
- Do not introduce `sorry`, `axiom`, or untracked theorem stubs.

## Verification

- Use `./scripts/verify.sh` as the default validation after Lean or module-graph edits.
- Use `./scripts/certify.sh` for stronger handoff validation when changes affect core semantics, prime logic, or cross-module proof wiring.
- `./scripts/verify.sh` already runs `scripts/sync_modules.py`, so prefer it over calling `lake build` alone.

## Editing Guidance

- Make the smallest change that preserves theorem intent and import stability.
- When touching proof-heavy files, prefer extending existing theorem packages and bridge layers over introducing duplicate statements.
- If a change affects project-wide semantics, mention the impacted modules in the final summary.
