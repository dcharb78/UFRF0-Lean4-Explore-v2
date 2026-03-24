# UFRF-Lean-V2 Agent Guide

## Supermemory

- If Supermemory MCP is available, use the `supermemory-codex-memory` workflow.
- Run recall before planning with queries that include `UFRF-Lean-V2`, `codex:project:UFRF-Lean-V2`, and the module or theorem names you are touching.
- Treat repository state as canonical. If recalled memory conflicts with current files, trust the repo and save a correction memory.
- Save small, durable memories for theorem additions, semantic decisions, and verification outcomes. Avoid saving raw logs or speculative ideas.
- If `supermemory/whoAmI` succeeds but `recall` or `memory` times out twice, treat Supermemory as degraded for the rest of the turn instead of blocking work.
- In degraded mode, recover context from local canonical sources in this order: current repo state and branch head, recent `git log`, `AGENTS.md`, `docs/RESIDUE_INTEGRATION_PLAN.md`, and the touched modules/proof notes.
- After local recovery, keep a short working-context block in the thread and continue normally; if Supermemory recovers later, save one compact repo-verified summary or correction memory.

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

## Suggested Subagent Roster

Use a small fixed roster instead of inventing new agent roles each session.

- `Plan Guardian`
  Read `AGENTS.md`, `docs/RESIDUE_INTEGRATION_PLAN.md`, the touched modules, and `UFRF.lean`.
  Check for drift between theorem names, blockers, docs, and reviewer-facing framing.
  Default output: findings first, then a single best next plan step. No code edits.
- `Invariant Auditor`
  Read the touched modules and nearby docs.
  Check the standing constraints: no fake general residue theorem or generic `Res` API, no projection-law promotion, no modular/complex residue conflation, preserve the prime semantics split, and avoid unnecessary import drift.
  Default output: findings first, then residual risks. No code edits.
- `Mathlib Scout`
  Before nontrivial analytic bridges, search for the smallest Mathlib-supported theorem path.
  Prefer exact lemma names, required hypotheses, and proof skeletons over broad strategy.
  Default output: one concrete theorem candidate and the lemmas needed to prove it.
- `Validation Sentinel`
  After Lean edits, run `./scripts/verify.sh`.
  For core semantic or cross-module changes, also run `./scripts/certify.sh` and `git diff --check`.
  Default output: only failures, regressions, or missing coverage.

## Suggested Use Pattern

- Start `Plan Guardian` and `Mathlib Scout` before proof-heavy work.
- Run `Invariant Auditor` before promoting new docs or semantic framing.
- Run `Validation Sentinel` after edits and before handoff.
- Keep subagents read-only unless the task explicitly calls for parallel code edits.
