# AGENTS.md

This repository is worked on interactively across multiple conversations.
Use this file as the always-on workflow and proof discipline for new Codex
threads.

## Scope

These instructions apply to the whole repository. For Collatz work, also read
[`docs/proofs/COLLATZ_CONCURRENT_FRONTIER.md`](docs/proofs/COLLATZ_CONCURRENT_FRONTIER.md)
before changing proofs.

## Core Proof Discipline

- Preserve the project standard: no new `sorry`, no new custom `axiom`, no
  weakening of existing statements to bypass proof obligations.
- Treat Lean as the source of truth. Conceptual ideas are welcome, but only
  theorem statements and kernel-checked proofs count as facts.
- Prefer extending existing source-state machinery over adding parallel
  observer-only scaffolding.
- Do not silently revert unrelated user changes. Work with the current tree
  unless the user explicitly asks for cleanup.

## Build Discipline

- Run at most one Lean build at a time.
- Prefer targeted builds after meaningful proof changes, especially:
  `lake build UFRF.CollatzConcurrentScales`
- Use a full cold `lake build` at checkpoints before major commits or handoffs.
- If the user is actively monitoring builds manually, wait for the user's
  confirmation that the current build finished before starting another.

## Memory And Handoff Discipline

- If the `ufrf-memory-loop` skill is available in the environment, use it
  before substantial Collatz/UFRF proof work.
- Query recent curated notes before exploring widely. On the primary local
  workstation this curation directory is:
  `/Users/dcharb/.codex/tools/ufrf-rover/.ufrf_rover/curations/`
- When the theorem frontier materially moves, write back one short durable
  note that records:
  - what theorem family was added
  - what it means
  - what it rules out
  - the best next step
- If Lean source moves ahead of the last green build boundary, update
  `docs/proofs/COLLATZ_CONCURRENT_FRONTIER.md` immediately so it names both
  the `last green checkpoint` and the `current WIP in source`.
- Do not let compacted-thread handoffs flatten unverified source edits into
  verified checkpoint status. Keep WIP theorem families explicitly marked as
  unverified until the corresponding build is confirmed green.
- Keep memory notes theorem-centered and short. Avoid long reflective prose
  unless strategy truly changes.

## Local Name Discipline

- Use Rover to recover theorem clusters, frontier state, and best-next-family
  context. Do not use Rover as the final authority for exact Lean declaration
  names.
- Before applying or rewriting with local declarations in
  `UFRF/CollatzConcurrentScales.lean`, verify exact names in source using `rg`
  and the generated declaration index artifacts:
  - `docs/proofs/COLLATZ_CONCURRENT_SYMBOL_INDEX.md`
  - `docs/proofs/COLLATZ_CONCURRENT_SYMBOL_INDEX.json`
- Regenerate those artifacts after meaningful declaration movement with:
  `python3 scripts/generate_decl_index.py --input UFRF/CollatzConcurrentScales.lean --json docs/proofs/COLLATZ_CONCURRENT_SYMBOL_INDEX.json --markdown docs/proofs/COLLATZ_CONCURRENT_SYMBOL_INDEX.md --title "Collatz Concurrent Scales Symbol Index"`
- If the generated index and Lean source ever disagree, trust Lean source and
  regenerate the index before continuing.

## Collatz / Regime-II Strategy

For the current Collatz program, preserve these priorities:

- Intrinsic source state first, projections second.
- `RegimeIIState` is the ontology; observer bundles are charts or projections.
- Do not treat `bundle65` or any fixed chart as privileged.
- The goal is state-level classification that feeds actual shrink, not
  accumulation of modular curiosities.
- Prefer theorem work that narrows the bad frontier, strengthens the intrinsic
  return map, or directly feeds the remaining global shrink theorem.

## Working Rhythm

- Before substantial work, restate the target theorem family and why it is the
  right next step.
- For exact local names, check the generated symbol index first, then confirm
  the final statement shape in source before writing proof terms.
- Keep updates short and concrete while exploring or proving.
- When a checkpoint is green and the worktree is coherent, commit it instead of
  carrying a large amount of uncheckpointed theorem movement.
