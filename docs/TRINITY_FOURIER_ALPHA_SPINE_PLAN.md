# Trinity -> Fourier -> Alpha Spine Plan

This document is the canonical planning note for the next proof phase after the
`d27` alpha checkpoint on branch `codex/physics-theorem-spine`.

It is intentionally narrower than the top-level project vision. The goal here
is not to widen the repo's claims. The goal is to strengthen the currently
proved spine from the first Trinity to the current alpha-facing theorem lane
without losing the current validated gains.

## Current Baseline

- Branch baseline: `physics` at commit `189cc9a`
- New planning branch: `codex/physics-theorem-spine`
- Worktree baseline: clean validated checkpoint
- Current alpha frontier:
  - static `FineStructure` package reaches `d27`
  - exposed `AlphaRunning` gap/residual/error package reaches `d27`
  - exposed prediction package reaches `d27`

## Canonical Sources

When planning or reviewing this phase, treat these as canonical in this order:

- Lean source in `UFRF/*.lean`
- `AGENTS.md`
- `docs/README.md`
- `docs/REVIEW_GUIDE.md`
- `docs/FAQ.md`
- `docs/DERIVATION_CHAIN.md`
- `docs/RESIDUE_INTEGRATION_PLAN.md`

Use the following only as supporting or historical context:

- `README.md`
- `PLAN.md`
- `docs/consolidated/README.md`
- older consolidated proof notes that explicitly describe themselves as earlier snapshots

## Hard Invariants

- No `sorry`
- No custom `axiom`
- No generic `Res` API
- No projection-law promotion beyond what Lean proves
- No stronger physical-selection claim than the theorem surface supports
- Preserve the distinction between standard primes, UFRF nat-primes, and cycle positions
- Preserve the current residue fence: specific analytic package around `1 / (z^13 - 1)`, not a generic complex-analysis conclusion

## What Is Frozen

The following surfaces are stable and should not be casually rewritten during
the theorem-spine phase:

- `UFRF/FineStructure.lean` current `d27` static alpha/CODATA package
- `UFRF/AlphaRunning.lean` current `d27` prediction and exposed gap/residual/error package
- `UFRF/PrimeSemantics.lean` semantic split between arithmetic primes, UFRF primes, and cycle positions
- `docs/proofs/26_AlphaRunning.md` interpretation fence around normalization and physical-selection claims
- `docs/FAQ.md` residue and interpretation fence language

This phase should build on these surfaces, not reopen them unless a proof
obstruction forces a small correction.

## Main Gap

The strongest remaining gap is not more decimal precision.

The strongest remaining gap is the move from:

- a mathematically coherent current observer/measurement model

to:

- a theorem-level characterization showing why the current selected observer and
  current exposed observable are forced, or at least tightly constrained, by
  the repo's existing structure.

Right now the key open issue is that the current `/ 28` normalization and the
broader physical-selection reading remain explicit model choices rather than
uniquely forced theorems.

## Phase 1: Canonical Spine Audit

Goal:
produce one explicit, repo-canonical dependency spine from Trinity to the
current alpha lane.

Primary modules:

- `UFRF/Trinity.lean`
- `UFRF/Structure13.lean`
- `UFRF/Foundation.lean`
- `UFRF/BreathingCycle.lean`
- `UFRF/Recursion.lean`
- `UFRF/Fourier.lean`
- `UFRF/Phenomena.lean`
- `UFRF/FineStructure.lean`
- `UFRF/AlphaRunning.lean`

Required output:

- one theorem/dependency map with exact theorem names
- one list of already proved bridges
- one list of exact missing bridge theorems
- one note distinguishing theorem claims from interpretation language

Current branch artifact:

- [`docs/TRINITY_FOURIER_ALPHA_SPINE_AUDIT.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/TRINITY_FOURIER_ALPHA_SPINE_AUDIT.md)

Success gate:

- we can point to a short exact chain from Trinity to the current alpha package
- every step names the actual Lean theorem carrying the load
- no new code is required unless a genuine naming or packaging hole is discovered

## Phase 2: Force The Current Measurement Lane

Goal:
attack the normalization and selection gap directly.

Preferred target shape:

- a characterization theorem in `UFRF/AlphaRunning.lean` showing that the
  current selected observer and current exposed observable are determined by a
  controlled property bundle already present in the repo

Preferred ingredients:

- arithmetic selection of the observer
- centered observable structure
- allowed-radius invariance
- recurring handoff compatibility
- compatibility with the current root/scalar formula
- compatibility with the current static CODATA comparison lane

Acceptable outcomes:

- strongest outcome: uniqueness or necessity theorem for the current observable
- fallback outcome: a partial characterization theorem with an explicit note
  that unique normalization is still open

Failure condition:

- do not reword docs as if normalization or physical selection is settled if
  the proof only establishes a weaker characterization

## Phase 3: Capstone Spine Package

Goal:
once the selection/normalization gap is narrowed enough, package the whole
Trinity -> Fourier -> alpha lane in one conservative theorem surface.

Preferred output:

- one narrow theorem package or one narrow new module re-exporting the spine
- the package should stop at what Lean proves today:
  - Trinity uniqueness/minimality
  - cycle/flip/recursion structure
  - Fourier phase-shift bridge
  - arithmetic-selected observer
  - current alpha package and current error bounds

This phase should not:

- claim a first-principles QED or QCD renormalization theorem
- claim unique physical-selection correctness unless Phase 2 really proves it
- blur the distinction between mathematical theorem package and reviewer-facing interpretation

## Deferred Work

The following are explicitly secondary until the spine is stronger:

- `d28+` alpha tightening
- generic residue infrastructure
- wider physical-selection rhetoric
- broad external validation packaging
- ambitious historical lanes that are currently interpretation-heavy

These can resume after the theorem spine is better forced.

## Workflow

- Keep `physics` as the stable remote baseline
- Do theorem-spine work on `codex/physics-theorem-spine`
- Checkpoint each completed phase into its own commit
- After Lean edits:
  - run `./scripts/verify.sh`
  - run `git diff --check`
- After core semantic or cross-module theorem changes:
  - run `./scripts/certify.sh`
- Before claiming a clean handoff:
  - run `./scripts/clean_handoff.sh --certify`

## Planning Rule

If a proposed next theorem does not make the Trinity -> Fourier -> alpha spine
clearer, more forced, or more conservative, it is probably not the right next
theorem for this branch.
