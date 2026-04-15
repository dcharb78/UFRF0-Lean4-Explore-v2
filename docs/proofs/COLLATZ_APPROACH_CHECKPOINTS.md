# Collatz Approach Checkpoints

This note keeps the Collatz proof workflow durable when the local seam ladder
is moving quickly.

Its purpose is not to replace the main handoff or frontier files. Its purpose
is to prevent drift:

- drift from banked green checkpoints into unverified source summaries
- drift from theorem-centered work into metaphor-centered work
- drift from bridge theorems back into endless seam-chasing

Read this note together with:

- `docs/proofs/COLLATZ_COMPACT_HANDOFF.md`
- `docs/proofs/COLLATZ_CONCURRENT_FRONTIER.md`

## Current Stance

As of targeted build session `25387`, the live green boundary is banked through:

- exact `time = 211, 212, 213, 214, 215`
- residual `time >= 216`
- transport
  `2^(dst.time - 216) * dst.base = 27*m + 14`

That means the higher-time seam ladder is no longer just exploratory evidence.
It is now a banked local return mechanism.

The remaining global gap is still:

- `orbit_shrinks_W_steps`

So the default mode should now be:

- synthesis-first
- bridge-theorem-first
- seam extension only when it clearly supports the bridge

## Durable Workflow

For each source-side proof cycle, keep this order:

1. Re-anchor on the repo and run compact status.
2. State the exact theorem target for the cycle.
3. If the target is another seam, also state which bridge theorem it supports.
4. Keep source-only edits separate from the last green checkpoint until Lean is
   green.
5. After a green build, serialize artifact banking:
   - regenerate declaration index
   - update targeted-build status
   - update compact handoff
   - update frontier
   - rerun compact status
   - write one short Rover note
6. Before a pause, strategy pivot, or multi-day gap, commit and push the banked
   green checkpoint if the scope is clean.

## Checkpoint Types

### 1. Green Boundary Checkpoint

This is the ordinary proof checkpoint.

It is real only when all of these align:

- Lean build green
- `COLLATZ_TARGETED_BUILD_STATUS.json`
- compact handoff
- frontier
- symbol index
- Rover note

If any of those lag, do not flatten the state into one summary.

### 2. Strategy Checkpoint

This is the anti-drift checkpoint.

Take one whenever any of the following becomes true:

- two consecutive green seam checkpoints add no new bridge lemma toward
  `orbit_shrinks_W_steps`
- the next seam is obtained mainly by affine reuse of an older `27*m + c`
  family rather than by new conceptual structure
- discussion starts leaning on phrases like `mirror`, `lowering operator`,
  `freeze when exhaustive`, or `symmetry` without naming the supporting
  theorems
- we can describe the next shell, but not the exact bridge theorem it is meant
  to support

At a strategy checkpoint, answer these questions in writing:

1. What exact theorem target moved closer to `orbit_shrinks_W_steps`?
2. What new source object or invariant became available?
3. Did the last work prove a bridge fact, or only extend the ladder?
4. Is another seam really needed before the next bridge attempt?

### 3. Global-Approach Checkpoint

This is the larger proof-architecture checkpoint.

The current order of attack should be:

1. Entry / funnel theorem into the repeat-core regime.
2. Division-free projective potential theorem on that regime.
3. Bounded staircase-residue spending theorem.
4. Finite-descent theorem for sufficiently persistent `v2 = 1` windows.
5. Wrapper from that descent package into `orbit_shrinks_W_steps`.

If work is not progressing in that order, pause and justify the detour.

## Safe Theorem-Centered Summary

These claims are safe to treat as already formalized:

- the repeat-core package has strict projective contraction via
  `strict_projectiveSelfSlope_832_of_repeatCore832Transition`
- the chain package has a normalized projective equality interface via
  `normalizedProjectiveSelfSlopeEq_832_of_repeatCore832Transition_chain`
- the repeat-core package has exact or bounded `27/16` transport via
  `sixteen_mul_dst_stateValue_eq_twentySeven_mul_src_stateValue_add_19_of_repeatCore832Transition`
  and
  `sixteen_mul_dst_selfThresholdDefect_add_eleven_eq_twentySeven_mul_src_selfThresholdDefect_add_repeatThresholdResidue832_of_repeatCore832Transition`
- the pure affine phase is already isolated by
  `dst_repeatPurePhase832_of_repeatCore832Transition_chain`
  and the clock classifiers
  `repeatClock832_fst_eq5_of_repeatCore832Transition_chain`
  and
  `repeatClock832_eq_5_9_of_repeatCore832Transition_chain3`

These claims are still interpretation, not theorem names:

- `mirror down-ladder`
- `inverse renormalization`
- `QHO lowering operator`
- `freeze when exhaustive`

They may still be useful in discussion, but they should not drive bookkeeping
or proof summaries by themselves.

## Current Approach Rule

Until a bridge theorem proves otherwise:

- treat the seam ladder as banked local mechanism
- treat the repeat-core projective package as the main candidate descent engine
- treat new seam work as subordinate evidence unless it directly supports a
  bridge into `orbit_shrinks_W_steps`

In practice this means:

- do not chase another seam only because the next residual is available
- do chase another seam if it supplies an interface needed by a bridge theorem
- after every two seam checkpoints without a new bridge lemma, stop and write a
  short strategy note before continuing

## Current Best Next Step

The current best next step is to formulate a theorem-centered bridge memo using
only existing repo objects:

- higher-time seam ladder through session `25387`
- repeat-core projective contraction
- bounded staircase residue
- pure-phase / clock classifiers
- target theorem `orbit_shrinks_W_steps`

That memo now lives at:

- `docs/proofs/COLLATZ_ORBIT_SHRINKS_BRIDGE_MEMO.md`

Use it to specify the next formal bridge theorem before any further seam
extension is treated as default work.
