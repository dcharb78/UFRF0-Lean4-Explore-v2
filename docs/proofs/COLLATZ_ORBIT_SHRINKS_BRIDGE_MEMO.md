# Collatz Orbit-Shrink Bridge Memo

This memo records the current theorem-centered path from the banked local
return mechanism to the remaining global obligation
`orbit_shrinks_W_steps`.

It is intentionally written in repo language only.

## Target

The single remaining global theorem in this formulation is:

- `orbit_shrinks_W_steps`

The hard case is already isolated in the file:

- odd `n > 1`
- `v2 (3 * n + 1) = 1`
- large `n`
- no fixed universal window `W`

So the project no longer needs a new ontology.
It needs a bridge.

## Current Banked Ingredients

### A. Higher-Time Return Ladder

Current green checkpoint:

- targeted build session `25387`
- exact `time = 211, 212, 213, 214, 215`
- residual `time >= 216`
- transport
  `2^(dst.time - 216) * dst.base = 27*m + 14`

This means the higher-time seam ladder is now a banked local return mechanism,
not just exploratory telemetry.

### B. Repeat-Core Projective Contraction

The repeat-core package already gives the descent candidate:

- `strict_projectiveSelfSlope_832_of_repeatCore832Transition`
- `strict_projectiveSelfSlope_832_in_repeatInnerParam_of_repeatCore832Transition`
- `normalizedProjectiveSelfSlopeEq_832_of_repeatCore832Transition_chain`

These are the current best formal evidence that the branch can expand in raw
value/radial coordinates while still contracting projectively.

### C. Exact / Bounded `27/16` Transport

The repeat-core package already contains the exact affine transport needed for
renormalized descent:

- `sixteen_mul_dst_stateValue_eq_twentySeven_mul_src_stateValue_add_19_of_repeatCore832Transition`
- `sixteen_mul_dst_radialGap_832_eq_twentySeven_mul_src_radialGap_832_add_9171_of_repeatCore832Transition`
- `sixteen_mul_dst_selfThresholdDefect_add_eleven_eq_twentySeven_mul_src_selfThresholdDefect_add_repeatThresholdResidue832_of_repeatCore832Transition`
- `sixteen_mul_dst_selfThresholdDefect_le_twentySeven_mul_src_selfThresholdDefect_add_15_of_repeatCore832Transition`

The bounded staircase term is already explicit:

- `repeatThresholdResidue832_lt_27`

### D. Pure-Phase / Clock Entry Structure

The chain package already exposes the pure-phase interface and clock behavior:

- `dst_repeatPurePhase832_of_repeatCore832Transition_chain`
- `repeatClock832_fst_eq5_of_repeatCore832Transition_chain`
- `repeatClock832_eq_5_9_of_repeatCore832Transition_chain3`

These are the current best hooks for a structural entry/funneling theorem.

## What Is Missing

What is still missing is not another local shell theorem by itself.

What is missing is a theorem stack that turns:

- local return structure
- projective contraction
- bounded residue

into:

- eventual shrinkage of the actual odd orbit

That is the bridge from the current local package to
`orbit_shrinks_W_steps`.

## Proposed Bridge-Theorem Stack

### 1. Entry / Funnel Theorem

Goal shape:

- if a large `v2 = 1` orbit persists long enough in the surviving branch, then
  it enters the repeat-core regime where the projective package applies

Current source support:

- chain classifiers
- pure-phase entry lemmas
- banked higher-time return seams

This is the theorem that says the local repeat-core mechanism is not optional.

### 2. Division-Free Projective Potential Theorem

Do not introduce a ratio first.

Use the already formalized cross-multiplied form.

Potential ingredients:

- normalized radial-gap coordinate
- normalized self-threshold-defect coordinate
- the strict inequality behind
  `strict_projectiveSelfSlope_832_of_repeatCore832Transition`

Desired form:

- a determinant-like quantity strictly decreases on the repeat-core chain
- the proof should be division-free

### 3. Residue-Spending Theorem

Use the explicit staircase coordinate, not an implicit floor-term argument.

Current source support:

- `repeatThresholdResidue832_lt_27`
- exact affine self-threshold transport with explicit residue term

Desired form:

- the bounded residue cannot reset indefinitely without forcing entry into the
  exact pure phase or into a stricter projective drop

### 4. Finite-Descent Theorem on Persistent `v2 = 1` Windows

Goal shape:

- once an orbit is in the repeat-core funnel and persists long enough, the
  projective potential plus bounded residue budget force actual descent in the
  source-state package

This is the local-to-global bridge theorem immediately before
`orbit_shrinks_W_steps`.

### 5. Wrapper Into `orbit_shrinks_W_steps`

Once the previous theorem exists, the wrapper should be comparatively short:

- split by `v2 (3*n + 1) >= 2` versus `= 1`
- small-case computation already handles the finite low range
- the new bridge theorem handles the remaining large `v2 = 1` case

## When Another Seam Is Justified

Another seam is justified only if it clearly supports one of these bridge
layers.

Good reasons to extend the seam ladder:

- it supplies the exact entry interface needed by the funnel theorem
- it exposes a missing clock/residue relation needed by the projective
  potential argument
- it proves that a live residual really lands in the repeat-core package

Bad reasons to extend the seam ladder:

- the next residual is available
- the next affine substitution is easy
- the ladder appears aesthetically incomplete

## Current Best Next Move

The current best next move is not another default seam.

It is to formulate the first bridge theorem explicitly, in Lean-facing terms,
using the already banked ingredients above.

The most promising immediate target is:

- an entry/funnel theorem that says sufficiently persistent large `v2 = 1`
  behavior reaches the repeat-core regime where
  `strict_projectiveSelfSlope_832_of_repeatCore832Transition`
  and
  `normalizedProjectiveSelfSlopeEq_832_of_repeatCore832Transition_chain`
  can take over.

Only after that target is stated precisely should another seam be treated as
default work.
