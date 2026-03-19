# Residue Integration Plan

This document reviews [`/Users/dcharb/Downloads/RESIDUE_THEOREM_ROADMAP.md`](/Users/dcharb/Downloads/RESIDUE_THEOREM_ROADMAP.md) against the current Lean repo and sets a zero-`sorry` implementation pipeline.

## Why This Plan Exists

The roadmap is directionally strong, but it mixes three different kinds of work:

- safe interface work that the current repo and Mathlib already support,
- specific complex-analysis results that can be proved for carefully chosen functions,
- broader residue/Laurent/monodromy claims that would require substantially more infrastructure.

To keep the repo airtight, we need to separate those layers and only promote claims when the Lean proof actually supports them.

## Current Repo Leverage

The current Lean proof already gives us the correct base layer:

- `UFRF/Fourier.lean` formalizes the canonical additive character on `ZMod 13`, including the exact map `j ↦ exp(2πij/13)`.
- `UFRF/BreathingCycle.lean` formalizes the cycle as a contextual ring topology, including the chart/reindexing layer.
- `UFRF/AllenEmbedding.lean`, `UFRF/AllenBridge.lean`, and related modules already use modular residue language in the arithmetic sense.

This means the first residue-theorem phase should not rebuild the complex 13-cycle from scratch. It should expose a complex-plane interface on top of the existing Fourier character machinery.

## Roadmap Corrections

Before implementation, the roadmap needs five explicit corrections.

1. The roadmap still names the old repo `UFRFv3_LEAN4_explore`. The current target repo is `UFRF-Lean-V2`.
2. Placeholder theorem bodies such as `sorry` or `True := by trivial` are not acceptable in this repo. Every first-pass theorem must be real Lean content.
3. `ComplexBreathing.lean` should reuse `UFRF/Fourier.lean`, not duplicate the character construction with a parallel ad hoc definition stack.
4. The proposed `Complex.log (z * exp (2πi)) = Complex.log z + 2πi` statement is false for Lean's principal `Complex.log`. A future monodromy phase must use a different formalization strategy.
5. The word `residue` is already used informally in the repo for modular residue/reindexing language. Complex-analysis residue claims must be named carefully to avoid semantic drift.

## Terminology Contract

From this point on, the pipeline distinguishes:

- `cycle residue` or `modular residue`: arithmetic position in `ZMod 13`,
- `local chart` or `contextual coordinate`: the reindexing language from `BreathingCycle`,
- `complex residue`: the analytic coefficient/integral notion from contour integration.

No theorem or docstring should use plain `residue` when the intended meaning is ambiguous.

## Phase Pipeline

### Phase 0: Scope Fence

Goal:
- Lock the implementation order and the forbidden overclaims.

Rules:
- No general residue theorem in the first pass.
- No general Laurent-series API in the first pass.
- No projection-law theorem unless the formal statement is actually proved in Lean.
- No monodromy theorem based on the principal branch of `Complex.log`.

Acceptance gate:
- Every new module states exactly what is proved, what is definitional, and what remains open.

### Phase 1: Complex Breathing Interface

Target module:
- `UFRF/ComplexBreathing.lean`

Goal:
- Expose the breathing cycle as a complex-plane root-of-unity picture by reusing `UFRF/Fourier.lean`.

Allowed theorem shapes:
- explicit exponential formula for the breathing root,
- injectivity/distinctness of positions,
- root-of-unity membership and `13`-power closure,
- complete-cycle cancellation.

Out of scope:
- partial sums with heavy transcendental numerics,
- any analytic residue theorem,
- any observer/projection interpretation.

Acceptance gate:
- The module imports `UFRF/Fourier.lean` and proves exact interface theorems with zero placeholders.

### Phase 2: Specific Residues for Specific Functions

Target module:
- `UFRF/ResidueDefinition.lean`

Goal:
- Formalize explicit residues only for tightly controlled rational functions, beginning with functions built from `z^13 - 1`.

Preferred approach:
- use explicit factorization/derivative arguments for simple poles,
- prove the local value directly,
- derive total cancellation from the already-proved root-of-unity sum.

Out of scope:
- a fully general `Res(f, z₀)` API for arbitrary meromorphic functions.

Acceptance gate:
- every residue theorem is attached to a named concrete function with a real proof.

Current status:
- complete for the local simple-pole limit of `1 / (z^13 - 1)` at each breathing root,
- still intentionally not promoted to a general `Res(f, z₀)` API.

### Phase 3: Circle-Integral Bridge

Target module:
- `UFRF/CircleIntegralBreathing.lean`

Goal:
- connect the cycle picture to the existing Mathlib circle-integral API.

Preferred theorems:
- `∮ (z - w)⁻¹ dz = 2πi` on circles where Mathlib already has support,
- mode-selection statements that Lean can derive from existing `circleIntegral` lemmas,
- carefully bounded Cauchy-formula applications.

Out of scope:
- "projection law as residue theorem" unless the exact analytic statement is formalized.

Acceptance gate:
- every theorem is built from existing Mathlib contour-integral results, not narrative analogy.

Current status:
- `UFRF/CircleIntegralBreathing.lean` now proves the first honest contour statement for the
  specific breathing function `z ↦ 1 / (z^13 - 1)`.
- The module first records the standard kernel fact
  `circleIntegral_kernel_around_breathingRoot`, then proves the local closed-ball
  nonvanishing lemma
  `exists_pos_radius_localFactorAt_nonzero_closedBall`.
- The main bridge is
  `circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate`:
  on any positive-radius closed ball around `breathingRoot k` where `localFactorAt k`
  stays nonzero, the circle integral of `breathingFunction` equals
  `2πi * residueCandidateAt k`.
- The existence corollary
  `exists_pos_radius_circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate`
  packages that bridge as an actual small-circle theorem around each breathing root.
- This proof stays on Mathlib-supported ground:
  it applies Cauchy's circle-integral formula to the holomorphic inverse local factor on a
  closed ball, then identifies the boundary integrand with `breathingFunction`.
- Exact next blocker, if we want a tighter Phase 2 → Phase 3 bridge:
  a direct derivation from `breathingFunction_simplePole_limit` via
  `Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto`
  still needs a clean punctured-disk continuity/differentiability package for the
  desingularized function
  `z ↦ (z - breathingRoot k) * breathingFunction z`.
- Next smallest theorem needed:
  prove that this desingularized function is continuous on a punctured closed ball and
  differentiable on the corresponding punctured open ball for some explicit positive radius,
  then feed the already-proved punctured limit into Mathlib's center-of-circle formula.

### Phase 4: Interpretation Fence

Target docs:
- reviewer-facing docs and FAQ entries.

Goal:
- separate proved complex-analysis content from historical or interpretive language.

Required doc pattern:
- `theorem`,
- `definition`,
- `interpretation`,
- `open`.

Acceptance gate:
- no reviewer can mistake interpretation for proof.

### Phase 5: Advanced Branch

Candidate modules:
- `LaurentBreathing`,
- `MonodromyBreathing`,
- `AlphaResidue`,
- `SingularityClassification`.

Status:
- deliberately deferred.

Reason:
- these phases are feasible only after the specific-function residue pipeline is stable and the library gaps are better mapped.

## Execution Protocol

For each phase:

1. add only one new proof layer at a time,
2. run `lake build`,
3. run `./scripts/verify.sh`,
4. update reviewer docs only after the theorems exist,
5. keep theorem names narrower than the surrounding interpretation.

## Context Preservation Rules

To avoid losing context as the residue work grows:

1. every phase should leave behind at least one repo-local artifact:
   a new Lean module, an updated reviewer doc, or an explicit open-questions note,
2. every deferred claim should be named in writing rather than left implicit,
3. every theorem promoted into reviewer docs should cite its exact Lean name,
4. every interpretation layer should be labeled as interpretation, not proof,
5. commits should stay phase-scoped whenever possible, so the implementation history mirrors the plan.

## Plan Review

This plan is intentionally conservative, and that is a strength.

- It preserves the repo's current zero-`sorry` credibility.
- It starts from machinery the repo already has instead of re-deriving it in a second style.
- It avoids the biggest roadmap trap: importing speculative projection/monodromy language too early.
- It creates a clean place to stop after each phase with a coherent, truthful repo state.

That makes the pipeline suitable for adversarial review as well as steady implementation.
