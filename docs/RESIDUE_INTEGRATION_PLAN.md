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
- The direct Phase 2 → Phase 3 bridge is now also formalized:
  `desingularizedBreathingFunctionAt`,
  `continuousOn_desingularizedBreathingFunctionAt_punctured_closedBall`,
  `differentiableOn_desingularizedBreathingFunctionAt_punctured_ball`,
  and
  `circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_via_simplePole_limit`
  show that the punctured simple-pole limit theorem already plugs directly into Mathlib's
  punctured-center Cauchy formula.
- The local isolation package is now also explicit:
  `exists_pos_radius_closedBall_zero_unique_for_breathingDenominator`
  proves that on some sufficiently small closed ball around `breathingRoot k`,
  the denominator `z^13 - 1` vanishes only at that root, and
  `exists_pos_radius_closedBall_excludes_other_breathingRoots`
  specializes this to a radius criterion excluding every other breathing root.
- The algebraic zero pattern of the local factor is now partly explicit too:
  `localFactorAt_vanishes_at_other_breathingRoot`
  records that for fixed `k`, the local factor `localFactorAt k` vanishes at
  every other breathing root `breathingRoot j` with `j ≠ k`.
- The separation statement is now slightly more quantitative:
  `exists_pos_radius_lt_dist_other_breathingRoots`
  upgrades the same existential radius into a strict positive lower bound,
  for each fixed `k`, on the distance from `breathingRoot k` to every other
  breathing root.
- The repo also now has a global finite-separation package for the whole
  breathing-root configuration:
  `breathingRootSet_infsep_pos`,
  `half_infsep_lt_dist_breathingRoots`,
  and
  `half_infsep_closedBall_excludes_other_breathingRoots`
  provide a canonical uniform radius
  `infsep(range breathingRoot) / 2`
  that excludes every other breathing root around any chosen center.
- The zero set of the denominator is now fully tied back to the breathing-root
  interface:
  `exists_breathingRoot_of_breathingDenominator_eq_zero`
  proves that every zero of `z^13 - 1` is some `breathingRoot j`.
- The canonical nonvanishing bridge is now in place:
  `localFactorAt_nonzero_closedBall_half_infsep`
  shows that on the closed ball
  `closedBall (breathingRoot k) (infsep(range breathingRoot) / 2)`,
  the local factor `localFactorAt k` never vanishes.
- The single-root contour theorem has now been upgraded from an existential
  radius statement to a canonical-radius statement:
  `circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_half_infsep`
  proves that on the circle of radius
  `infsep(range breathingRoot) / 2`
  around `breathingRoot k`, the breathing function integrates to
  `2πi * residueCandidateAt k`.
- The geometric disjointness layer is now explicit too:
  `disjoint_ball_half_infsep_breathingRoots`
  proves that the canonical open balls of radius
  `infsep(range breathingRoot) / 2`
  around distinct breathing roots are disjoint, while
  `disjoint_closedBall_of_lt_half_infsep_breathingRoots`
  and
  `disjoint_sphere_of_lt_half_infsep_breathingRoots`
  give the stronger closed-ball and circle disjointness package for any common
  radius `R < infsep(range breathingRoot) / 2`.
- The repo now also exposes a fixed canonical closed-neighborhood scale for
  that separation package:
  `quarter_infsep_closedBall_disjoint_closedBall_breathingRoots`
  and
  `quarter_infsep_sphere_disjoint_sphere_breathingRoots`
  specialize the strict-radius disjointness theorems to the concrete radius
  `infsep(range breathingRoot) / 4`.
- The local nonvanishing and contour bridge have now been transported to that
  separated-circle scale:
  `localFactorAt_nonzero_closedBall_quarter_infsep`
  and
  `circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_quarter_infsep`
  give the same specific contour formula on the quarter-`infsep` circles.
- The repo now has a finite-subset multi-circle sum theorem at the separated
  quarter-`infsep` scale:
  `sum_circleIntegral_breathingFunction_quarter_infsep_eq_two_pi_I_mul_sum_residueCandidate`
  proves that for any finite set of breathing roots, the sum of the
  corresponding quarter-`infsep` circle integrals equals `2πi` times the sum
  of the explicit residue candidates.
- The all-roots zero statement is now packaged as a corollary of that finite
  subset formula:
  `sum_circleIntegral_breathingFunction_quarter_infsep_allRoots_eq_zero`
  shows that the sum of the circle integrals over the full family of separated
  quarter-`infsep` breathing-root circles is zero.
- The local contour package now also works uniformly at every common separated
  radius:
  `circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_of_lt_half_infsep`,
  `sum_circleIntegral_breathingFunction_of_lt_half_infsep_eq_two_pi_I_mul_sum_residueCandidate`,
  and
  `sum_circleIntegral_breathingFunction_of_lt_half_infsep_allRoots_eq_zero`
  extend the single-root, finite-subset, and all-roots formulas to any radius
  `R` satisfying `0 < R < infsep(range breathingRoot) / 2`.
  This strengthens the local separated-circle layer without yet comparing those
  inner circles to any outer contour.
- The repo now also has its first explicit annular boundary comparison theorem
  for the breathing function:
  `breathingDenominator_ne_zero_of_mem_closedBall_lt_half_infsep`,
  `continuousOn_breathingFunction_closedAnnulus_lt_half_infsep`,
  `differentiableOn_breathingFunction_openAnnulus_lt_half_infsep`,
  and
  `circleIntegral_breathingFunction_eq_of_le_lt_half_infsep`
  prove that for any fixed breathing root `breathingRoot k` and any
  `0 < r ≤ R < infsep(range breathingRoot) / 2`, the circle integrals of
  `breathingFunction` over the concentric circles of radii `r` and `R` agree.
  This is a genuine same-center annulus theorem built from Mathlib's annulus
  API; it still does not compare several disjoint inner circles to one outer
  contour.
- The same-center radius-invariance layer now also has a finite-family form:
  `sum_circleIntegral_breathingFunction_eq_of_le_lt_half_infsep`
  proves that for any finite set of breathing roots and any common radii
  `0 < r ≤ R < infsep(range breathingRoot) / 2`, the sum of the corresponding
  breathing-function circle integrals at radius `R` equals the sum at radius
  `r`.
  This is still an internal separated-regime comparison, not yet an enclosing
  outer-contour theorem.
- The repo now also has its first explicit enclosing outer-contour theorem for
  the breathing function:
  `norm_breathingRoot_eq_one`,
  `breathingDenominator_ne_zero_of_one_lt_norm`,
  `continuousOn_breathingFunction_closedAnnulus_of_one_lt`,
  `differentiableOn_breathingFunction_openAnnulus_of_one_lt`,
  `circleIntegral_breathingFunction_eq_of_one_lt_le`,
  `norm_breathingFunction_le_two_div_radius_pow_of_mem_sphere_of_two_le`,
  and
  `circleIntegral_breathingFunction_eq_zero_of_one_lt`
  show that every origin-centered circle of radius `R > 1` has breathing
  integral `0`.
  This is a real outer-contour statement for the specific function
  `z ↦ 1 / (z^13 - 1)`, proved by an origin-centered annulus theorem plus an
  explicit large-radius decay estimate, not by a general residue API.
- The first honest inner-to-outer comparison theorem is now present too:
  `sum_circleIntegral_breathingFunction_of_lt_half_infsep_allRoots_eq_outerCircle_of_one_lt`
  proves that for any separated inner radius
  `0 < r < infsep(range breathingRoot) / 2`
  and any origin-centered outer radius `R > 1`, the sum of the full family of
  breathing-root circle integrals equals that enclosing outer-circle integral.
  The proof stays precise: both sides are separately shown to be `0`.
  This is therefore an explicit enclosing-contour comparison for the full
  breathing-root family, but it is not yet a finite-subset theorem and not yet
  a direct multi-boundary decomposition theorem.
- The repo now also has a direct subset-sensitive single-circle contour
  theorem:
  `breathingRootsInBall`,
  `circleIntegral_kernel_eq_zero_of_not_mem_closedBall`,
  and
  `circleIntegral_breathingFunction_eq_two_pi_I_mul_sum_residueCandidate_of_no_boundary_roots`
  prove that for any center `c`, any radius `R > 0`, and any circle `C(c, R)`
  whose boundary contains no breathing root, the circle integral of
  `breathingFunction` equals `2πi` times the sum of the explicit residue
  candidates over exactly the breathing roots strictly inside
  `Metric.ball c R`.
  This is the first honest proper-subset/nonzero contour theorem in the repo,
  and it is obtained from the concrete partial-fraction identity in
  `ResidueDefinition`, not from a general residue API.
- The repo now also has the corresponding enclosing-circle to local-circles
  comparison theorem:
  `circleIntegral_breathingFunction_eq_sum_localCircleIntegrals_of_lt_half_infsep_of_no_boundary_roots`
  proves that any circle `C(c, R)` with `R > 0` and no breathing root on its
  boundary has the same integral as the sum of the breathing-function integrals
  over the separated local circles of any common radius
  `0 < r < infsep(range breathingRoot) / 2` around exactly the enclosed
  breathing roots.
  This gives a real proper-subset boundary-comparison theorem without invoking
  a general multi-boundary residue package.
- The repo now also has its first honest noncircular outer-boundary theorem:
  `integral_boundary_rect_breathingFunction_eq_zero_of_breathingDenominator_ne_zero`
  and
  `integral_boundary_rect_breathingFunction_eq_zero_of_no_breathingRoots`
  prove that the boundary integral of `breathingFunction` around a closed
  rectangle is zero whenever the rectangle contains no poles, equivalently no
  breathing roots.
  This moves the contour layer beyond circles while staying inside Mathlib's
  existing rectangle-boundary Cauchy-Goursat support.
- The repo now also has a rectangle-kernel support layer:
  `boundaryRectIntegral`,
  `closedRect`,
  `boundaryRectIntegral_sub_inv_eq_zero_of_not_mem_closedRect`,
  `boundaryRectIntegral_inv_centeredSquare`,
  and
  `boundaryRectIntegral_sub_inv_arbitraryCenterSquare`,
  and
  `boundaryRectIntegral_sub_inv_eq_two_pi_I_of_mem_interior_closedRect`
  package the coordinate rectangle boundary integral, prove that the standard
  kernel `(z - a)⁻¹` contributes `0` when its pole `a` lies outside the closed
  rectangle, prove the explicit centered-square kernel value
  `2πi` for `z ↦ z⁻¹` on `[-r, r] × [-r, r]`, and transport that computation
  to the arbitrary-center square
  `[(a.re - r), (a.re + r)] × [(a.im - r), (a.im + r)]`, and then to an
  arbitrary positively oriented rectangle whose pole lies in the interior.
- The repo now also has its first honest noncircular nonzero square theorem
  for the specific breathing function:
  `boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_of_no_otherRoots_centeredSquare`
  proves that if a square centered at `breathingRoot k` contains no other
  breathing roots, then the rectangle boundary integral of `breathingFunction`
  around that square is exactly `2πi * residueCandidateAt k`.
  This is still deliberately local and specific: it does not introduce a
  generic rectangle residue API, and it keeps the geometric hypothesis explicit
  instead of hiding it behind an unproved canonical square scale.
- The repo now also has the canonical small-square corollary:
  `quarter_infsep_closedRect_excludes_other_breathingRoots`
  derives the needed square-isolation hypothesis from the global breathing-root
  separation package, and
  `boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_quarter_infsep_centeredSquare`
  packages the resulting quarter-`infsep` centered-square boundary integral
  formula for `breathingFunction`.
  This keeps the theorem specific to `1 / (z^13 - 1)` while removing the last
  ad hoc geometric hypothesis from the local noncircular square layer.
- The repo now also has its first honest finite-enclosure rectangle theorem:
  `breathingRootsInInteriorRect`
  and
  `boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_sum_residueCandidate_of_interior_or_outside`
  show that if every breathing root is either strictly inside a positively
  oriented rectangle or completely outside its closed region, then the
  rectangle boundary integral of `breathingFunction` is exactly `2πi` times
  the sum of `residueCandidateAt` over the enclosed labels.
  This is still deliberately explicit and specific: it does not introduce a
  generic rectangle residue API, and it does not yet hide the geometric
  partition hypothesis behind an unproved boundary-safe selector theorem.
- The repo now also has the boundary-clean rectangle corollary:
  `boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_sum_residueCandidate_of_no_boundary_roots`
  shows that if no breathing root lies on the boundary of a positively
  oriented rectangle, then the same rectangle boundary integral is exactly
  `2πi` times the sum of `residueCandidateAt` over
  `breathingRootsInInteriorRect`.
  This packages the natural boundary-safe rectangle hypothesis into the
  existing explicit finite-enclosure theorem without introducing a generic
  rectangle residue API.
- The repo now also has the direct outer-rectangle to local-squares comparison:
  `sum_boundaryRectIntegral_breathingFunction_quarter_infsep_centeredSquare_eq_two_pi_I_mul_sum_residueCandidate`
  packages the canonical quarter-`infsep` local squares as a finite contour
  family, and
  `boundaryRectIntegral_breathingFunction_eq_sum_quarter_infsep_centeredSquareIntegrals_of_no_boundary_roots`
  shows that a boundary-clean outer rectangle has exactly the same
  breathing-function boundary integral as the sum of those local square
  boundary integrals over the enclosed breathing roots.
  This now aligns the noncircular outer-boundary theorem with the canonical
  local square layer without introducing any generic multi-boundary residue
  API.
- The repo now also has the all-roots cancellation corollary:
  `boundaryRectIntegral_breathingFunction_eq_zero_of_all_breathingRoots_mem_interior_closedRect`
  shows that if every breathing root lies strictly inside a positively
  oriented rectangle, then the boundary integral of `breathingFunction`
  around that rectangle is zero.
- The repo now also has the reusable variable-radius large-square corollary:
  `breathingRoot_mem_interior_closedRect_centeredSquare_of_one_lt`
  and
  `boundaryRectIntegral_breathingFunction_eq_zero_of_one_lt_centeredSquare`
  show that for every `R > 1`, every breathing root lies strictly inside the
  centered square `[-R, R] × [-R, R]`, and therefore the breathing-function
  boundary integral around that square is zero.
  This keeps the enclosing-rectangle corollary parameterized by a variable
  `R`, rather than hardcoding one specific box size.
- The repo now also has the asymmetric large-rectangle corollary:
  `breathingRoot_mem_interior_closedRect_of_encloses_unitSquare`
  and
  `boundaryRectIntegral_breathingFunction_eq_zero_of_encloses_unitSquare`
  show that if a positively oriented rectangle strictly contains the unit square
  `[-1, 1] × [-1, 1]`, then every breathing root lies in its interior and the
  breathing-function boundary integral around that rectangle is zero.
  This is the smallest reusable non-centered wrapper around the current
  norm-one root geometry.
- Exact next blocker for a broader contour layer:
  the repo now has a canonical single-root contour theorem, a strict-radius
  separation package, a fixed quarter-`infsep` separated-circle theorem, and a
  finite multi-circle cancellation formula, all now promoted to an arbitrary
  common radius `0 < R < infsep(range breathingRoot) / 2`, together with
  same-center annulus comparison theorems for one chosen breathing root and
  for finite common-radius families, plus an explicit origin-centered
  outer-circle theorem, a full-family inner-to-outer comparison corollary, and
  now a direct subset-sensitive single-circle formula for arbitrary centers,
  together with the matching enclosing-circle/local-circles comparison theorem.
  The remaining gap is no longer to compare one enclosing circle to the
  enclosed separated local circles; that bridge now exists. The remaining
  structural gap is no longer the first nonzero noncircular theorem, and it is
  no longer the lack of a canonical local square scale. The repo now has a
  quarter-`infsep` centered-square theorem with no extra geometric hypothesis,
  and it now also has the explicit finite-enclosure rectangle theorem, its
  boundary-clean corollary, the direct outer-rectangle to local-squares
  comparison theorem, the all-roots interior cancellation corollary, and the
  variable-radius `R > 1` large-square zero corollary, plus its asymmetric
  enclosing-rectangle wrapper. There is no longer a missing structural
  rectangle-comparison step in Phase 3.
  Further work in this direction is now convenience packaging rather than a
  foundational blocker.
- Next optional theorem if desired:
  generalize the canonical quarter-`infsep` local-square package from its fixed
  radius to a variable half-side.
  Concretely, prove a square-family theorem of the form
  `0 < r < infsep(range breathingRoot) / 4`
  implies that the centered square of half-side `r` around `breathingRoot k`
  contains no other breathing roots, then lift the current quarter-`infsep`
  square integral and outer/local-square comparison theorems to that variable
  square scale.

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

Started:
- `docs/FAQ.md` now includes a residue-specific reviewer entry that applies the
  `definition` / `theorem` / `interpretation` / `open` fence to
  `ResidueDefinition` and `CircleIntegralBreathing`.
- `docs/proofs/25_ResidueContourSlice.md` now inventories the exact theorem
  surface for `ResidueDefinition` and `CircleIntegralBreathing`, and the review
  entry points link to it.

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
