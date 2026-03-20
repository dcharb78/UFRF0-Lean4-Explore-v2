# ResidueContourSlice - Specific Contour Package for `1 / (z^13 - 1)`

## Overview

This note inventories the exact proved surface of
`UFRF/ResidueDefinition.lean` and `UFRF/CircleIntegralBreathing.lean`.

The analytic layer is deliberately concrete:

- one function: `breathingFunction = 1 / (z^13 - 1)`,
- one explicit pole family: `breathingRoot`,
- one explicit coefficient family: `residueCandidateAt`,
- one circle/rectangle contour package built only for that function.

It is not a generic residue library.

## Key Definitions

- `breathingFunction`: the concrete meromorphic function `z ↦ 1 / (z^13 - 1)`.
- `breathingRoot k`: the `k`-indexed breathing root in the 13-cycle root family.
- `residueCandidateAt k`: the explicit local coefficient attached to
  `breathingRoot k`.
- `breathingRootsInInteriorRect x0 x1 y0 y1`: the finite set of breathing-root
  labels whose roots lie in the interior of the rectangle.

## Proved Theorem Surface

### Local Analytic Input

- `breathingDenominator_vanishes_at_root`: each labeled breathing root is
  actually a zero of `z^13 - 1`.
- `breathingFunction_eq_sum_residueCandidateAt_sub_inv`: away from breathing
  roots, `breathingFunction` is exactly the explicit finite sum of kernel terms
  `residueCandidateAt j * (z - breathingRoot j)⁻¹`.
- `breathingFunction_simplePole_limit`: the desingularized local limit at each
  `breathingRoot k` is the explicit coefficient `residueCandidateAt k`.
- `total_residue_candidate_zero`: the global sum of the explicit coefficients is
  zero.

### Local Contour Theorems

- `circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_of_lt_half_infsep`:
  the local circle around one breathing root integrates to `2πi` times the
  explicit coefficient, under the proven separation bound.
- `boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_quarter_infsep_centeredSquare`:
  the canonical quarter-`infsep` square around one breathing root gives the
  same `2πi` local coefficient formula.

### Finite Enclosure Theorems

- `boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_sum_residueCandidate_of_no_boundary_roots`:
  a boundary-clean rectangle integrates to `2πi` times the sum of the explicit
  coefficients for exactly the breathing roots in its interior.
- `sum_boundaryRectIntegral_breathingFunction_quarter_infsep_centeredSquare_eq_two_pi_I_mul_sum_residueCandidate`:
  a finite family of canonical local squares sums to the matching finite sum of
  coefficients.
- `boundaryRectIntegral_breathingFunction_eq_sum_quarter_infsep_centeredSquareIntegrals_of_no_boundary_roots`:
  a boundary-clean outer rectangle equals the sum of the enclosed canonical
  local square integrals.

### Large-Region Cancellation Corollaries

- `boundaryRectIntegral_breathingFunction_eq_zero_of_all_breathingRoots_mem_interior_closedRect`:
  if all breathing roots lie strictly inside the rectangle, the boundary
  integral is zero.
- `boundaryRectIntegral_breathingFunction_eq_zero_of_one_lt_centeredSquare`:
  for every `R > 1`, the centered square `[-R, R] × [-R, R]` has zero boundary
  integral.
- `boundaryRectIntegral_breathingFunction_eq_zero_of_encloses_unitSquare`:
  any positively oriented rectangle strictly containing `[-1, 1] × [-1, 1]`
  has zero boundary integral.

## Boundary Of The Current Proof Surface

- No generic residue theorem is proved here.
- No generic `Res` API is introduced here.
- No Laurent-series or monodromy package is provided here.
- No projection law is promoted into a complex-analytic residue theorem here.
- No modular-residue language from `ZMod 13` is identified with complex
  residues here.

## Suggested Audit Order

1. Read `UFRF/ResidueDefinition.lean` for the concrete function, pole data, and
   simple-pole limit.
2. Read `UFRF/CircleIntegralBreathing.lean` for the local contour theorems,
   finite-enclosure package, and large-rectangle zero corollaries.
3. Read `docs/FAQ.md` for the reviewer-facing `definition` / `theorem` /
   `interpretation` / `open` fence.
