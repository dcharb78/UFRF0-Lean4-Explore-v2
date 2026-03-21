# AlphaRunning - Contour-Deformation Running Model

## Overview

This note inventories the new model layer in `UFRF/AlphaRunning.lean`.

The point of this module is narrow:

- it does not claim a first-principles QED or QCD renormalization theorem,
- it does not introduce a generic residue API,
- it does define a scale-indexed inverse-coupling observable built from the
  existing breathing contour package plus the existing Fourier phase-shift
  theorem from `Calculus.lean`.

## Definition

- `normalizedLocalContour k R`: the local breathing contour integral normalized
  by `2πi`.
- `standardModePhaseShift`: the discrete derivative of the standard breathing
  character at the cycle origin.
- `contourRunningIncrement k R`: midpoint coherence weight times Fourier phase
  shift times normalized local contour.
- `alphaInvRunningModel n k R`: the static `ufrf_alpha_inv` plus `n` copies of
  the contour running increment.
- `alphaPhaseObserver`: the selected physics observer channel, tied to phase
  `7` through `Phenomena.alpha_coordinate_refined`.
- `alphaPhaseObserverCorrection n R`: the deviation of the phase-7 observer
  channel from the static UFRF inverse fine-structure value.

## Theorem

- `normalizedLocalContour_eq_residueCandidate_of_lt_half_infsep`:
  in the existing separated-radius regime, the normalized local contour is
  exactly the explicit coefficient `residueCandidateAt k`.
- `normalizedLocalContour_eq_of_le_lt_half_infsep`:
  the normalized local contour is invariant under same-center contour
  deformation inside the separated annulus.
- `standardModePhaseShift_eq_breathingCharacter_one_sub_one`:
  the calculus discrete derivative of the standard character is the explicit
  Fourier phase-shift factor `χ(1) - 1`.
- `contourRunningIncrement_eq_midpoint_mul_phaseShift_mul_residueCandidate`:
  the running increment factors into midpoint coherence, Fourier phase shift,
  and the explicit local contour coefficient.
- `contourRunningIncrement_ne_zero_of_lt_half_infsep`:
  every allowed local observer channel carries a genuinely nonzero correction.
- `sum_contourRunningIncrement_allRoots_eq_zero`:
  the full breathing-root family of running increments cancels exactly.
- `alphaPhaseObserverCorrection_ne_zero_of_ne_zero_of_lt_half_infsep`:
  the selected phase-7 observer channel deviates nontrivially from the static
  UFRF value once a nonzero scale step is chosen.
- `alphaPhaseObserverCorrection_eq_phase7_scalar_mul_residueCandidate`:
  in the separated-radius regime, the selected observer correction is exactly a
  fixed scalar times the explicit phase-7 residue coefficient.
- `alphaPhaseObserverRealCorrection_eq_re_phase7_scalar_mul_residueCandidate`:
  taking the real channel of the selected observer correction yields a
  well-typed real observable induced by that same explicit phase-7 residue
  coefficient.
- `alphaPhaseObserverModelNormalization_eq_twenty_eight`:
  the current model normalization is explicitly `4 × 7 = 28`, packaging the
  simplex boundary factor `4` with the selected phase label `7`.
- `alphaPhaseObserverNormalizedRealCorrection_eq_re_phase7_scalar_mul_residueCandidate`:
  the normalized real comparison observable is the real phase-7 correction
  divided by that explicit model normalization.
- `alphaPhaseObserverNormalizedRealCorrection_eq_realCorrection_div_twenty_eight`:
  equivalently, the current normalized observable is just the real phase-7
  correction divided by `28`.
- `alphaPhaseObserverCorrection_eq_alpha_selected_scalar_mul_residueCandidate`:
  the selected observer correction is also packaged directly through
  `alphaPhaseObserver`, not only through a literal phase-7 residue label.
- `alphaPhaseObserverRealCorrection_eq_re_alpha_selected_scalar_mul_residueCandidate`:
  the real comparison observable likewise has an observer-indexed scalar/root
  formula.
- `alphaPhaseObserverNormalizedRealCorrection_eq_re_alpha_selected_scalar_mul_residueCandidate`:
  the normalized real comparison observable is likewise rewritten directly in
  terms of the alpha-selected observer channel.
- `alphaPhaseObserverCorrection_eq_of_le_lt_half_infsep`:
  the selected phase-7 observer correction is radius-invariant inside the
  separated annulus.
- `alphaPhaseObserverRealCorrection_eq_of_le_lt_half_infsep`:
  the induced real phase-7 observable is radius-invariant there as well.
- `alphaPhaseObserverNormalizedRealCorrection_eq_of_le_lt_half_infsep`:
  the normalized real comparison observable is likewise radius-invariant in the
  allowed contour-deformation regime.
- `alphaInvRunningModel_step`:
  one scale step adds exactly one contour running increment.
- `alphaInvRunningModel_eq_of_le_lt_half_infsep`:
  the full model is radius-invariant under the same allowed contour
  deformation.
- `sum_alphaInvRunningModel_allRoots_eq_thirteen_mul_static`:
  summing over all breathing roots recovers `13` copies of the static UFRF
  inverse fine-structure value.
- `avg_alphaInvRunningModel_allRoots_eq_static`:
  averaging over the full breathing-root family collapses back to the static
  UFRF inverse fine-structure candidate.
- `alphaPhaseObserverDeviationFromAverage_eq_phase7_residue_correction`:
  the selected phase-7 observer deviation from the global average is exactly
  the phase-7 residue correction term.
- `alphaPhaseObserverDeviationFromAverage_eq_phase7_scalar_mul_residueCandidate`:
  equivalently, the selected deviation is exactly a fixed scalar times the
  explicit phase-7 residue coefficient.
- `alphaPhaseObserverDeviationFromAverage_eq_alpha_selected_residue_correction`:
  the selected observer deviation from the global average is also packaged
  directly through `alphaPhaseObserver`.
- `alphaPhaseObserverDeviationFromAverage_eq_alpha_selected_scalar_mul_residueCandidate`:
  equivalently, that centered deviation is expressed directly with the
  alpha-selected residue coefficient.
- `alphaPhaseObserverRealCorrection_eq_re_deviationFromAverage`:
  the same real observable is also the real channel of the selected observer
  deviation from the breathing-root average.
- `alphaPhaseObserverNormalizedRealCorrection_eq_re_deviationFromAverage_div_twenty_eight`:
  equivalently, the normalized real observable is the real deviation from the
  global average divided by `28`.
- `alphaPhaseObserverNormalizedRealCorrection_is_alpha_selected_centered_comparison`:
  the current comparison quantity is exactly the normalized real part of the
  centered running observable at the alpha-selected observer channel.
- `phase7OneStepModelPrediction_eq_alpha_selected_centered_comparison`:
  the current radius-free one-step prediction is exactly that same
  alpha-selected centered comparison scalar.
- `alphaPhaseObserverNormalizedRealCorrection_one_eq_alpha_selected_centered_comparison`:
  equivalently, the one-step normalized observable itself is exactly that same
  alpha-selected centered comparison scalar.
- `alphaPhaseObserverNormalizedRealCorrection_one_eq_centered_comparison_of_floor_eq`:
  more generally, if a channel `k` satisfies `floor α mod 13 = k`, then the
  same one-step normalized observable is exactly the centered comparison scalar
  written at that `k`.
- `alphaPhaseObserverNormalizedRealCorrection_one_sub_codataGap_eq_alpha_selected_centered_comparison_sub_codataGap`:
  the one-step normalized observable minus the static CODATA 2022 gap is
  exactly that same alpha-selected centered comparison scalar minus the same
  gap.
- `alpha_selected_centered_comparison_sub_codataGap_unique_by_arithmetic`:
  if a channel `k` satisfies `floor α mod 13 = k`, then `k` is exactly the
  selected observer channel and the one-step normalized observable minus the
  static CODATA 2022 gap is exactly the centered comparison scalar written at
  that same `k`.
- `phase7OneStepModelResidual_eq_alpha_selected_centered_comparison_sub_codataGap`:
  the compared one-step residual is exactly the alpha-selected centered
  comparison scalar minus the static CODATA 2022 gap.
- `phase7OneStepModelResidual_is_alpha_selected_root_scalar_sub_codataGap`:
  equivalently, the compared one-step residual is the explicit
  alpha-selected root/scalar formula minus the static CODATA 2022 gap.
- `phase7OneStepModelResidual_eq_of_le_lt_half_infsep`:
  the one-step residual against the static CODATA 2022 gap is contour-invariant
  inside the allowed regime.
- `no_terminal_scale_for_alpha_running`:
  there is no terminal scale for the running/projection picture.
- `prime_tower_is_coherent`:
  every prime tower is coherent across all finite depths.
- `prime_start_pattern`:
  for every prime `p`, the tower starts with `1` and then resolves each coarse
  point into exactly `p` positions at the next depth.
- `ufrf_start_pattern`:
  specialized to the UFRF position, this is the concrete `1` then `13`
  start pattern.
- `cycle_seed_zero_to_one`:
  the smallest breathing step is the literal cycle move `0 -> 1`.
- `alphaPhaseObserver_is_seven_steps_on_seed_orbit`:
  the selected phase-7 observer is reached from the seed by seven universal
  successor steps, so phase `7` is a contextual point on the shared
  `0 -> 1 -> 2 -> ...` orbit rather than a separate absolute origin.
- `alphaPhaseObserver_enters_terminal_handoff_in_fixed_steps`:
  the selected phase-7 observer reaches REST after `+2`, the bridge strip after
  `+3,+4`, the seed/closure point after `+5`, and the restarted cycle point
  after `+6`.
- `alphaPhaseObserver_selected_by_alpha_arithmetic`:
  the selected observer channel is exactly the phase picked out by the integer
  projection of `ufrf_alpha_inv`.
- `phase7OneStepModelPrediction_is_alpha_selected_root_scalar`:
  the current one-step prediction is exactly the explicit root/scalar formula
  built from the alpha-selected observer channel, not just from a hard-coded
  phase literal.
- `alphaPhaseObserverNormalizedRealCorrection_one_eq_alpha_selected_root_scalar`:
  the one-step normalized observable itself is also packaged directly as that
  same explicit alpha-selected root/scalar formula.
- `alphaPhaseObserverNormalizedRealCorrection_one_eq_root_scalar_of_floor_eq`:
  more generally, if a channel `k` satisfies `floor α mod 13 = k`, then the
  same one-step normalized observable is exactly the root/scalar formula
  written at that `k`.
- `alphaPhaseObserverNormalizedRealCorrection_one_sub_codataGap_eq_alpha_selected_root_scalar_sub_codataGap`:
  equivalently, the one-step normalized observable minus the static CODATA 2022
  gap is also packaged directly as that same alpha-selected root/scalar formula
  minus the same gap.
- `alpha_selected_root_scalar_sub_codataGap_unique_by_arithmetic`:
  if a channel `k` satisfies `floor α mod 13 = k`, then `k` is exactly the
  selected observer channel and the one-step normalized observable minus the
  static CODATA 2022 gap is exactly the root/scalar formula written at that
  same `k`.
- `cycle_prime_channels_hit_alphaPhaseObserver`:
  each local cycle-prime channel `3, 5, 7, 11` hits the selected phase-7
  observer at some step.
- `cycle_prime_paths_cover_all_positions`:
  the four cycle-prime channels `3, 5, 7, 11` each carry a full 13-position
  visit order on the breathing cycle.
- `cycle_prime_paths_close_after_thirteen`:
  those same cycle-prime paths close after 13 steps.

## Interpretation

The safe interpretation is:

- contour deformation supplies the scale-stable local coefficient,
- Fourier differentiation supplies the scale-step phase multiplier,
- the calculus midpoint factor records the existing `6.5 / 13 = 1 / 2`
  coherence weight,
- together these yield a discrete RG-style ansatz for `α⁻¹`, anchored at the
  static UFRF value,
- on the analytic side, the global breathing function decomposes into explicit
  local coefficient channels, and the phase-7 observer is now collapsed to one
  explicit residue coefficient times a fixed scalar,
- the repo now also carries a real-valued observable extracted from that
  complex phase-7 correction, so comparison with measured real gaps is
  mathematically well-typed,
- the current external normalization choice is no longer hidden in the script;
  it is named explicitly in Lean as a model normalization factor,
- the current normalized real observable is also contour-deformation invariant
  inside the separated annulus, so the comparison quantity does not depend on
  the local radius parameter there,
- the full contour family still sums to zero, so the correction is properly
  understood as an observer-local projection of a globally conserved residue
  package, not as a new global constant,
- on the algebraic side, the safe bridge is only that zero-sum conservation is
  preserved under the native projection laws there as well,
- no theorem here identifies complex residues with p-adic projections, and no
  theorem here identifies CRT with the analytic partial-fraction package,
- the phase-7 observer channel is the current candidate local comparison
  channel,
- that channel is now selected in Lean by the alpha arithmetic itself, not just
  by external naming: `Int.floor ufrf_alpha_inv` lands on the same observer,
- the one-step prediction is also now rewritten directly in terms of the
  alpha-selected observer root/scalar package, rather than only as a formula
  with the literal phase `7`,
- the one-step normalized observable itself now also has direct
  observer-indexed root/scalar and centered-comparison forms, so the exposed
  comparison stack depends less on the legacy `phase7OneStepModelPrediction`
  wrapper,
- those same one-step formulas now also transport to any `k` that satisfies
  `floor α mod 13 = k`, so the arithmetic selection statement is no longer
  tied to one hard-coded symbol name,
- the correction, normalized observable, and centered deviation formulas now
  also have observer-indexed versions, so the exposed comparison story is less
  tied to literal phase syntax,
- phase `7` is now pinned as a visited point on the universal seed orbit,
  reached after seven ordinary successor steps from `0`, not as a separate
  absolute starting point,
- that observer channel is now also pinned geometrically: it is not an
  isolated phase label, but a fixed number of unit steps before the explicit
  `REST, bridge, bridge, seed/closure, restart` handoff block,
- the current comparison scalar is also no longer described only informally:
  Lean now packages it as the normalized real part of the observer-local
  running deviation after subtracting the global breathing-root average,
- the current radius-free one-step prediction is now proved to be exactly that
  same alpha-selected centered comparison scalar,
- the actual one-step normalized observable minus the static CODATA gap now
  also has direct observer-indexed centered-comparison and root/scalar forms,
  so the compared quantity no longer has to be introduced only through the
  legacy `phase7OneStepModelResidual` alias,
- the same compared quantity is now also unique in the arithmetic sense:
  any `k` satisfying `floor α mod 13 = k` is forced to be the selected
  observer channel and yields the same centered and root/scalar one-step gap
  comparison formulas,
- the one-step residual against the static CODATA gap is also contour-stable in
  the separated annulus, so the comparison does not depend on an arbitrary
  local radius choice there,
- the residual itself is now packaged as the alpha-selected centered
  comparison scalar minus the static CODATA gap, which matches the actual shape
  of the current external check,
- the same residual also has a direct alpha-selected root/scalar formula, so
  both the observer-indexed residue picture and the centered-comparison picture
  now land on the same compared quantity,
- the concurrency statement is now split cleanly into two layers:
  every prime starts the same `1` then `p` projection pattern through a
  coherent all-scale tower, and independently the local cycle-prime channels
  `3, 5, 7, 11` all hit phase `7`, traverse the full 13-position geometry
  beginning from the seed step `0 -> 1`, and close after 13 steps.

This is a model layer, not a proof that physical renormalization in QED is now
derived from the repo.

## External Numeric Check

- `scripts/alpha_phase7_residue_check.py` evaluates the phase-7 residue
  projection scalar externally.
- Current output:
  `gap = 0.000304598878...`
  `phase7_projection = 0.000305537183...`
  `abs_error = 9.38e-7`

This is evidence for the phase-7 residue channel, not yet a Lean theorem.

## Open

- No continuum `μ d/dμ` beta-function theorem is proved here.
- No weak-coupling or strong-coupling prediction theorem is proved here.
- Lean now does attach exact one-step rewrite theorems to the static CODATA gap
  comparison.
- No theorem yet proves the numeric accuracy of that CODATA comparison.
- The current `4 × 7` normalization is present only as an explicit model choice.
- The repo now proves that the current candidate comparison quantity is the
  normalized real, centered observable at the alpha-selected channel.
- What remains open is the stronger claim that this current candidate quantity
  is the uniquely correct physical-selection quantity.
- The dated CODATA comparison remains on the static side in
  `UFRF/FineStructure.lean`.
