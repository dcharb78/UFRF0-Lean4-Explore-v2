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
- `alphaPhaseObserver`: the selected physics observer channel, tied to label
  `7` through `Phenomena.alpha_coordinate_refined`.
- `alphaPhaseObserverCorrection n R`: the deviation of the selected observer
  channel from the static UFRF inverse fine-structure value.
- `alphaPhaseObserverOneStepComparison`: observer-indexed name for the current
  one-step comparison scalar.
- `alphaCodata2022Gap`: the static UFRF-to-CODATA 2022 gap used for the
  current comparison layer.
- `alphaPhaseObserverOneStepResidual R`: observer-indexed name for the current
  one-step comparison residual against the static CODATA 2022 gap.
- `alphaPhaseObserverResidueCheckAbsError`: script-aligned absolute error
  between the observer-indexed one-step comparison scalar and the static
  CODATA 2022 gap.

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
  the selected observer channel deviates nontrivially from the static
  UFRF value once a nonzero scale step is chosen.
- `alphaPhaseObserverCorrection_eq_phase7_scalar_mul_residueCandidate`:
  in the separated-radius regime, the selected observer correction is exactly a
  fixed scalar times the explicit legacy `7`-channel residue coefficient.
- `alphaPhaseObserverRealCorrection_eq_re_phase7_scalar_mul_residueCandidate`:
  taking the real channel of the selected observer correction yields a
  well-typed real observable induced by that same explicit legacy residue
  coefficient.
- `alphaPhaseObserverModelNormalization_eq_twenty_eight`:
  the current model normalization is explicitly `4 × 7 = 28`, packaging the
  simplex boundary factor `4` with the selected phase label `7`.
- `alphaPhaseObserverModelNormalization_inherits_simplex_boundary_and_selected_label`:
  equivalently, that same current normalization is now also packaged through
  the arithmetic-selected observer itself: the normalization is the simplex
  boundary factor times the selected observer label, so the current `/ 28`
  rule is structurally inherited rather than appearing only as a raw scalar.
- `alphaPhaseObserverNormalizedRealCorrection_eq_re_phase7_scalar_mul_residueCandidate`:
  the normalized real comparison observable is the real selected-observer correction
  divided by that explicit model normalization.
- `alphaPhaseObserverNormalizedRealCorrection_eq_realCorrection_div_twenty_eight`:
  equivalently, the current normalized observable is just the real selected-observer
  correction divided by `28`.
- `alphaPhaseObserverNormalizedRealCorrection_eq_realCorrection_div_inherited_normalization`:
  equivalently again, the same normalized observable is the real
  selected-observer correction divided by the inherited simplex-boundary-times-
  selected-label factor.
- `alphaPhaseObserverCorrection_eq_alpha_selected_scalar_mul_residueCandidate`:
  the selected observer correction is also packaged directly through
  `alphaPhaseObserver`, not only through a literal legacy wrapper label.
- `alphaPhaseObserverRealCorrection_eq_re_alpha_selected_scalar_mul_residueCandidate`:
  the real comparison observable likewise has an observer-indexed scalar/root
  formula.
- `alphaPhaseObserverNormalizedRealCorrection_eq_re_alpha_selected_scalar_mul_residueCandidate`:
  the normalized real comparison observable is likewise rewritten directly in
  terms of the alpha-selected observer channel.
- `alphaPhaseObserverCorrection_eq_of_le_lt_half_infsep`:
  the selected observer correction is radius-invariant inside the
  separated annulus.
- `alphaPhaseObserverRealCorrection_eq_of_le_lt_half_infsep`:
  the induced real selected-observer observable is radius-invariant there as well.
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
  the selected observer deviation from the global average is exactly
  the legacy `7`-channel residue correction term.
- `alphaPhaseObserverDeviationFromAverage_eq_phase7_scalar_mul_residueCandidate`:
  equivalently, the selected deviation is exactly a fixed scalar times the
  explicit legacy `7`-channel residue coefficient.
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
- `alpha_selected_centered_comparison_eq_alpha_selected_root_scalar`:
  equivalently, those same observer-indexed centered and root/scalar
  presentations are exactly the same normalized real quantity.
- `alphaPhaseObserverOneStepComparison_is_alpha_selected_root_scalar`:
  the observer-indexed one-step comparison alias is the same explicit
  alpha-selected root/scalar formula as the historical legacy wrapper.
- `phase7OneStepModelPrediction_eq_alpha_selected_centered_comparison`:
  the current radius-free one-step prediction is exactly that same
  alpha-selected centered comparison scalar.
- `phase7OneStepModelPrediction_bounds_d13`:
  the current radius-free one-step prediction lies in the tighter explicit
  interval
  `0.00030553718304 < prediction < 0.00030553718305`.
- `phase7OneStepModelPrediction_bounds_d16`:
  the same radius-free one-step prediction is now also pinned to the sharper
  explicit interval
  `0.0003055371830425 < prediction < 0.0003055371830426`.
- `phase7OneStepModelPrediction_bounds_d18`:
  the same radius-free one-step prediction is now also pinned to the still
  sharper explicit interval
  `0.000305537183042514 < prediction < 0.000305537183042516`.
- `phase7OneStepModelPrediction_bounds_d19`:
  the same radius-free one-step prediction is now also pinned to the still
  sharper explicit interval
  `0.0003055371830425148 < prediction < 0.0003055371830425159`.
- `phase7OneStepModelPrediction_bounds_d20`:
  the same radius-free one-step prediction is now also pinned to the still
  sharper explicit interval
  `0.00030553718304251501 < prediction < 0.00030553718304251502`.
- `phase7OneStepModelPrediction_bounds_d21`:
  the same radius-free one-step prediction is now also pinned to the sharper
  explicit interval
  `0.00030553718304251501169 < prediction < 0.00030553718304251501180`.
- `phase7OneStepModelPrediction_bounds_d27`:
  the same radius-free one-step prediction is now also pinned to the sharper
  explicit interval
  `0.000305537183042515011706524 < prediction < 0.000305537183042515011706528`.
- `phase7OneStepModelPrediction_bounds_d25`:
  equivalently, the same prediction also satisfies the weaker compatibility
  interval
  `0.0003055371830425150117064 < prediction < 0.0003055371830425150117084`.
- `phase7OneStepModelPrediction_bounds_d12`:
  equivalently, the same prediction also satisfies the weaker explicit
  `10^-12`-scale interval
  `0.0003055371830 < prediction < 0.0003055371832`.
- `phase7OneStepModelPrediction_rounds_to_0_0003055`:
  the current radius-free one-step prediction rounds to `0.0003055` at seven
  decimal places.
- `alphaPhaseObserverOneStepComparison_rounds_to_0_0003055`:
  equivalently, the observer-indexed one-step comparison alias rounds to that
  same seven-decimal value.
- `alphaPhaseObserverNormalizedRealCorrection_one_eq_oneStepComparison`:
  equivalently, the one-step normalized observable is also exactly the
  observer-indexed one-step comparison alias.
- `alphaPhaseObserverOneStepComparison_eq_alpha_selected_centered_comparison`:
  the observer-indexed one-step comparison alias is exactly that same
  alpha-selected centered comparison scalar.
- `alphaPhaseObserverNormalizedRealCorrection_one_eq_alpha_selected_centered_comparison`:
  equivalently, the one-step normalized observable itself is exactly that same
  alpha-selected centered comparison scalar.
- `alphaPhaseObserverNormalizedRealCorrection_eq_centered_comparison_of_floor_eq`:
  more generally, if a channel `k` satisfies `floor α mod 13 = k`, then the
  same normalized real observable at any discrete running step `n` is exactly
  the centered comparison scalar written at that `k`.
- `alphaPhaseObserverNormalizedRealCorrection_eq_root_scalar_of_floor_eq`:
  equivalently, at any discrete running step `n`, the same normalized real
  observable is also exactly the root/scalar formula written at that `k`.
- `alphaPhaseObserverNormalizedRealCorrection_one_eq_centered_comparison_of_floor_eq`:
  in particular, at `n = 1`, the one-step normalized observable is exactly the
  centered comparison scalar written at that `k`.
- `alpha_selected_centered_observable_eq_root_scalar_of_floor_eq`:
  more generally, at any discrete running step `n`, the centered observable
  formula and the explicit root/scalar formula written at `k` are exactly the
  same normalized real quantity.
- `alpha_selected_centered_comparison_eq_root_scalar_of_floor_eq`:
  for any channel `k` satisfying `floor α mod 13 = k`, the centered one-step
  comparison scalar and the explicit root/scalar one-step formula written at
  `k` are exactly the same quantity.
- `alpha_selected_centered_observable_unique_by_arithmetic`:
  if a channel `k` satisfies `floor α mod 13 = k`, then `k` is exactly the
  selected observer channel and the normalized real centered observable itself
  is exactly the centered comparison scalar written at that same `k`.
- `alpha_selected_root_scalar_observable_unique_by_arithmetic`:
  equivalently, if a channel `k` satisfies `floor α mod 13 = k`, then `k` is
  exactly the selected observer channel and the normalized real observable
  itself is exactly the root/scalar formula written at that same `k`.
- `alpha_selected_centered_comparison_unique_by_arithmetic`:
  if a channel `k` satisfies `floor α mod 13 = k`, then `k` is exactly the
  selected observer channel and the observer-indexed one-step comparison alias
  is exactly the centered one-step comparison scalar written at that same `k`.
- `alpha_selected_root_scalar_unique_by_arithmetic`:
  equivalently, if a channel `k` satisfies `floor α mod 13 = k`, then `k` is
  exactly the selected observer channel and the observer-indexed one-step
  comparison alias is exactly the root/scalar one-step formula written at that
  same `k`.
- `alphaPhaseObserverNormalizedRealCorrection_one_sub_codataGap_eq_alpha_selected_centered_comparison_sub_codataGap`:
  the one-step normalized observable minus the static CODATA 2022 gap is
  exactly that same alpha-selected centered comparison scalar minus the same
  gap.
- `alpha_selected_centered_comparison_sub_codataGap_unique_by_arithmetic`:
  if a channel `k` satisfies `floor α mod 13 = k`, then `k` is exactly the
  selected observer channel and the one-step normalized observable minus the
  static CODATA 2022 gap is exactly the centered comparison scalar written at
  that same `k`.
- `alphaPhaseObserverOneStepResidual_eq_oneStepComparison_sub_codataGap`:
  the observer-indexed one-step residual alias is exactly the observer-indexed
  one-step comparison alias minus the static CODATA 2022 gap.
- `phase7OneStepModelResidual_bounds_micro`:
  in the separated regime, the one-step residual against the static CODATA
  2022 gap lies in the explicit micro interval
  `0.000000921017 < residual < 0.000000947269`.
- `phase7OneStepModelResidual_bounds_d13`:
  in the separated regime, the same one-step residual is also pinned to the
  tighter explicit interval
  `0.0000009383045 < residual < 0.0000009383047`.
- `phase7OneStepModelResidual_bounds_d14`:
  in the separated regime, the same one-step residual is also pinned to the
  tighter explicit interval
  `0.00000093830460 < residual < 0.00000093830462`.
- `phase7OneStepModelResidual_bounds_d15`:
  in the separated regime, the same one-step residual is also pinned to the
  tighter explicit interval
  `0.000000938304607 < residual < 0.000000938304618`.
- `phase7OneStepModelResidual_bounds_d16`:
  in the separated regime, the same one-step residual is also pinned to the
  sharper explicit interval
  `0.0000009383046099 < residual < 0.0000009383046101`.
- `phase7OneStepModelResidual_bounds_d17`:
  in the separated regime, the same one-step residual is also pinned to the
  sharper explicit interval
  `0.00000093830460994 < residual < 0.00000093830460997`.
- `phase7OneStepModelResidual_bounds_d18`:
  in the separated regime, the same one-step residual is also pinned to the
  sharper explicit interval
  `0.000000938304609953 < residual < 0.000000938304609958`.
- `phase7OneStepModelResidual_bounds_d19`:
  in the separated regime, the same one-step residual is also pinned to the
  sharper explicit interval
  `0.0000009383046099546 < residual < 0.0000009383046099571`.
- `phase7OneStepModelResidual_bounds_d20`:
  in the separated regime, the same one-step residual is also pinned to the
  sharper explicit interval
  `0.00000093830460995488 < residual < 0.00000093830460995615`.
- `phase7OneStepModelResidual_bounds_d21`:
  in the separated regime, the same one-step residual is now also pinned to
  the sharper explicit interval
  `0.000000938304609955807 < residual < 0.000000938304609955811`.
- `phase7OneStepModelResidual_bounds_d25`:
  in the separated regime, the same one-step residual is now also pinned to
  the sharper explicit interval
  `0.0000009383046099558092932 < residual < 0.0000009383046099558094159`.
- `phase7OneStepModelResidual_bounds_d26`:
  in the separated regime, the same one-step residual is now also pinned to
  the sharper explicit interval
  `0.00000093830460995580931173 < residual < 0.00000093830460995580931192`.
- `phase7OneStepModelResidual_bounds_d27`:
  in the separated regime, the same one-step residual is now also pinned to
  the sharper explicit interval
  `0.000000938304609955809311781 < residual < 0.000000938304609955809311912`.
- `phase7OneStepModelResidual_bounds_d12`:
  equivalently, the same residual also satisfies the weaker
  `10^-12`-scale interval
  `0.0000009383044 < residual < 0.0000009383048`.
- `alphaPhaseObserverOneStepResidual_bounds_micro`:
  equivalently, the observer-indexed one-step residual alias satisfies that
  same explicit micro interval.
- `alphaPhaseObserverOneStepResidual_bounds_d13`:
  equivalently, the observer-indexed one-step residual alias satisfies that
  same tighter explicit interval
  `0.0000009383045 < residual < 0.0000009383047`.
- `alphaPhaseObserverOneStepResidual_bounds_d14`:
  equivalently, the observer-indexed one-step residual alias also satisfies the
  tighter explicit interval
  `0.00000093830460 < residual < 0.00000093830462`.
- `alphaPhaseObserverOneStepResidual_bounds_d15`:
  equivalently, the observer-indexed one-step residual alias also satisfies the
  tighter explicit interval
  `0.000000938304607 < residual < 0.000000938304618`.
- `alphaPhaseObserverOneStepResidual_bounds_d16`:
  equivalently, the observer-indexed one-step residual alias also satisfies the
  sharper explicit interval
  `0.0000009383046099 < residual < 0.0000009383046101`.
- `alphaPhaseObserverOneStepResidual_bounds_d17`:
  equivalently, the observer-indexed one-step residual alias also satisfies the
  sharper explicit interval
  `0.00000093830460994 < residual < 0.00000093830460997`.
- `alphaPhaseObserverOneStepResidual_bounds_d18`:
  equivalently, the observer-indexed one-step residual alias also satisfies the
  sharper explicit interval
  `0.000000938304609953 < residual < 0.000000938304609958`.
- `alphaPhaseObserverOneStepResidual_bounds_d19`:
  equivalently, the observer-indexed one-step residual alias also satisfies the
  sharper explicit interval
  `0.0000009383046099546 < residual < 0.0000009383046099571`.
- `alphaPhaseObserverOneStepResidual_bounds_d20`:
  equivalently, the observer-indexed one-step residual alias also satisfies the
  sharper explicit interval
  `0.00000093830460995488 < residual < 0.00000093830460995615`.
- `alphaPhaseObserverOneStepResidual_bounds_d21`:
  equivalently, the observer-indexed one-step residual alias also satisfies the
  sharper explicit interval
  `0.000000938304609955807 < residual < 0.000000938304609955811`.
- `alphaPhaseObserverOneStepResidual_bounds_d25`:
  equivalently, the observer-indexed one-step residual alias also satisfies the
  sharper explicit interval
  `0.0000009383046099558092932 < residual < 0.0000009383046099558094159`.
- `alphaPhaseObserverOneStepResidual_bounds_d26`:
  equivalently, the observer-indexed one-step residual alias also satisfies the
  sharper explicit interval
  `0.00000093830460995580931173 < residual < 0.00000093830460995580931192`.
- `alphaPhaseObserverOneStepResidual_bounds_d27`:
  equivalently, the observer-indexed one-step residual alias also satisfies the
  sharper explicit interval
  `0.000000938304609955809311781 < residual < 0.000000938304609955809311912`.
- `alphaPhaseObserverOneStepResidual_bounds_d12`:
  equivalently, the observer-indexed one-step residual alias also satisfies the
  weaker `10^-12`-scale interval
  `0.0000009383044 < residual < 0.0000009383048`.
- `phase7OneStepModelResidual_abs_lt_one_millionth`:
  in the separated regime, the absolute one-step residual against the static
  CODATA 2022 gap is bounded above by `0.000001`.
- `alphaPhaseObserverOneStepResidual_abs_lt_one_millionth`:
  equivalently, the observer-indexed one-step residual alias satisfies that
  same absolute `10⁻⁶` bound.
- `alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs`:
  in the separated regime, that script-aligned absolute error is exactly the
  absolute value of the observer-indexed one-step residual alias.
- `alphaPhaseObserverResidueCheckAbsError_eq_modelPrediction_sub_codataGap_abs`:
  in the separated regime, that same script-aligned absolute error is exactly
  the absolute projected difference `|phase7OneStepModelPrediction -
  alphaCodata2022Gap|`.
- `alphaPhaseObserverResidueCheckAbsError_bounds_micro`:
  the script-aligned absolute error lies in the explicit micro interval
  `0.000000921017 < error < 0.000000947269`.
- `alphaPhaseObserverResidueCheckAbsError_bounds_d13`:
  the same script-aligned absolute error is also pinned to the tighter
  explicit interval
  `0.0000009383045 < error < 0.0000009383047`.
- `alphaPhaseObserverResidueCheckAbsError_bounds_d14`:
  the same script-aligned absolute error is also pinned to the tighter
  explicit interval
  `0.00000093830460 < error < 0.00000093830462`.
- `alphaPhaseObserverResidueCheckAbsError_bounds_d15`:
  the same script-aligned absolute error is also pinned to the tighter
  explicit interval
  `0.000000938304607 < error < 0.000000938304618`.
- `alphaPhaseObserverResidueCheckAbsError_bounds_d16`:
  the same script-aligned absolute error is also pinned to the sharper
  explicit interval
  `0.0000009383046099 < error < 0.0000009383046101`.
- `alphaPhaseObserverResidueCheckAbsError_bounds_d17`:
  the same script-aligned absolute error is also pinned to the sharper
  explicit interval
  `0.00000093830460994 < error < 0.00000093830460997`.
- `alphaPhaseObserverResidueCheckAbsError_bounds_d18`:
  the same script-aligned absolute error is also pinned to the sharper
  explicit interval
  `0.000000938304609953 < error < 0.000000938304609958`.
- `alphaPhaseObserverResidueCheckAbsError_bounds_d19`:
  the same script-aligned absolute error is also pinned to the sharper
  explicit interval
  `0.0000009383046099546 < error < 0.0000009383046099571`.
- `alphaPhaseObserverResidueCheckAbsError_bounds_d20`:
  the same script-aligned absolute error is also pinned to the sharper
  explicit interval
  `0.00000093830460995488 < error < 0.00000093830460995615`.
- `alphaPhaseObserverResidueCheckAbsError_bounds_d21`:
  the same script-aligned absolute error is now also pinned to the sharper
  explicit interval
  `0.000000938304609955807 < error < 0.000000938304609955811`.
- `alphaPhaseObserverResidueCheckAbsError_bounds_d25`:
  the same script-aligned absolute error is now also pinned to the sharper
  explicit interval
  `0.0000009383046099558092932 < error < 0.0000009383046099558094159`.
- `alphaPhaseObserverResidueCheckAbsError_bounds_d26`:
  the same script-aligned absolute error is now also pinned to the sharper
  explicit interval
  `0.00000093830460995580931173 < error < 0.00000093830460995580931192`.
- `alphaPhaseObserverResidueCheckAbsError_bounds_d27`:
  the same script-aligned absolute error is now also pinned to the sharper
  explicit interval
  `0.000000938304609955809311781 < error < 0.000000938304609955809311912`.
- `alphaCodata2022Gap_gt_three_hundred_projection_error`:
  the static CODATA gap is more than `300` times larger than the
  script-aligned observer-local projection error, so the small matched
  quantity is not the raw static gap itself.
- `alphaPhaseObserverResidueCheckAbsError_bounds_d12`:
  equivalently, the same error also satisfies the weaker `10^-12`-scale
  interval
  `0.0000009383044 < error < 0.0000009383048`.
- `alphaPhaseObserverResidueCheckAbsError_lt_one_millionth`:
  in particular, the same script-aligned absolute error is strictly below the
  external script's `10⁻⁶` tolerance.
- `alphaPhaseObserverResidueCheckAbsError_rounds_to_0_0000009`:
  the same script-aligned absolute error rounds to `0.0000009` at seven
  decimal places.
- `alphaCodata2022Gap_bounds_d13`:
  the static UFRF-to-CODATA 2022 gap lies in the explicit interval
  `0.0003045988784 < gap < 0.0003045988785`.
- `alphaCodata2022Gap_bounds_d14`:
  the static UFRF-to-CODATA 2022 gap lies in the explicit interval
  `0.00030459887843 < gap < 0.00030459887844`.
- `alphaCodata2022Gap_bounds_d15`:
  the static UFRF-to-CODATA 2022 gap lies in the explicit interval
  `0.000304598878432 < gap < 0.000304598878433`.
- `alphaCodata2022Gap_bounds_d16`:
  the static UFRF-to-CODATA 2022 gap lies in the sharper explicit interval
  `0.0003045988784325 < gap < 0.0003045988784326`.
- `alphaCodata2022Gap_bounds_d17`:
  the static UFRF-to-CODATA 2022 gap lies in the sharper explicit interval
  `0.00030459887843255 < gap < 0.00030459887843257`.
- `alphaCodata2022Gap_bounds_d18`:
  the static UFRF-to-CODATA 2022 gap lies in the sharper explicit interval
  `0.000304598878432558 < gap < 0.000304598878432561`.
- `alphaCodata2022Gap_bounds_d19`:
  the static UFRF-to-CODATA 2022 gap lies in the sharper explicit interval
  `0.0003045988784325588 < gap < 0.0003045988784325602`.
- `alphaCodata2022Gap_bounds_d20`:
  the static UFRF-to-CODATA 2022 gap lies in the sharper explicit interval
  `0.00030459887843255887 < gap < 0.00030459887843256013`.
- `alphaCodata2022Gap_bounds_d21`:
  the derived `AlphaRunning` gap alias now also lies in the sharper explicit
  interval
  `0.000304598878432559201 < gap < 0.000304598878432559204`.
- `alphaCodata2022Gap_bounds_d25`:
  the derived `AlphaRunning` gap alias now also lies in the sharper explicit
  interval
  `0.0003045988784325592023841 < gap < 0.0003045988784325592023968`.
- `alphaCodata2022Gap_bounds_d26`:
  the derived `AlphaRunning` gap alias now also lies in the sharper explicit
  interval
  `0.00030459887843255920239461 < gap < 0.00030459887843255920239475`.
- `alphaCodata2022Gap_bounds_d27`:
  the derived `AlphaRunning` gap alias now also lies in the sharper explicit
  interval
  `0.000304598878432559202394616 < gap < 0.000304598878432559202394743`.
- `alphaCodata2022Gap_rounds_to_0_000304598878`:
  equivalently, that same static gap rounds to `0.000304598878` at the
  `10^-12` place.
- `phase7OneStepModelResidual_abs_lt_one_thousandth`:
  in the separated regime, the absolute one-step residual against the static
  CODATA 2022 gap is bounded above by `0.001`.
- `alphaPhaseObserverOneStepResidual_abs_lt_one_thousandth`:
  equivalently, the observer-indexed one-step residual alias satisfies that
  same absolute `0.001` bound.
- `phase7OneStepModelResidual_eq_alpha_selected_centered_comparison_sub_codataGap`:
  the compared one-step residual is exactly the alpha-selected centered
  comparison scalar minus the static CODATA 2022 gap.
- `alphaPhaseObserverOneStepResidual_eq_alpha_selected_centered_comparison_sub_codataGap`:
  equivalently, the observer-indexed one-step residual alias is exactly that
  same centered comparison scalar minus the same gap.
- `phase7OneStepModelResidual_is_alpha_selected_root_scalar_sub_codataGap`:
  equivalently, the compared one-step residual is the explicit
  alpha-selected root/scalar formula minus the static CODATA 2022 gap.
- `alphaPhaseObserverOneStepResidual_is_alpha_selected_root_scalar_sub_codataGap`:
  equivalently, the observer-indexed one-step residual alias is the same
  alpha-selected root/scalar-minus-gap formula.
- `alpha_selected_centered_residual_unique_by_arithmetic`:
  if a channel `k` satisfies `floor α mod 13 = k`, then `k` is exactly the
  selected observer channel and the observer-indexed one-step residual alias is
  exactly the centered one-step comparison-minus-gap scalar written at that
  same `k`.
- `alpha_selected_root_scalar_residual_unique_by_arithmetic`:
  equivalently, if a channel `k` satisfies `floor α mod 13 = k`, then `k` is
  exactly the selected observer channel and the observer-indexed one-step
  residual alias is exactly the root/scalar-minus-gap formula written at that
  same `k`.
- `phase7OneStepModelResidual_eq_of_le_lt_half_infsep`:
  the one-step residual against the static CODATA 2022 gap is contour-invariant
  inside the allowed regime.
- `alphaPhaseObserverOneStepResidual_eq_of_le_lt_half_infsep`:
  the observer-indexed one-step residual alias is contour-invariant in that
  same allowed regime.
- `no_terminal_scale_for_alpha_running`:
  there is no terminal scale for the running/projection picture.
- `alpha_running_no_terminal_scale_and_handoff`:
  the running/projection layer also packages unbounded scale descent together
  with the local terminal handoff law `13 ↦ 3`, `14 ↦ 4` at every whole-cycle
  translate; this is a scale-indexed repetition theorem, not a coinductive
  all-scales-at-once object.
- `alpha_selected_observer_reaches_recurring_handoff`:
  the alpha-selected observer channel is the arithmetic-selected label, reaches
  closure and restart in fixed successor steps, and sits inside the same
  recurring `13 ↦ 3`, `14 ↦ 4` handoff package at every indexed scale; this is
  an observer-local bridge theorem, not a stronger physical-selection claim.
- `alpha_selected_observer_sits_on_prism_orbit_before_recurring_handoff`:
  a second exposed structural consequence is now packaged without touching the
  current measurement lane: the universal PRISM walk from `0` reaches every
  cycle position, the arithmetic-selected observer is specifically label `7`
  and is reached after seven successor steps, the closure point is still the
  contextual `13` / local `3` / cycle `0` location, and five/six more observer
  steps land at the same recurring `13 ↦ 3`, `14 ↦ 4` handoff at every indexed
  scale. This is still an observer-local structural theorem, not an absolute-
  origin or stronger physical-selection claim.
- `alpha_selected_centered_deviation_has_local_origin_and_recurring_handoff`:
  one layer earlier than the measured real observable, the centered complex
  deviation itself now also sits on that same structural package in one
  theorem: the current local start point reindexes to `0`, the observer
  channel is still the arithmetic-selected alpha observer, that centered
  complex deviation is the explicit alpha-selected root/scalar-residue
  quantity, and the same observer still sits inside the recurring
  `13 ↦ 3`, `14 ↦ 4` closure/restart package at every indexed scale. This is
  still a packaging theorem, not a stronger measurement-correctness claim.
- `alpha_selected_real_correction_has_local_origin_radius_invariance_and_recurring_handoff`:
  one layer earlier than the current `/ 28` comparison rule, the unnormalized
  real selected-observer correction itself now also sits on that same
  structural package in one theorem: the current local start point reindexes
  to `0`, the observer channel is still the arithmetic-selected alpha
  observer, the real correction is both the real part of the centered running
  deviation and the real part of the explicit alpha-selected
  root/scalar-residue quantity, that real correction is stable under allowed
  contour-radius changes, and the same observer still sits inside the
  recurring `13 ↦ 3`, `14 ↦ 4` closure/restart package at every indexed scale.
  This is still a packaging theorem, not a stronger measurement-correctness or
  unique-normalization claim.
- `alpha_selected_centered_observable_global_average_package_has_local_origin_radius_invariance_and_recurring_handoff`:
  the centered observer-local observable now also packages the conserved-average
  story in one theorem: the current local start point reindexes to `0`, the
  observer channel is still the arithmetic-selected alpha observer, the
  all-root average of the running model still collapses back to the static
  UFRF value, the centered observable is the normalized real part of the
  selected observer's deviation from that global average, that centered
  observable is stable under allowed contour-radius changes, and the same
  observer still sits inside the recurring `13 ↦ 3`, `14 ↦ 4`
  closure/restart package at every indexed scale. This is still a packaging
  theorem, not a stronger unique-normalization or physical-selection claim.
- `alpha_selected_centered_observable_reaches_recurring_handoff`:
  more generally, the exposed normalized real centered observable itself, at
  any discrete running step `n`, is attached to that same arithmetic-selected
  recurring-handoff channel: it is written at the selected observer and that
  same observer still reaches the recurring `13 ↦ 3`, `14 ↦ 4` closure/restart
  package at every indexed scale. This is still a packaging theorem, not a
  stronger measurement-correctness claim.
- `alpha_selected_centered_observable_has_local_origin_and_recurring_handoff`:
  the centered-observable package now makes the measurement-side chart explicit
  in one theorem: the current local start point reindexes to `0`, the observer
  channel is still the arithmetic-selected alpha observer, the measurement rule
  is still the normalized real part of the centered observable with model
  normalization `28`, and that same observer still sits inside the recurring
  `13 ↦ 3`, `14 ↦ 4` closure/restart package at every indexed scale. This is
  still a packaging theorem, not a stronger claim that every chart or
  measurement rule is equivalent.
- `alpha_selected_centered_observable_has_local_origin_radius_invariance_and_recurring_handoff`:
  the same centered-observable package now also carries its allowed-radius
  stability: within the admitted contour regime, the exposed measurement is
  unchanged when the contour radius varies from `r` to `R`, while the local
  chart still starts at `0` and the selected observer still sits on the same
  recurring `13 ↦ 3`, `14 ↦ 4` closure/restart package. This is still a
  packaging theorem, not a stronger claim that arbitrary measurement rules are
  equivalent.
- `alpha_selected_comparison_and_residual_reach_recurring_handoff`:
  the exposed observer-indexed one-step comparison and one-step residual are
  both attached to that same arithmetic-selected recurring-handoff channel:
  the comparison is the selected centered observable, the residual is that
  same quantity minus the static CODATA gap, and the selected observer still
  reaches closure/restart inside the recurring `13 ↦ 3`, `14 ↦ 4` package at
  every indexed scale. This is still a packaging theorem, not a stronger
  measurement-correctness claim.
- `alpha_selected_one_step_measurement_package_has_local_origin_and_recurring_handoff`:
  this is the smallest current one-step user-facing bundle in one theorem: the
  current local start point reindexes to `0`, the observer channel is still
  the arithmetic-selected alpha observer, the exposed one-step measurement
  rule is still the normalized real part of the centered observable with
  explicit `/ 28` normalization, the one-step comparison alias is exactly that
  same quantity, the one-step residual alias is that same quantity minus the
  static CODATA gap, and the same observer still sits inside the recurring
  `13 ↦ 3`, `14 ↦ 4` closure/restart package at every indexed scale. This is
  still a packaging theorem, not a stronger measurement-correctness claim.
- `alpha_selected_one_step_measurement_package_has_local_origin_radius_invariance_and_recurring_handoff`:
  the same one-step user-facing bundle now also carries its allowed-radius
  stability in one theorem: the current local start point still reindexes to
  `0`, the observer channel is still the arithmetic-selected alpha observer,
  the exposed one-step measurement is unchanged when the contour radius varies
  from `r` to `R` in the admitted regime, the one-step comparison alias is
  still the explicit `/ 28` centered-observable quantity, the one-step
  residual alias is still that same quantity minus the static CODATA gap and
  is likewise unchanged when the contour radius varies from `r` to `R`, and
  the same observer still sits inside the recurring `13 ↦ 3`, `14 ↦ 4`
  closure/restart package at every indexed scale. This is still a packaging
  theorem, not a stronger measurement-correctness claim.
- `alpha_selected_one_step_absolute_error_package_has_local_origin_and_recurring_handoff`:
  this extends the current one-step user-facing bundle by adding the
  script-aligned absolute-error identity in one theorem: the current local
  start point still reindexes to `0`, the observer channel is still the
  arithmetic-selected alpha observer, the exposed one-step measurement rule is
  still the explicit `/ 28` centered-observable quantity, the one-step
  residual alias is still that same quantity minus the static CODATA gap, the
  absolute error is exactly the absolute value of that one-step residual, and
  the same observer still sits inside the recurring `13 ↦ 3`, `14 ↦ 4`
  closure/restart package at every indexed scale. This is still a packaging
  theorem, not a stronger measurement-correctness claim.
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
- `alpha_running_coherent_start_and_handoff`:
  this bundles the safe nested reading in one theorem: the `13`-tower is
  coherent across finite depths, the exposed UFRF start pattern is `1` then
  `13`, the cycle-side seed move is `0 -> 1`, there is no bottom scale, and
  every whole-cycle translate still closes at local `3` and re-enters at
  local `4`; this is still a packaged scale-indexed theorem, not a single
  simultaneous-all-scales object.
- `alphaPhaseObserver_is_seven_steps_on_seed_orbit`:
  the selected observer label is reached from the seed by seven universal
  successor steps, so label `7` is a contextual point on the shared
  `0 -> 1 -> 2 -> ...` orbit rather than a separate absolute origin.
- `alphaPhaseObserver_enters_terminal_handoff_in_fixed_steps`:
  the selected observer label reaches REST after `+2`, the bridge strip after
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
- `alpha_selected_centered_comparison_sub_codataGap_eq_root_scalar_sub_codataGap_of_floor_eq`:
  for any channel `k` satisfying `floor α mod 13 = k`, the centered one-step
  comparison-minus-gap scalar and the root/scalar-minus-gap formula written at
  `k` are exactly the same quantity.
- `alpha_selected_root_scalar_sub_codataGap_unique_by_arithmetic`:
  if a channel `k` satisfies `floor α mod 13 = k`, then `k` is exactly the
  selected observer channel and the one-step normalized observable minus the
  static CODATA 2022 gap is exactly the root/scalar formula written at that
  same `k`.
- `cycle_prime_channels_hit_alphaPhaseObserver`:
  each local cycle-prime channel `3, 5, 7, 11` hits the selected
  observer at some step.
- `cycle_prime_paths_cover_all_positions`:
  the four cycle-prime channels `3, 5, 7, 11` each carry a full 13-position
  visit order on the breathing cycle.
- `cycle_prime_paths_close_after_thirteen`:
  those same cycle-prime paths close after 13 steps.
- `alpha_running_three_layer_concurrency_package`:
  the current safe three-layer reading is now also packaged in one theorem.
  Semantically this is now a running-side re-export of
  `Recursion.prism_walk_and_terminal_handoff_at_scale`:
  the cycle-side seed move is the literal `0 -> 1` step, the same PRISM walk
  from `0` reaches every cycle position, `13` is still `0` in the pure cycle
  chart while every whole-cycle translate still exposes the local handoff
  `13 ↦ 3`, `14 ↦ 4`, and there is still no bottom scale. This is still a
  packaged concurrency theorem for the cycle/recursion layer, not a claim that
  the projection tower, local cycle chart, and analytic observer package are
  one undifferentiated all-scales-at-once object.

## Interpretation

The safe interpretation is:

- contour deformation supplies the scale-stable local coefficient,
- Fourier differentiation supplies the scale-step phase multiplier,
- the calculus midpoint factor records the existing `6.5 / 13 = 1 / 2`
  coherence weight,
- together these yield a discrete RG-style ansatz for `α⁻¹`, anchored at the
  static UFRF value,
- on the analytic side, the global breathing function decomposes into explicit
  local coefficient channels, and the selected observer is now collapsed to one
  explicit residue coefficient times a fixed scalar,
- the repo now also carries a real-valued observable extracted from that
  complex selected-observer correction, so comparison with measured real gaps is
  mathematically well-typed,
- the current external normalization choice is no longer hidden in the script;
  it is named explicitly in Lean as a model normalization factor,
- the current normalized real observable is also contour-deformation invariant
  inside the separated annulus, so the comparison quantity does not depend on
  the local radius parameter there,
- the full contour family still sums to zero, so the correction is properly
  understood as an observer-local projection of a globally conserved residue
  package, not as a new global constant,
- on the algebraic side, the safe bridge is only that Lean separately proves
  projection-tower coherence/start-pattern facts and local cycle-prime
  visit-order facts there as well,
- no theorem here identifies complex residues with p-adic projections, and no
  theorem here identifies CRT with the analytic partial-fraction package,
- the selected observer channel is the current candidate local comparison
  channel,
- that channel is now selected in Lean by the alpha arithmetic itself, not just
  by external naming: `Int.floor ufrf_alpha_inv` lands on the same observer,
- the one-step prediction is also now rewritten directly in terms of the
  alpha-selected observer root/scalar package, rather than only as a formula
  with the literal phase `7`,
- the one-step normalized observable itself now also has direct
  observer-indexed root/scalar and centered-comparison forms, and Lean now
  also exposes an explicit `alphaPhaseObserverOneStepComparison` alias, so the
  exposed comparison stack depends less on the legacy
  `phase7OneStepModelPrediction` wrapper,
- those same one-step formulas now also transport to any `k` that satisfies
  `floor α mod 13 = k`, so the arithmetic selection statement is no longer
  tied to one hard-coded symbol name,
- Lean now also proves directly, for any such selected `k`, that the centered
  one-step comparison formula and the explicit root/scalar one-step formula are
  identical, both before and after subtracting the static CODATA gap,
- Lean now also packages the underlying normalized real centered observable
  itself with that same arithmetic uniqueness shape before any one-step alias
  is introduced,
- the same generic transport now also exists on the root/scalar side for any
  discrete running step `n`, so the centered and root/scalar presentations are
  matched before specializing to the one-step alias layer,
- Lean now also packages the raw one-step comparison alias itself with the
  same arithmetic uniqueness shape: any such `k` is forced to be the selected
  observer channel and yields the same centered and root/scalar one-step
  comparison formulas before the CODATA subtraction,
- the observer-indexed one-step residual alias now has the same arithmetic
  uniqueness packaging after the CODATA subtraction, so the exposed residual
  API matches the comparison API on both the centered and root/scalar sides,
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
- Lean now also packages that centered observable itself, before any one-step
  specialization, on the same recurring-handoff channel as the selected
  observer across all discrete running steps `n`,
- that observer-indexed centered presentation is now also tied directly to the
  observer-indexed root/scalar presentation before any one-step or gap
  specialization, so the two current candidate packages are visibly the same
  quantity and not merely parallel rewrites through older aliases,
- the current radius-free one-step prediction is now proved to be exactly that
  same alpha-selected centered comparison scalar,
- the actual one-step normalized observable minus the static CODATA gap now
  also has direct observer-indexed centered-comparison and root/scalar forms,
  and Lean now also exposes an explicit `alphaPhaseObserverOneStepResidual`
  alias, so the compared quantity no longer has to be introduced only through
  the legacy `phase7OneStepModelResidual` wrapper,
- Lean now also proves a micro-scale numeric theorem about that compared
  quantity itself: throughout the separated regime, the exposed one-step
  residual lies in the explicit interval
  `0.000000921017 < residual < 0.000000947269`, and hence also satisfies the
  absolute bound `|residual| < 0.000001`,
- Lean now also proves a tighter `Complex.exp`-driven Taylor-remainder window
  for the actual one-step prediction itself:
  `0.0003055371830425 < prediction < 0.0003055371830426`,
- Lean now also sharpens that same prediction package again, now to the
  `d27` interval
  `0.000305537183042515011706524 < prediction < 0.000305537183042515011706528`,
- the stronger local `π` control on the static side now sharpens the
  CODATA-gap ingredient further to a `d26` interval
  `0.00030459887843255920239461 < gap < 0.00030459887843255920239475`,
- within `AlphaRunning`, the derived gap alias and the exposed
  residual/error window now reach `d26`:
  `0.00030459887843255920239461 < gap < 0.00030459887843255920239475` and
  `0.00000093830460995580931173 < residual,error < 0.00000093830460995580931192`,
- the earlier coarse `0.001` residual bound is still present as a simpler
  fallback estimate,
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
- Lean now also packages those exposed observer-indexed comparison/residual
  quantities on the same recurring-handoff channel as the selected observer,
  so the measurement-side formulas are no longer disconnected from the
  no-bottom-scale / closure-and-restart package,
- the concurrency statement is now split cleanly into two layers:
  every prime starts the same `1` then `p` projection pattern through a
  coherent all-scale tower, and independently the local cycle-prime channels
  `3, 5, 7, 11` all hit phase `7`, traverse the full 13-position geometry
  beginning from the seed step `0 -> 1`, and close after 13 steps.

This is a model layer, not a proof that physical renormalization in QED is now
derived from the repo.

## External Numeric Check

- `scripts/alpha_phase7_residue_check.py` evaluates the selected-observer residue
  projection scalar externally.
- Current output:
  `gap = 0.000304598878...`
  `phase7_projection = 0.000305537183...`
  `abs_error = 9.38e-7`

Lean now proves the real-number pass condition behind that check:
`alphaPhaseObserverResidueCheckAbsError_lt_one_millionth` formalizes that the
same absolute error is below `10⁻⁶`, and
`alphaPhaseObserverResidueCheckAbsError_bounds_micro` pins it to the explicit
window `0.000000921017 < error < 0.000000947269`.
The sharper theorem `alphaPhaseObserverResidueCheckAbsError_bounds_d13` now
also pins the same error to the tighter interval
`0.0000009383045 < error < 0.0000009383047`.
The still tighter theorem `alphaPhaseObserverResidueCheckAbsError_bounds_d14`
now pins the same error to
`0.00000093830460 < error < 0.00000093830462`.
The current `AlphaRunning` d27 theorem
`alphaPhaseObserverResidueCheckAbsError_bounds_d27`
now pins the same error to
`0.000000938304609955809311781 < error < 0.000000938304609955809311912`.
It also now proves seven-decimal rounding theorems for both the current
one-step comparison scalar and the script-aligned absolute error.
Separately, the derived `AlphaRunning` gap alias is now pinned to
`0.000304598878432559202394616 < gap < 0.000304598878432559202394743`,
while the stronger static-side control remains in `UFRF/FineStructure.lean`.
Lean now also makes the scale split explicit:
`alphaPhaseObserverResidueCheckAbsError =
|phase7OneStepModelPrediction - alphaCodata2022Gap|`,
and the static gap is more than `300` times larger than that observer-local
projection error.

What Lean still does not prove is the script's floating-point printout itself.

## Current Local Conclusion

- Within the current `AlphaRunning` model layer, the one-step
  observer/measurement bridge is now locally concluded in the narrow
  repo-supported sense: Lean packages the current one-step measurement story
  end to end, from the local origin `0` and the arithmetic-selected observer
  through the centered complex deviation, the normalized real `/ 28`
  measurement rule, the one-step comparison alias, the one-step residual
  alias, the script-aligned absolute-error identity, the allowed-radius
  invariance package, and the recurring `13 ↦ 3`, `14 ↦ 4` handoff.
- Further work on this exact bridge lane is now mostly convenience packaging
  rather than a missing theorem-level bridge.
- What is not concluded here is any stronger physical-selection claim, any
  proof that the current `/ 28` normalization rule is uniquely correct, any
  simultaneous all-scales object, or the external script's floating-point
  printout itself.
- The next meaningful pivot is either breadth, namely a second exposed
  observer/measurement-side consequence from the same structural mechanism, or
  stronger static alpha/CODATA-gap control beyond the current `d26` lane if
  the goal is more exposed decimals.

## Open

- No continuum `μ d/dμ` beta-function theorem is proved here.
- No weak-coupling or strong-coupling prediction theorem is proved here.
- Lean now does attach exact one-step rewrite theorems to the static CODATA gap
  comparison.
- Lean now proves an explicit micro residual window and an absolute
  `0.000001` bound on the one-step residual.
- Lean now also proves a tighter one-step prediction window; the exposed
  residual/error windows now reach `d27` on the current static-gap lane.
- Lean now also proves the real-number `10⁻⁶` pass condition checked by the
  external script.
- Lean now also proves seven-decimal rounding theorems for the exposed
  one-step comparison scalar and the script-aligned absolute error.
- Lean now also packages the derived `AlphaRunning` CODATA gap alias through a
  `d27` window, matching the stronger static-side control in
  `UFRF/FineStructure.lean`.
- Lean now sharpens the exposed one-step prediction package to `d27` by
  bounding the shared `π/13` prediction polynomial directly through the
  current order-20 `Complex.exp`-based Taylor route, while the exposed
  residual/error package now also reaches `d27`.
- What Lean still does not prove is the external script's floating-point output
  itself, or any stronger projection-law / physical-selection claim.
- The current `4 × 7` normalization is present only as an explicit model choice.
- The repo now proves that the current candidate comparison quantity is the
  normalized real, centered observable at the alpha-selected channel.
- What remains open is the stronger claim that this current candidate quantity
  is the uniquely correct physical-selection quantity.
- The CODATA reference value itself is still defined on the static side in
  `UFRF/FineStructure.lean`, while `UFRF/AlphaRunning.lean` now packages the
  derived comparison gap `alphaCodata2022Gap` and its one-step comparison
  theorems.
- If the next proof-heavy branch is pursued for further exposed tightening,
  the natural target is now stronger static alpha/CODATA-gap control beyond
  `d27`: the exposed `AlphaRunning` prediction surface and the exposed
  gap/residual/error surface now both reach `d27`.
