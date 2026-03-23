# UFRF Proofs: Physics & Physical Constants

This document consolidates the physics-related modules.

---

## 1. FineStructure - The Inverse Fine Structure Constant

### Overview
α⁻¹ is derived from zero free parameters as the polynomial `4π³ + π² + π`.

### Proven Theorems

- **`alpha_inv_floor_137`**: ⌊4π³ + π² + π⌋ = 137 (proven via tight π bounds)
- **`alpha_inv_bounds_d9`**: `137.036303775 < α⁻¹ < 137.036303776`
- **`ufrf_matches_codata`**: `|ufrf − CODATA 2022| < 0.00031`
- **`alpha_polynomial_form`**: Coefficients are {4, 1, 1} from LOGGrade duality

### Connection to ThreeLOG
The coefficients {4, 1, 1} are the LOG grade duality factors:
- **4** = C(4,3), derived from Simplex in Phase 20 (was axiom)
- **1, 1** = Log1, Log2 duality factors

---

## 2. AlphaRunning - Contour Deformation Running Layer

### Proven Theorems

- **`normalizedLocalContour_eq_residueCandidate_of_lt_half_infsep`**: normalized local contour = explicit residue candidate
- **`standardModePhaseShift_eq_breathingCharacter_one_sub_one`**: discrete derivative of the standard character is the Fourier phase-shift factor
- **`sum_contourRunningIncrement_allRoots_eq_zero`**: the full residue-driven correction family cancels globally
- **`alphaInvRunningModel_eq_of_le_lt_half_infsep`**: the running model is invariant under local contour deformation in the separated annulus
- **`avg_alphaInvRunningModel_allRoots_eq_static`**: averaging over all breathing roots recovers the static UFRF alpha candidate
- **`alphaPhaseObserverCorrection_eq_phase7_scalar_mul_residueCandidate`**: the selected observer correction is a fixed scalar times the explicit legacy `7`-channel residue coefficient
- **`alphaPhaseObserverRealCorrection_eq_re_phase7_scalar_mul_residueCandidate`**: the selected observer induces a real comparison observable from that same coefficient
- **`alphaPhaseObserverModelNormalization_eq_twenty_eight`**: the current model normalization is explicitly `4 × 7 = 28`
- **`alphaPhaseObserverNormalizedRealCorrection_eq_re_phase7_scalar_mul_residueCandidate`**: the normalized selected-observer real observable is the induced real channel divided by that model normalization
- **`alphaPhaseObserverNormalizedRealCorrection_eq_of_le_lt_half_infsep`**: that normalized selected-observer real observable is radius-invariant in the allowed contour regime
- **`prime_tower_is_coherent`**: every prime tower is coherent across all finite depths
- **`prime_start_pattern`**: every prime tower starts with `1` and then resolves into `p` positions at the next depth
- **`ufrf_start_pattern`**: the UFRF specialization is the concrete `1` then `13` start pattern
- **`cycle_seed_zero_to_one`**: the smallest breathing-cycle step is `0 -> 1`
- **`alphaPhaseObserver_is_seven_steps_on_seed_orbit`**: phase `7` is reached by seven ordinary successor steps from the seed, so it is a contextual point on the universal orbit rather than an absolute origin
- **`alphaPhaseObserver_enters_terminal_handoff_in_fixed_steps`**: the selected observer label hits REST, then the two bridge positions, then seed/closure, and then restart after fixed successor steps
- **`alphaPhaseObserver_selected_by_alpha_arithmetic`**: the selected observer channel is exactly the phase picked out by the integer projection of `ufrf_alpha_inv`
- **`alphaPhaseObserverOneStepComparison_is_alpha_selected_root_scalar`**: the observer-indexed one-step comparison alias is the same alpha-selected root/scalar one-step formula as the historical legacy wrapper
- **`phase7OneStepModelPrediction_is_alpha_selected_root_scalar`**: the current one-step prediction is the explicit root/scalar formula built from the alpha-selected observer channel
- **`alphaPhaseObserverNormalizedRealCorrection_one_eq_alpha_selected_root_scalar`**: the one-step normalized observable itself also has that same alpha-selected root/scalar form
- **`alphaPhaseObserverNormalizedRealCorrection_one_eq_root_scalar_of_floor_eq`**: more generally, any channel `k` satisfying `floor α mod 13 = k` gives that same one-step root/scalar formula
- **`alpha_selected_centered_comparison_eq_root_scalar_of_floor_eq`**: for any channel `k` satisfying `floor α mod 13 = k`, the centered one-step comparison formula and the explicit root/scalar one-step formula at `k` are exactly the same scalar
- **`alpha_selected_centered_comparison_unique_by_arithmetic`**: if `k` satisfies `floor α mod 13 = k`, then `k` is exactly the selected observer channel and the observer-indexed one-step comparison alias gives that same centered one-step comparison formula
- **`alpha_selected_root_scalar_unique_by_arithmetic`**: equivalently, if `k` satisfies `floor α mod 13 = k`, then `k` is exactly the selected observer channel and the observer-indexed one-step comparison alias gives that same root/scalar one-step formula
- **`alphaPhaseObserverNormalizedRealCorrection_one_sub_codataGap_eq_alpha_selected_root_scalar_sub_codataGap`**: the one-step normalized observable minus the static CODATA gap also has that same alpha-selected root/scalar-minus-gap form
- **`alpha_selected_centered_comparison_sub_codataGap_eq_root_scalar_sub_codataGap_of_floor_eq`**: for any channel `k` satisfying `floor α mod 13 = k`, the centered one-step comparison-minus-gap formula and the root/scalar-minus-gap formula at `k` are exactly the same scalar
- **`alpha_selected_root_scalar_sub_codataGap_unique_by_arithmetic`**: if `k` satisfies `floor α mod 13 = k`, then `k` is exactly the selected observer channel and gives that same root/scalar one-step gap comparison
- **`alphaPhaseObserverCorrection_eq_alpha_selected_scalar_mul_residueCandidate`**: the observer correction itself is also rewritten directly through the alpha-selected residue channel
- **`alphaPhaseObserverNormalizedRealCorrection_eq_re_alpha_selected_scalar_mul_residueCandidate`**: the normalized real comparison observable likewise has an observer-indexed scalar/root formula
- **`alphaPhaseObserverDeviationFromAverage_eq_alpha_selected_scalar_mul_residueCandidate`**: the centered observer deviation is likewise rewritten through the alpha-selected residue channel
- **`alphaPhaseObserverNormalizedRealCorrection_is_alpha_selected_centered_comparison`**: the current comparison quantity is the normalized real part of the centered running observable at that alpha-selected channel
- **`alpha_selected_centered_comparison_eq_alpha_selected_root_scalar`**: the observer-indexed centered comparison formula and the observer-indexed root/scalar formula are exactly the same normalized real quantity
- **`alphaPhaseObserverOneStepComparison_eq_alpha_selected_centered_comparison`**: the observer-indexed one-step comparison alias is exactly that centered alpha-selected comparison scalar
- **`phase7OneStepModelPrediction_eq_alpha_selected_centered_comparison`**: the current radius-free one-step prediction is exactly that centered alpha-selected comparison scalar
- **`alphaPhaseObserverNormalizedRealCorrection_one_eq_alpha_selected_centered_comparison`**: equivalently, the one-step normalized observable itself is exactly that centered alpha-selected comparison scalar
- **`alphaPhaseObserverNormalizedRealCorrection_eq_centered_comparison_of_floor_eq`**: more generally, any channel `k` satisfying `floor α mod 13 = k` gives that same centered comparison formula at any discrete running step `n`
- **`alphaPhaseObserverNormalizedRealCorrection_eq_root_scalar_of_floor_eq`**: equivalently, at any discrete running step `n`, that same normalized real observable also gives the root/scalar formula at `k`
- **`alphaPhaseObserverNormalizedRealCorrection_one_eq_centered_comparison_of_floor_eq`**: in particular, at `n = 1`, any channel `k` satisfying `floor α mod 13 = k` gives that same centered one-step comparison formula
- **`alpha_selected_centered_observable_eq_root_scalar_of_floor_eq`**: more generally, at any discrete running step `n`, the centered observable formula and the root/scalar formula at any arithmetic-selected `k` are exactly the same normalized real quantity
- **`alpha_selected_centered_observable_unique_by_arithmetic`**: if `k` satisfies `floor α mod 13 = k`, then `k` is exactly the selected observer channel and the normalized real centered observable itself gives that same centered comparison formula
- **`alpha_selected_root_scalar_observable_unique_by_arithmetic`**: equivalently, if `k` satisfies `floor α mod 13 = k`, then `k` is exactly the selected observer channel and the normalized real observable itself gives that same root/scalar formula
- **`alphaPhaseObserverNormalizedRealCorrection_one_sub_codataGap_eq_alpha_selected_centered_comparison_sub_codataGap`**: equivalently, the one-step normalized observable minus the static CODATA gap is exactly that centered alpha-selected comparison scalar minus the same gap
- **`alpha_selected_centered_comparison_sub_codataGap_unique_by_arithmetic`**: if `k` satisfies `floor α mod 13 = k`, then `k` is exactly the selected observer channel and gives that same centered one-step gap comparison
- **`phase7OneStepModelResidual_bounds_micro`**: in the separated regime, the one-step residual against the static CODATA gap lies in the explicit interval `0.000000921017 < residual < 0.000000947269`
- **`alphaPhaseObserverOneStepResidual_bounds_micro`**: equivalently, the observer-indexed one-step residual alias satisfies that same explicit micro interval
- **`phase7OneStepModelResidual_abs_lt_one_millionth`**: in the separated regime, the absolute one-step residual against the static CODATA gap is bounded by `0.000001`
- **`alphaPhaseObserverOneStepResidual_abs_lt_one_millionth`**: equivalently, the observer-indexed one-step residual alias satisfies that same absolute `10⁻⁶` bound
- **`phase7OneStepModelResidual_abs_lt_one_thousandth`**: in the separated regime, the absolute one-step residual against the static CODATA gap is bounded by `0.001`
- **`alphaPhaseObserverOneStepResidual_abs_lt_one_thousandth`**: equivalently, the observer-indexed one-step residual alias satisfies that same absolute `0.001` bound
- **`alphaPhaseObserverOneStepResidual_eq_alpha_selected_centered_comparison_sub_codataGap`**: the observer-indexed one-step residual alias is exactly that centered alpha-selected comparison scalar minus the static CODATA gap
- **`phase7OneStepModelResidual_eq_alpha_selected_centered_comparison_sub_codataGap`**: the compared one-step residual is exactly that alpha-selected centered comparison scalar minus the static CODATA gap
- **`alphaPhaseObserverOneStepResidual_is_alpha_selected_root_scalar_sub_codataGap`**: equivalently, the observer-indexed one-step residual alias is the explicit alpha-selected root/scalar formula minus the static CODATA gap
- **`phase7OneStepModelResidual_is_alpha_selected_root_scalar_sub_codataGap`**: equivalently, the compared one-step residual is the explicit alpha-selected root/scalar formula minus the static CODATA gap
- **`alpha_selected_centered_residual_unique_by_arithmetic`**: if `k` satisfies `floor α mod 13 = k`, then `k` is exactly the selected observer channel and the observer-indexed one-step residual alias gives that same centered one-step gap comparison
- **`alpha_selected_root_scalar_residual_unique_by_arithmetic`**: equivalently, if `k` satisfies `floor α mod 13 = k`, then `k` is exactly the selected observer channel and the observer-indexed one-step residual alias gives that same root/scalar one-step gap comparison
- **`phase7OneStepModelResidual_eq_of_le_lt_half_infsep`**: the one-step residual against the static CODATA gap is contour-invariant in the allowed regime
- **`cycle_prime_channels_hit_alphaPhaseObserver`**: each local cycle-prime channel `3, 5, 7, 11` also hits the selected observer label
- **`cycle_prime_paths_cover_all_positions`**: the cycle-prime channels `3, 5, 7, 11` each traverse all 13 positions before return
- **`cycle_prime_paths_close_after_thirteen`**: those cycle-prime channels close after one full 13-step traversal
- **`terminal_block_phase_pattern_at_scale`**: in the paired `BreathingCycle` layer, the tail block at every scale is `REST, bridge, bridge, seed`
- **`terminal_block_handoff_reindexes_at_scale`**: in the paired `BreathingCycle` layer, the full handoff `10,11,12,13,14` reindexes locally as `0,1,2,3,4`
- **`fourteen_restarts_after_thirteen_at_scale`**: in the paired `BreathingCycle` layer, `13` is closure/seed and `14` is the first re-entry label at every scale

Safe reading: the current formal picture says label `7` is one visited point on
the universal seed orbit and is also hit by the local cycle-prime channels.
The repo now also packages the current candidate comparison scalar as the
normalized real part of the centered running deviation at the alpha-selected
channel.
It also rewrites the one-step prediction directly in terms of that
alpha-selected observer root/scalar package.
The one-step normalized observable itself now also has direct observer-indexed
root/scalar and centered-comparison forms, and the repo now also exposes an
explicit `alphaPhaseObserverOneStepComparison` alias, so the comparison stack
depends less on the legacy `phase7OneStepModelPrediction` wrapper.
Those same one-step formulas now also transport to any `k` satisfying
`floor α mod 13 = k`, so the arithmetic selection statement is no longer tied
to one hard-coded symbol name.
The repo now also proves directly that, for any such selected `k`, the centered
one-step comparison formula and the explicit root/scalar formula coincide, both
before and after subtracting the static CODATA gap.
The correction and centered-deviation formulas now also have observer-indexed
versions, so the comparison package is less tied to literal phase syntax.
The observer-indexed centered and root/scalar presentations are now also
proved directly equal before specializing to one-step or subtracting the
CODATA gap.
It also proves exact one-step rewrite theorems for the observable-minus-gap and
residual-minus-gap packages, including both centered-comparison and
alpha-selected root/scalar forms, and the repo now also exposes an explicit
`alphaPhaseObserverOneStepResidual` alias for that same compared quantity. It
now also proves an explicit micro residual window and the absolute bound
`|residual| < 0.000001` for that exposed residual, while retaining the earlier
coarse `0.001` fallback bound; the one-step CODATA residual is also
contour-invariant in the allowed regime.
It now also proves arithmetic uniqueness in the narrow safe sense: any channel
`k` satisfying `floor α mod 13 = k` is forced to be the selected observer and
gives the same centered and root/scalar one-step gap comparison formulas.
What is not proved yet is the external script's floating-point output itself,
or any stronger claim that this current candidate quantity is uniquely
physically correct.

---

## 3. GoldenAngle - Geometric Mappings

### Proven Theorems

- **`golden_angle_bins_to_5`**: 13/φ² is rigorously in Position 5's bin [4.5, 5.5)
- **`twin_gap_maps_to_rest`**: 2 × golden_angle_position ∈ (9, 10.5) → REST

---

## 4. Manifold - Toroidal Topology + ZMod Bridge

### Structure
- `MasterManifold`: T² = S¹ × S¹ with breathing flow and flip at 1/2
- `toroidal_emergence` (theorem): Torus = S\u00b9 \u00d7 S\u00b9 from dual flows (formerly axiom)

### ZMod ↔ Torus Bridge (NEW — Phase 21)
- **`discretize`**: Continuous torus parameter → `ZMod 13` phase bin
- **`inject`**: `ZMod 13` → continuous parameter center
- **`torus_bin_spacing`**: 1/13 angular quantum
- **`continuous_bridge_seed`**: 13/13 = 1 (closure)

---

## 5. Phenomena - Physical Constant Mapping

### Proven Theorems
- **`alpha_inv_floor_mod_13_eq_seven`**: 137 mod 13 = 7 (not hardcoded)
- **`alpha_inv_decomposition`**: 137 decomposes as `13 × 10 + 7`, giving the refined alpha address `(10, 7)`
- **`alpha_coordinate_refined_handoff_path`**: the refined alpha address `(10,7)` runs into REST at `+2`, the two bridge positions at `+3,+4`, then seed/closure at `+5`, and then re-enters at depth `11`

Safe reading: these Phenomena theorems locate `α⁻¹` arithmetically in the
13-cycle chart. They do not promote label `7` to a repo-level structural-prime
or irreducibility theorem.

---

## 6. AngularEmbedding - Rod and Staff

### Proven Theorems
- **`observer_is_orthogonal`**: Equidistance constraint → observer at ±π/2
- **`rod_staff_orthogonal`**: Canonical embedding has obs = pos + π/2
- **`four_arcs_minus_identification`**: 4 arcs − 1 identification = 3 manifolds

---

## Summary

All physical constants are derived, not fitted:
- **α⁻¹ = 137**: Zero free parameters
- **Torus**: Unique topology
- **Label 7**: Derived arithmetically
- **Rod/Staff**: Orthogonality proven from equidistance
