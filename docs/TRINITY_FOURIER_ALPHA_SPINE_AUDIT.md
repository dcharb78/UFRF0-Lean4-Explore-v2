# Trinity -> Fourier -> Alpha Spine Audit

This note is the Phase 1 output for the theorem-spine branch
`codex/physics-theorem-spine`.

Its purpose is narrower than [`docs/DERIVATION_CHAIN.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/DERIVATION_CHAIN.md).
That file is a useful broad dependency map. This file is stricter:

- it names the exact theorem-carrying steps that currently bear the
  Trinity -> Fourier -> alpha lane,
- it marks which links are already load-bearing in Lean,
- it marks which links are still conceptual or packaging-level rather than
  uniquely forced,
- it identifies the smallest honest next theorem targets.

## Scope

This audit is only about the current lane:

- Trinity and cycle structure
- Fourier phase-shift bridge
- arithmetic alpha selection
- static alpha/CODATA package
- exposed `AlphaRunning` prediction/gap/residual/error package

It is not a global claim about every module in the repo.

## Canonical Load-Bearing Spine

### 1. Trinity Seed

Current theorem carriers:

- [UFRF/Trinity.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Trinity.lean#L58) `trinity_symmetry`
- [UFRF/Trinity.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Trinity.lean#L74) `trinity_uniqueness`
- [UFRF/Trinity.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Trinity.lean#L93) `trinity_is_minimal_two`
- [UFRF/Constants.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Constants.lean#L80) `trinity_range_is_one`

What this actually gives:

- the symmetric conserved triple is fixed up to scaling
- the midpoint/observer structure is explicit
- the repo has a clean seed object for later cycle and addressing layers

### 2. From Balance To 13

Current theorem carriers:

- [UFRF/Structure13.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Structure13.lean#L50) `uniqueness_of_three`
- [UFRF/Structure13.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Structure13.lean#L60) `uniqueness_of_thirteen`
- [UFRF/Foundation.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Foundation.lean#L52) `cycle_is_thirteen`
- [UFRF/Foundation.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Foundation.lean#L73) `dimensional_closure_equivalent`

What this actually gives:

- the current repo-level cycle length `13` is theorem-backed
- the arithmetic address space used downstream is not ad hoc

### 3. Cycle, Flip, And Recursion Structure

Current theorem carriers:

- [UFRF/BreathingCycle.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/BreathingCycle.lean#L554) `flip_at_half`
- [UFRF/BreathingCycle.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/BreathingCycle.lean#L611) `prism_identity`
- [UFRF/BreathingCycle.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/BreathingCycle.lean#L231) `bridge_seed_wraps`
- [UFRF/BreathingCycle.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/BreathingCycle.lean#L471) `terminal_block_closes_and_restarts_at_scale`
- [UFRF/Recursion.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Recursion.lean#L241) `prism_walk_and_terminal_handoff_at_scale`

What this actually gives:

- midpoint/flip structure
- the seed walk and recurring `13 -> 3`, `14 -> 4` handoff
- the no-bottom-scale recursive package used later by the running layer

### 4. Fourier Carrier And Phase-Shift Bridge

Current theorem carriers:

- [UFRF/Fourier.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Fourier.lean#L90) `standard_character_is_primitive`
- [UFRF/Fourier.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Fourier.lean#L105) `character_injective`
- [UFRF/Fourier.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Fourier.lean#L135) `fourier_basis_exists`
- [UFRF/Fourier.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Fourier.lean#L180) `prime_oscillator_count`
- [UFRF/Calculus.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Calculus.lean#L273) `derivative_is_phase_shift`
- [UFRF/AlphaRunning.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/AlphaRunning.lean#L106) `standardModePhaseShift_eq_breathingCharacter_one_sub_one`

What this actually gives:

- a theorem-backed finite Fourier context on the 13-cycle
- an explicit discrete-derivative-to-phase-shift bridge
- the exact bridge used by `AlphaRunning` is already present; it is not just a narrative association

### 5. Alpha Polynomial And Static Arithmetic Selection

Current theorem carriers:

- [UFRF/ThreeLOG.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/ThreeLOG.lean#L175) `log3_geometric_factor_is_four`
- [UFRF/FineStructure.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/FineStructure.lean#L146) `alpha_polynomial_form`
- [UFRF/FineStructure.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/FineStructure.lean#L63) `alpha_inv_floor_137`
- [UFRF/FineStructure.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/FineStructure.lean#L976) `alpha_inv_bounds_d27`
- [UFRF/Phenomena.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Phenomena.lean#L54) `alpha_inv_floor_mod_13_eq_seven`
- [UFRF/Phenomena.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Phenomena.lean#L108) `alpha_inv_decomposition`

What this actually gives:

- the current static alpha candidate is explicit and numerically strong
- the arithmetic-selected label `7` is theorem-backed through the floor of the static alpha value
- the refined `(10,7)` address is also theorem-backed as arithmetic decomposition

### 6. Observer Selection And Current Measurement Lane

Current theorem carriers:

- [UFRF/AlphaRunning.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/AlphaRunning.lean#L260) `alphaPhaseObserver_selected_by_alpha_arithmetic`
- [UFRF/AlphaRunning.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/AlphaRunning.lean#L351) `alphaPhaseObserverModelNormalization_eq_twenty_eight`
- [UFRF/AlphaRunning.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/AlphaRunning.lean#L1783) `phase7OneStepModelPrediction_is_alpha_selected_root_scalar`
- [UFRF/AlphaRunning.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/AlphaRunning.lean#L1977) `alphaPhaseObserverNormalizedRealCorrection_one_eq_alpha_selected_root_scalar`
- [UFRF/AlphaRunning.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/AlphaRunning.lean#L3198) `alpha_selected_root_scalar_sub_codataGap_unique_by_arithmetic`
- [UFRF/AlphaRunning.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/AlphaRunning.lean#L1458) `phase7OneStepModelPrediction_bounds_d27`
- [UFRF/AlphaRunning.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/AlphaRunning.lean#L1875) `alphaCodata2022Gap_bounds_d27`
- [UFRF/AlphaRunning.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/AlphaRunning.lean#L2146) `phase7OneStepModelResidual_bounds_d27`
- [UFRF/AlphaRunning.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/AlphaRunning.lean#L2566) `alphaPhaseObserverResidueCheckAbsError_bounds_d27`
- [UFRF/AlphaRunning.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/AlphaRunning.lean#L3970) `alpha_selected_one_step_absolute_error_package_has_local_origin_and_recurring_handoff`

What this actually gives:

- the selected observer is theorem-backed by alpha arithmetic
- the current one-step prediction is already rewritten in alpha-selected root/scalar form
- the normalized observable is already transported onto that same selected root/scalar form
- the comparison-minus-gap formula already has a uniqueness-by-arithmetic theorem for any selected `k`
- the current exposed prediction/gap/residual/error package is all at `d27`
- the current one-step package is already tied back to the recurring-handoff structure

### 7. Structural Companion Package

Current theorem carrier:

- [UFRF/AlphaRunning.lean](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/AlphaRunning.lean#L4183) `alpha_running_three_layer_concurrency_package`

What this actually gives:

- a running-side re-export of the lower cycle/recursion concurrency package
- a nearby structural companion theorem for the measurement cluster

What it does not give:

- it is not the semantic origin of the alpha lane
- it does not by itself force the observer/measurement choice

## Already Proved Bridges Worth Freezing

- The Fourier phase shift used in the running model is already explicit and theorem-backed.
- The selected observer is already theorem-backed by the arithmetic floor of `ufrf_alpha_inv`.
- The current one-step prediction is already written as the alpha-selected root/scalar formula.
- The normalized one-step observable and the comparison-minus-gap form already transport to any arithmetic-selected `k`.
- The current exposed numeric package is already aligned at `d27`.
- The current one-step measurement lane now also has a conservative
  inherited-normalization characterization package in `AlphaRunning`.
- The start-pattern / seed-orbit lane now also has a conservative structural
  junction package back into the inherited-normalized one-step lane in
  `AlphaRunning`.
- The current public prediction wrapper now also meets that junction through
  an explicit Fourier-exposed capstone theorem in `AlphaRunning`.

These are not planning hypotheses. They are already part of the current Lean surface.

## Conceptual Links That Are Not Yet Fully Forced

- There is still no single theorem yet that packages the exact
  Trinity -> Fourier -> alpha lane end to end across modules, even though the
  AlphaRunning-side Fourier/start-pattern capstone package now exists.
- The current `/28` normalization is explicit, but it is not yet proved to be the uniquely forced normalization.
- The current physical-selection reading remains fenced; the repo does not yet prove that the current comparison observable is the uniquely correct physical-selection quantity.
- The `KissingEigen` `E×B` language currently functions as a companion
  geometric/interpretive lane, not as a theorem-level bridge into the current
  Fourier phase-shift or alpha-selection package.
- The old broad derivation map should not be read as saying every import edge is already a theorem-level semantic derivation. Some arrows are still best read as disciplined conceptual adjacency.

## Exact Missing Bridge Targets

These are the smallest honest missing theorem families for this branch.

### A. A Canonical Spine Package

Target shape:

- one theorem or one narrow theorem family that explicitly packages
  Trinity/cycle/Fourier/arithmetic-selection/current-alpha-lane together
- build above the now-existing start-pattern / seed-orbit / inherited-
  measurement junction package rather than re-proving that local bridge again

Reason:

- this would turn the current dispersed evidence into one exact theorem surface
  without widening claims

### B. A Forced-Selection / Forced-Normalization Theorem

Target shape:

- implemented first entry target:
  `alphaPhaseObserverModelNormalization_inherits_simplex_boundary_and_selected_label`
- this local theorem now shows that the current normalization inherits the
  simplex boundary factor together with the arithmetic-selected observer label,
  rather than appearing only as a raw `/ 28`
- one conservative characterization package also now exists:
  `alpha_selected_one_step_measurement_characterization_has_inherited_normalization_radius_invariance_and_recurring_handoff`
- after that, if still needed, one characterization theorem in
  `UFRF/AlphaRunning.lean` showing that the current
  observer/observable/normalization lane is determined, or tightly
  constrained, by a small explicit property bundle already present in the repo

Candidate ingredients:

- arithmetic selection
- centered observable structure
- root/scalar compatibility
- allowed-radius invariance
- recurring-handoff compatibility
- static CODATA comparison compatibility

Reason:

- this is the main remaining gap between a coherent model lane and a more
  mathematically forced lane
- the local normalization-inheritance theorem is the smallest honest move
  because it partially forces the current measurement rule without promoting
  it into a unique physical-selection theorem

### C. A Conservative Theorem About What Is Still Open

Target shape:

- a doc or theorem-adjacent note that explicitly marks the current open gap as
  unique normalization / stronger physical-selection, not “more decimals”

Reason:

- this keeps the branch from drifting back into precision-only work

## What Not To Spend Time On Next

- more prediction-only wrappers
- another pass on static decimal tightening before the characterization gap moves
- a generic residue abstraction
- rhetoric that turns the current observer-local package into a settled physical-selection theorem

## Interpretation Fence

For this branch, the following sentence should remain the practical guardrail:

The repo already proves a strong Trinity -> cycle -> Fourier -> alpha-facing
mathematical lane, but it does not yet prove that the current `/28`
normalization and the broader physical-selection reading are uniquely forced.
