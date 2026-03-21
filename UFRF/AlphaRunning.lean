import UFRF.Calculus
import UFRF.CircleIntegralBreathing
import UFRF.FineStructure
import UFRF.InverseLimit
import UFRF.Phenomena
import UFRF.Recursion
import UFRF.Simplex
import UFRF.StarPolygon

/-!
# UFRF.AlphaRunning

This module adds a narrow scale-indexed running-coupling model on top of the
existing breathing contour package.

The scope is intentionally conservative:

- it uses the specific contour theorems for `z ↦ 1 / (z^13 - 1)`,
- it uses the existing Fourier phase-shift theorem from `Calculus`,
- it keeps the output as a model observable rather than a first-principles QED
  or QCD renormalization theorem.

The core idea is:

1. contour deformation keeps the local normalized breathing contour observable
   fixed inside the separated regime,
2. the discrete derivative of the standard character is an explicit Fourier
   phase shift,
3. a scale step may therefore be modeled by multiplying that fixed contour
   observable by the fixed phase-shift factor.
-/

noncomputable section

open Complex
open UFRF.ComplexBreathing
open UFRF.Constants
open scoped BigOperators

namespace UFRF.AlphaRunning

/-- The inherited cycle length from the breathing contour package. -/
abbrev CycleLen : ℕ := UFRF.CircleIntegralBreathing.CycleLen

/--
The local breathing contour observable, normalized by `2πi`, around a circle of
radius `R` centered at `breathingRoot k`.
-/
def normalizedLocalContour (k : ZMod CycleLen) (R : ℝ) : ℂ :=
  ((2 * Real.pi * Complex.I)⁻¹) *
    (∮ z in C(breathingRoot k, R), UFRF.ResidueDefinition.breathingFunction z)

private theorem two_pi_I_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero h2 hpi) Complex.I_ne_zero

/--
Inside the separated-radius regime, the normalized local contour observable is
exactly the explicit residue candidate.
-/
theorem normalizedLocalContour_eq_residueCandidate_of_lt_half_infsep
    (k : ZMod CycleLen) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    normalizedLocalContour k R = UFRF.ResidueDefinition.residueCandidateAt k := by
  rw [normalizedLocalContour,
    UFRF.CircleIntegralBreathing.circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_of_lt_half_infsep
      (k := k) (R := R) hR hRlt]
  field_simp [two_pi_I_ne_zero]

/--
Within the same separated annulus, the normalized local contour observable is
invariant under contour deformation of the radius.
-/
theorem normalizedLocalContour_eq_of_le_lt_half_infsep
    (k : ZMod CycleLen) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    normalizedLocalContour k R = normalizedLocalContour k r := by
  unfold normalizedLocalContour
  rw [UFRF.CircleIntegralBreathing.circleIntegral_breathingFunction_eq_of_le_lt_half_infsep
    (k := k) (r := r) (R := R) hr hrR hRlt]

/--
The midpoint weight imported from the calculus layer.

We keep it as a separate definition so that the model visibly records the
existing `6.5 / 13 = 1 / 2` coherence factor from `Calculus.lean`.
-/
def midpointWeight : ℝ := 1 / 2

theorem midpointWeight_eq_coherence :
    midpointWeight = (6.5 : ℝ) / 13 := by
  simpa [midpointWeight] using coherence_at_midpoint.symm

/--
The one-step phase shift of the standard breathing character, read from the
discrete derivative at the cycle origin.
-/
def standardModePhaseShift : ℂ :=
  discrete_derivative (⇑breathingCharacter) 0

theorem standardModePhaseShift_eq_breathingCharacter_one_sub_one :
    standardModePhaseShift = breathingCharacter 1 - 1 := by
  have hshift_raw :
      discrete_derivative (⇑breathingCharacter) 0 =
        (breathingCharacter 1 - 1) * breathingCharacter 0 :=
    derivative_is_phase_shift (χ := breathingCharacter) (t := (0 : ZMod 13))
  have hshift :
      standardModePhaseShift = (breathingCharacter 1 - 1) * breathingCharacter 0 := by
    simpa [standardModePhaseShift] using hshift_raw
  calc
    standardModePhaseShift = (breathingCharacter 1 - 1) * breathingCharacter 0 := hshift
    _ = breathingCharacter 1 - 1 := by simp

theorem breathingCharacter_one_ne_one : breathingCharacter 1 ≠ 1 := by
  intro h
  have hroot : breathingRoot (1 : ZMod CycleLen) = breathingRoot 0 := by
    simpa [breathingRoot, breathingRoot_zero] using h
  have h10 : (1 : ZMod CycleLen) = 0 := breathingRoot_injective hroot
  exact one_ne_zero h10

theorem standardModePhaseShift_ne_zero : standardModePhaseShift ≠ 0 := by
  rw [standardModePhaseShift_eq_breathingCharacter_one_sub_one]
  exact sub_ne_zero.mpr breathingCharacter_one_ne_one

theorem residueCandidateAt_ne_zero (k : ZMod CycleLen) :
    UFRF.ResidueDefinition.residueCandidateAt k ≠ 0 := by
  rw [UFRF.ResidueDefinition.residueCandidateAt_eq_inverse_localFactorAt_root]
  exact inv_ne_zero (UFRF.ResidueDefinition.localFactorAt_root_ne_zero k)

/--
One discrete running increment: midpoint coherence times the Fourier phase
shift times the normalized local contour observable.
-/
def contourRunningIncrement (k : ZMod CycleLen) (R : ℝ) : ℂ :=
  (midpointWeight : ℂ) * standardModePhaseShift * normalizedLocalContour k R

/--
Inside the separated-radius regime, the running increment is explicitly
midpoint-weight times the Fourier phase shift times the residue candidate.
-/
theorem contourRunningIncrement_eq_midpoint_mul_phaseShift_mul_residueCandidate
    (k : ZMod CycleLen) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    contourRunningIncrement k R =
      (midpointWeight : ℂ) * standardModePhaseShift *
        UFRF.ResidueDefinition.residueCandidateAt k := by
  rw [contourRunningIncrement,
    normalizedLocalContour_eq_residueCandidate_of_lt_half_infsep (k := k) (R := R) hR hRlt]

/--
The running increment is invariant under contour deformation of the local
radius inside the separated annulus.
-/
theorem contourRunningIncrement_eq_of_le_lt_half_infsep
    (k : ZMod CycleLen) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    contourRunningIncrement k R = contourRunningIncrement k r := by
  rw [contourRunningIncrement,
    normalizedLocalContour_eq_of_le_lt_half_infsep (k := k) (r := r) (R := R) hr hrR hRlt,
    contourRunningIncrement]

theorem contourRunningIncrement_ne_zero_of_lt_half_infsep
    (k : ZMod CycleLen) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    contourRunningIncrement k R ≠ 0 := by
  rw [contourRunningIncrement_eq_midpoint_mul_phaseShift_mul_residueCandidate
    (k := k) (R := R) hR hRlt]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num [midpointWeight]) standardModePhaseShift_ne_zero)
    (residueCandidateAt_ne_zero k)

/--
Across the full breathing-root family, the normalized local contour observable
still sums to zero.

This is the residue package's global cancellation theorem rewritten in the
normalized contour language.
-/
theorem sum_normalizedLocalContour_allRoots_eq_zero
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (∑ k : ZMod CycleLen, normalizedLocalContour k R) = 0 := by
  rw [show (∑ k : ZMod CycleLen, normalizedLocalContour k R) =
      Finset.sum Finset.univ (fun k : ZMod CycleLen => normalizedLocalContour k R) by rfl]
  simp_rw [normalizedLocalContour_eq_residueCandidate_of_lt_half_infsep
    (R := R) (hR := hR) (hRlt := hRlt)]
  exact UFRF.ResidueDefinition.total_residue_candidate_zero

/--
Across the full breathing-root family, the contour running increment sums to
zero.

This is the projection-law statement in residue language: the full contour
family is globally conserved, and only observer-local projections survive.
-/
theorem sum_contourRunningIncrement_allRoots_eq_zero
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (∑ k : ZMod CycleLen, contourRunningIncrement k R) = 0 := by
  rw [show (∑ k : ZMod CycleLen, contourRunningIncrement k R) =
      Finset.sum Finset.univ (fun k : ZMod CycleLen => contourRunningIncrement k R) by rfl]
  simp_rw [contourRunningIncrement_eq_midpoint_mul_phaseShift_mul_residueCandidate
    (R := R) (hR := hR) (hRlt := hRlt)]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [UFRF.ResidueDefinition.total_residue_candidate_zero]
  simp

/--
The scale-indexed inverse-coupling model anchored at the static UFRF candidate.
-/
def alphaInvRunningModel (n : ℤ) (k : ZMod CycleLen) (R : ℝ) : ℂ :=
  (ufrf_alpha_inv : ℂ) + (n : ℂ) * contourRunningIncrement k R

/--
The physics observer channel selected by the existing phase-addressing layer:
the fine-structure phenomenon lives at phase `7`.
-/
def alphaPhaseObserver : ZMod CycleLen := UFRF.Phenomena.alpha_coordinate_refined.phase

theorem alphaPhaseObserver_eq_phase7 :
    alphaPhaseObserver = (7 : ZMod CycleLen) := rfl

/--
The selected observer channel is exactly the phase picked out by the integer
projection of the static UFRF inverse fine-structure value.

This is the safe arithmetic-selection statement for the current layer: phase
`7` is not chosen ad hoc, but inherited from `Phenomena.alpha_inv_projects_to_phase_7`.
-/
theorem alphaPhaseObserver_selected_by_alpha_arithmetic :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver := by
  rw [alphaPhaseObserver_eq_phase7]
  exact UFRF.Phenomena.alpha_inv_projects_to_phase_7

/--
The selected phase-7 observer reaches the terminal handoff in fixed unit
steps on the 13-cycle.

This packages the cycle-side selection story as:
- `+2` lands at REST,
- `+3,+4` land in the nested bridge strip,
- `+5` lands at the seed/closure point,
- `+6` lands at the restarted cycle point.
-/
theorem alphaPhaseObserver_enters_terminal_handoff_in_fixed_steps :
    alphaPhaseObserver + 2 = (9 : ZMod CycleLen) ∧
    alphaPhaseObserver + 3 = (10 : ZMod CycleLen) ∧
    alphaPhaseObserver + 4 = (11 : ZMod CycleLen) ∧
    alphaPhaseObserver + 5 = (12 : ZMod CycleLen) ∧
    alphaPhaseObserver + 6 = (0 : ZMod CycleLen) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [alphaPhaseObserver_eq_phase7] <;> decide

/--
The selected phase-7 observer is a point on the universal seed orbit, not a
separate absolute origin.

The same `0 -> 1 -> 2 -> ...` successor law that generates the whole cycle
from the seed reaches the observer after seven unit steps.
-/
theorem alphaPhaseObserver_is_seven_steps_on_seed_orbit :
    ((fun x : BreathingCycle.CyclePos => BreathingCycle.neg (BreathingCycle.comp x))^[7]) 0 =
      (7 : BreathingCycle.CyclePos) := by
  exact BreathingCycle.prism_step_iterate_from_zero 7

/--
The local observer correction is the deviation of the selected phase-7 channel
from the static UFRF inverse fine-structure value.
-/
def alphaPhaseObserverCorrection (n : ℤ) (R : ℝ) : ℂ :=
  alphaInvRunningModel n alphaPhaseObserver R - ufrf_alpha_inv

theorem alphaPhaseObserverCorrection_eq
    (n : ℤ) (R : ℝ) :
    alphaPhaseObserverCorrection n R = (n : ℂ) * contourRunningIncrement alphaPhaseObserver R := by
  simp [alphaPhaseObserverCorrection, alphaInvRunningModel]

theorem alphaPhaseObserverCorrection_eq_phase7
    (n : ℤ) (R : ℝ) :
    alphaPhaseObserverCorrection n R = (n : ℂ) * contourRunningIncrement (7 : ZMod CycleLen) R := by
  rw [alphaPhaseObserverCorrection_eq, alphaPhaseObserver_eq_phase7]

theorem alphaPhaseObserverCorrection_eq_phase7_scalar_mul_residueCandidate
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverCorrection n R =
      ((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
        UFRF.ResidueDefinition.residueCandidateAt (7 : ZMod CycleLen) := by
  rw [alphaPhaseObserverCorrection_eq_phase7,
    contourRunningIncrement_eq_midpoint_mul_phaseShift_mul_residueCandidate
      (k := (7 : ZMod CycleLen)) (R := R) hR hRlt]
  simp [mul_assoc]

theorem alphaPhaseObserverCorrection_eq_alpha_selected_scalar_mul_residueCandidate
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverCorrection n R =
      ((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
        UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver := by
  rw [alphaPhaseObserver_eq_phase7]
  exact alphaPhaseObserverCorrection_eq_phase7_scalar_mul_residueCandidate
    (n := n) (R := R) hR hRlt

/--
A real-valued observable extracted from the selected phase-7 observer
correction.
-/
def alphaPhaseObserverRealCorrection (n : ℤ) (R : ℝ) : ℝ :=
  Complex.re (alphaPhaseObserverCorrection n R)

/--
Model normalization for the phase-7 comparison observable.

This packages the existing simplex boundary factor `4` together with the
selected phase label `7` into the explicit scalar used by the external
phase-7 check.
-/
def alphaPhaseObserverModelNormalization : ℝ :=
  (simplex3_boundary_face_count : ℝ) * 7

theorem alphaPhaseObserverModelNormalization_eq_twenty_eight :
    alphaPhaseObserverModelNormalization = 28 := by
  unfold alphaPhaseObserverModelNormalization simplex3_boundary_face_count
  norm_num [simplex3_face_count]

/--
Normalized real-valued phase-7 correction used for model comparison.
-/
def alphaPhaseObserverNormalizedRealCorrection (n : ℤ) (R : ℝ) : ℝ :=
  alphaPhaseObserverRealCorrection n R / alphaPhaseObserverModelNormalization

/--
Fixed one-step phase-7 model prediction, expressed without a radius parameter.

This is the explicit real scalar extracted from the selected phase-7 residue
channel after one running step and the current model normalization.
-/
def phase7OneStepModelPrediction : ℝ :=
  Complex.re
    (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
      UFRF.ResidueDefinition.residueCandidateAt (7 : ZMod CycleLen)) /
    alphaPhaseObserverModelNormalization

theorem phase7OneStepModelPrediction_is_alpha_selected_root_scalar :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    phase7OneStepModelPrediction =
      Complex.re
        (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver) /
        alphaPhaseObserverModelNormalization := by
  refine ⟨alphaPhaseObserver_selected_by_alpha_arithmetic, ?_⟩
  rw [phase7OneStepModelPrediction, alphaPhaseObserver_eq_phase7]

/--
The static UFRF-to-CODATA 2022 gap used for comparison.
-/
def alphaCodata2022Gap : ℝ :=
  ufrf_alpha_inv - codata_alpha_inv

/--
Exact residual between the one-step normalized phase-7 model prediction and the
static CODATA 2022 gap.
-/
def phase7OneStepModelResidual (R : ℝ) : ℝ :=
  alphaPhaseObserverNormalizedRealCorrection 1 R - alphaCodata2022Gap

theorem alphaPhaseObserverRealCorrection_eq_re_phase7_scalar_mul_residueCandidate
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverRealCorrection n R =
      Complex.re
        (((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt (7 : ZMod CycleLen)) := by
  rw [alphaPhaseObserverRealCorrection,
    alphaPhaseObserverCorrection_eq_phase7_scalar_mul_residueCandidate
      (n := n) (R := R) hR hRlt]

theorem alphaPhaseObserverRealCorrection_eq_re_alpha_selected_scalar_mul_residueCandidate
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverRealCorrection n R =
      Complex.re
        (((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver) := by
  rw [alphaPhaseObserver_eq_phase7]
  exact alphaPhaseObserverRealCorrection_eq_re_phase7_scalar_mul_residueCandidate
    (n := n) (R := R) hR hRlt

theorem alphaPhaseObserverNormalizedRealCorrection_eq_re_phase7_scalar_mul_residueCandidate
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverNormalizedRealCorrection n R =
      Complex.re
        (((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt (7 : ZMod CycleLen)) /
        alphaPhaseObserverModelNormalization := by
  rw [alphaPhaseObserverNormalizedRealCorrection,
    alphaPhaseObserverRealCorrection_eq_re_phase7_scalar_mul_residueCandidate
      (n := n) (R := R) hR hRlt]

theorem alphaPhaseObserverNormalizedRealCorrection_eq_re_alpha_selected_scalar_mul_residueCandidate
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverNormalizedRealCorrection n R =
      Complex.re
        (((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver) /
        alphaPhaseObserverModelNormalization := by
  rw [alphaPhaseObserver_eq_phase7]
  exact alphaPhaseObserverNormalizedRealCorrection_eq_re_phase7_scalar_mul_residueCandidate
    (n := n) (R := R) hR hRlt

theorem alphaPhaseObserverNormalizedRealCorrection_eq_realCorrection_div_twenty_eight
    (n : ℤ) (R : ℝ) :
    alphaPhaseObserverNormalizedRealCorrection n R =
      alphaPhaseObserverRealCorrection n R / 28 := by
  rw [alphaPhaseObserverNormalizedRealCorrection,
    alphaPhaseObserverModelNormalization_eq_twenty_eight]

theorem alphaPhaseObserverNormalizedRealCorrection_one_eq_modelPrediction
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverNormalizedRealCorrection 1 R = phase7OneStepModelPrediction := by
  rw [alphaPhaseObserverNormalizedRealCorrection_eq_re_phase7_scalar_mul_residueCandidate
      (n := 1) (R := R) hR hRlt,
    phase7OneStepModelPrediction]
  simp

theorem alphaPhaseObserverNormalizedRealCorrection_one_eq_alpha_selected_root_scalar
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection 1 R =
      Complex.re
        (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver) /
        alphaPhaseObserverModelNormalization := by
  rcases phase7OneStepModelPrediction_is_alpha_selected_root_scalar with ⟨hsel, hpred⟩
  refine ⟨hsel, ?_⟩
  rw [alphaPhaseObserverNormalizedRealCorrection_one_eq_modelPrediction
      (R := R) hR hRlt, hpred]

theorem phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    phase7OneStepModelResidual R =
      phase7OneStepModelPrediction - alphaCodata2022Gap := by
  rw [phase7OneStepModelResidual,
    alphaPhaseObserverNormalizedRealCorrection_one_eq_modelPrediction
      (R := R) hR hRlt]

theorem alphaPhaseObserverCorrection_eq_of_le_lt_half_infsep
    (n : ℤ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverCorrection n R = alphaPhaseObserverCorrection n r := by
  rw [alphaPhaseObserverCorrection_eq_phase7, alphaPhaseObserverCorrection_eq_phase7,
    contourRunningIncrement_eq_of_le_lt_half_infsep
      (k := (7 : ZMod CycleLen)) (r := r) (R := R) hr hrR hRlt]

theorem alphaPhaseObserverRealCorrection_eq_of_le_lt_half_infsep
    (n : ℤ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverRealCorrection n R = alphaPhaseObserverRealCorrection n r := by
  unfold alphaPhaseObserverRealCorrection
  rw [alphaPhaseObserverCorrection_eq_of_le_lt_half_infsep
      (n := n) (r := r) (R := R) hr hrR hRlt]

theorem alphaPhaseObserverNormalizedRealCorrection_eq_of_le_lt_half_infsep
    (n : ℤ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverNormalizedRealCorrection n R =
      alphaPhaseObserverNormalizedRealCorrection n r := by
  rw [alphaPhaseObserverNormalizedRealCorrection,
    alphaPhaseObserverNormalizedRealCorrection,
    alphaPhaseObserverRealCorrection_eq_of_le_lt_half_infsep
      (n := n) (r := r) (R := R) hr hrR hRlt]

theorem phase7OneStepModelResidual_eq_of_le_lt_half_infsep
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    phase7OneStepModelResidual R = phase7OneStepModelResidual r := by
  unfold phase7OneStepModelResidual
  rw [alphaPhaseObserverNormalizedRealCorrection_eq_of_le_lt_half_infsep
      (n := 1) (r := r) (R := R) hr hrR hRlt]

theorem alphaPhaseObserverCorrection_ne_zero_of_ne_zero_of_lt_half_infsep
    {n : ℤ} (hn : n ≠ 0) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverCorrection n R ≠ 0 := by
  rw [alphaPhaseObserverCorrection_eq_phase7]
  refine mul_ne_zero ?_ (contourRunningIncrement_ne_zero_of_lt_half_infsep (k := (7 : ZMod CycleLen)) hR hRlt)
  exact_mod_cast hn

/-- Scale `0` recovers the static UFRF inverse fine-structure candidate. -/
theorem alphaInvRunningModel_zero (k : ZMod CycleLen) (R : ℝ) :
    alphaInvRunningModel 0 k R = ufrf_alpha_inv := by
  simp [alphaInvRunningModel]

/--
One discrete scale step adds exactly one contour running increment.
-/
theorem alphaInvRunningModel_step (n : ℤ) (k : ZMod CycleLen) (R : ℝ) :
    alphaInvRunningModel (n + 1) k R =
      alphaInvRunningModel n k R + contourRunningIncrement k R := by
  simp [alphaInvRunningModel]
  ring

/--
Inside the separated-radius regime, the full running model is invariant under
contour deformation of the local radius.
-/
theorem alphaInvRunningModel_eq_of_le_lt_half_infsep
    (n : ℤ) (k : ZMod CycleLen) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaInvRunningModel n k R = alphaInvRunningModel n k r := by
  rw [alphaInvRunningModel, alphaInvRunningModel,
    contourRunningIncrement_eq_of_le_lt_half_infsep (k := k) (r := r) (R := R) hr hrR hRlt]

/--
Summing the scale-indexed running model over the full breathing-root family
recovers `13` copies of the static UFRF inverse fine-structure candidate.

Equivalently: the global breathing contour average is unchanged; only the local
observer projections carry the running correction.
-/
theorem sum_alphaInvRunningModel_allRoots_eq_thirteen_mul_static
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (∑ k : ZMod CycleLen, alphaInvRunningModel n k R) = (13 : ℂ) * ufrf_alpha_inv := by
  rw [show (∑ k : ZMod CycleLen, alphaInvRunningModel n k R) =
      Finset.sum Finset.univ (fun k : ZMod CycleLen => alphaInvRunningModel n k R) by rfl]
  simp_rw [alphaInvRunningModel]
  rw [Finset.sum_add_distrib]
  have hconst :
      Finset.sum Finset.univ (fun _ : ZMod CycleLen => (ufrf_alpha_inv : ℂ)) =
        (13 : ℂ) * ufrf_alpha_inv := by
    simp [UFRF.ResidueDefinition.cycleLen_eq_thirteen]
  have hzero :
      Finset.sum Finset.univ (fun k : ZMod CycleLen => (n : ℂ) * contourRunningIncrement k R) = 0 := by
    rw [← Finset.mul_sum]
    rw [show (Finset.sum Finset.univ (fun k : ZMod CycleLen => contourRunningIncrement k R)) =
        (∑ k : ZMod CycleLen, contourRunningIncrement k R) by rfl]
    rw [sum_contourRunningIncrement_allRoots_eq_zero (R := R) hR hRlt]
    simp
  rw [hconst, hzero, add_zero]

/--
After averaging over the full breathing-root family, the running model collapses
back to the static UFRF inverse fine-structure value.
-/
theorem avg_alphaInvRunningModel_allRoots_eq_static
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R) = ufrf_alpha_inv := by
  rw [sum_alphaInvRunningModel_allRoots_eq_thirteen_mul_static (n := n) (R := R) hR hRlt]
  field_simp

theorem alphaPhaseObserverDeviationFromAverage_eq
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaInvRunningModel n alphaPhaseObserver R -
      ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R) =
        alphaPhaseObserverCorrection n R := by
  rw [avg_alphaInvRunningModel_allRoots_eq_static (n := n) (R := R) hR hRlt]
  simp [alphaPhaseObserverCorrection]

theorem alphaPhaseObserverDeviationFromAverage_eq_phase7_residue_correction
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaInvRunningModel n alphaPhaseObserver R -
      ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R) =
        (n : ℂ) * contourRunningIncrement (7 : ZMod CycleLen) R := by
  rw [alphaPhaseObserverDeviationFromAverage_eq (n := n) (R := R) hR hRlt,
    alphaPhaseObserverCorrection_eq_phase7]

theorem alphaPhaseObserverDeviationFromAverage_eq_alpha_selected_residue_correction
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaInvRunningModel n alphaPhaseObserver R -
      ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R) =
        (n : ℂ) * contourRunningIncrement alphaPhaseObserver R := by
  rw [alphaPhaseObserver_eq_phase7]
  exact alphaPhaseObserverDeviationFromAverage_eq_phase7_residue_correction
    (n := n) (R := R) hR hRlt

theorem alphaPhaseObserverDeviationFromAverage_eq_phase7_scalar_mul_residueCandidate
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaInvRunningModel n alphaPhaseObserver R -
      ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R) =
        ((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt (7 : ZMod CycleLen) := by
  rw [alphaPhaseObserverDeviationFromAverage_eq (n := n) (R := R) hR hRlt,
    alphaPhaseObserverCorrection_eq_phase7_scalar_mul_residueCandidate
      (n := n) (R := R) hR hRlt]

theorem alphaPhaseObserverDeviationFromAverage_eq_alpha_selected_scalar_mul_residueCandidate
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaInvRunningModel n alphaPhaseObserver R -
      ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R) =
        ((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver := by
  rw [alphaPhaseObserver_eq_phase7]
  exact alphaPhaseObserverDeviationFromAverage_eq_phase7_scalar_mul_residueCandidate
    (n := n) (R := R) hR hRlt

theorem alphaPhaseObserverRealCorrection_eq_re_deviationFromAverage
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverRealCorrection n R =
      Complex.re
        (alphaInvRunningModel n alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R)) := by
  rw [alphaPhaseObserverRealCorrection]
  congr 1
  exact (alphaPhaseObserverDeviationFromAverage_eq (n := n) (R := R) hR hRlt).symm

theorem alphaPhaseObserverNormalizedRealCorrection_eq_re_deviationFromAverage_div_twenty_eight
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverNormalizedRealCorrection n R =
      Complex.re
        (alphaInvRunningModel n alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R)) / 28 := by
  rw [alphaPhaseObserverNormalizedRealCorrection_eq_realCorrection_div_twenty_eight,
    alphaPhaseObserverRealCorrection_eq_re_deviationFromAverage
      (n := n) (R := R) hR hRlt]

/--
The current comparison quantity is the normalized real part of the centered
running observable at the alpha-selected observer channel.

This packages the present repo-supported physical-selection story without
promoting it to a uniqueness theorem: the channel is selected by the alpha
arithmetic, then centered by subtracting the global breathing-root average,
and finally normalized by the explicit model factor.
-/
theorem alphaPhaseObserverNormalizedRealCorrection_is_alpha_selected_centered_comparison
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection n R =
      Complex.re
        (alphaInvRunningModel n alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R)) /
        alphaPhaseObserverModelNormalization := by
  refine ⟨alphaPhaseObserver_selected_by_alpha_arithmetic, ?_⟩
  rw [alphaPhaseObserverNormalizedRealCorrection,
    alphaPhaseObserverRealCorrection_eq_re_deviationFromAverage
      (n := n) (R := R) hR hRlt]

theorem phase7OneStepModelPrediction_eq_alpha_selected_centered_comparison
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    phase7OneStepModelPrediction =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) /
        alphaPhaseObserverModelNormalization := by
  rcases alphaPhaseObserverNormalizedRealCorrection_is_alpha_selected_centered_comparison
      (n := 1) (R := R) hR hRlt with ⟨hsel, hcmp⟩
  refine ⟨hsel, ?_⟩
  rw [← alphaPhaseObserverNormalizedRealCorrection_one_eq_modelPrediction
      (R := R) hR hRlt, hcmp]

theorem alphaPhaseObserverNormalizedRealCorrection_one_eq_alpha_selected_centered_comparison
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection 1 R =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) /
        alphaPhaseObserverModelNormalization := by
  rcases phase7OneStepModelPrediction_eq_alpha_selected_centered_comparison
      (R := R) hR hRlt with ⟨hsel, hcmp⟩
  refine ⟨hsel, ?_⟩
  rw [alphaPhaseObserverNormalizedRealCorrection_one_eq_modelPrediction
      (R := R) hR hRlt, hcmp]

theorem alphaPhaseObserverNormalizedRealCorrection_one_eq_centered_comparison_of_floor_eq
    {k : ZMod CycleLen}
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k)
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverNormalizedRealCorrection 1 R =
      Complex.re
        (alphaInvRunningModel 1 k R -
          ((13 : ℂ)⁻¹) * (∑ j : ZMod CycleLen, alphaInvRunningModel 1 j R)) /
        alphaPhaseObserverModelNormalization := by
  have hk' : k = alphaPhaseObserver := hk.symm.trans alphaPhaseObserver_selected_by_alpha_arithmetic
  rcases alphaPhaseObserverNormalizedRealCorrection_one_eq_alpha_selected_centered_comparison
      (R := R) hR hRlt with ⟨_, hcmp⟩
  simpa [hk'] using hcmp

theorem alphaPhaseObserverNormalizedRealCorrection_one_eq_root_scalar_of_floor_eq
    {k : ZMod CycleLen}
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k)
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverNormalizedRealCorrection 1 R =
      Complex.re
        (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt k) /
        alphaPhaseObserverModelNormalization := by
  have hk' : k = alphaPhaseObserver := hk.symm.trans alphaPhaseObserver_selected_by_alpha_arithmetic
  rcases alphaPhaseObserverNormalizedRealCorrection_one_eq_alpha_selected_root_scalar
      (R := R) hR hRlt with ⟨_, hroot⟩
  simpa [hk'] using hroot

theorem alphaPhaseObserverNormalizedRealCorrection_one_sub_codataGap_eq_alpha_selected_centered_comparison_sub_codataGap
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection 1 R - alphaCodata2022Gap =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) /
        alphaPhaseObserverModelNormalization - alphaCodata2022Gap := by
  rcases alphaPhaseObserverNormalizedRealCorrection_one_eq_alpha_selected_centered_comparison
      (R := R) hR hRlt with ⟨hsel, hcmp⟩
  refine ⟨hsel, ?_⟩
  rw [hcmp]

theorem alphaPhaseObserverNormalizedRealCorrection_one_sub_codataGap_eq_alpha_selected_root_scalar_sub_codataGap
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection 1 R - alphaCodata2022Gap =
      Complex.re
        (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver) /
        alphaPhaseObserverModelNormalization - alphaCodata2022Gap := by
  rcases alphaPhaseObserverNormalizedRealCorrection_one_eq_alpha_selected_root_scalar
      (R := R) hR hRlt with ⟨hsel, hroot⟩
  refine ⟨hsel, ?_⟩
  rw [hroot]

theorem alpha_selected_centered_comparison_sub_codataGap_unique_by_arithmetic
    {k : ZMod CycleLen} {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k) :
    k = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection 1 R - alphaCodata2022Gap =
      Complex.re
        (alphaInvRunningModel 1 k R -
          ((13 : ℂ)⁻¹) * (∑ j : ZMod CycleLen, alphaInvRunningModel 1 j R)) /
        alphaPhaseObserverModelNormalization - alphaCodata2022Gap := by
  have hk' : k = alphaPhaseObserver := hk.symm.trans alphaPhaseObserver_selected_by_alpha_arithmetic
  rcases alphaPhaseObserverNormalizedRealCorrection_one_sub_codataGap_eq_alpha_selected_centered_comparison_sub_codataGap
      (R := R) hR hRlt with ⟨_, hcmp⟩
  refine ⟨hk', ?_⟩
  simpa [hk'] using hcmp

theorem alpha_selected_root_scalar_sub_codataGap_unique_by_arithmetic
    {k : ZMod CycleLen} {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k) :
    k = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection 1 R - alphaCodata2022Gap =
      Complex.re
        (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt k) /
        alphaPhaseObserverModelNormalization - alphaCodata2022Gap := by
  have hk' : k = alphaPhaseObserver := hk.symm.trans alphaPhaseObserver_selected_by_alpha_arithmetic
  rcases alphaPhaseObserverNormalizedRealCorrection_one_sub_codataGap_eq_alpha_selected_root_scalar_sub_codataGap
      (R := R) hR hRlt with ⟨_, hroot⟩
  refine ⟨hk', ?_⟩
  simpa [hk'] using hroot

theorem phase7OneStepModelResidual_eq_alpha_selected_centered_comparison_sub_codataGap
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    phase7OneStepModelResidual R =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) /
        alphaPhaseObserverModelNormalization - alphaCodata2022Gap := by
  rcases alphaPhaseObserverNormalizedRealCorrection_one_sub_codataGap_eq_alpha_selected_centered_comparison_sub_codataGap
      (R := R) hR hRlt with ⟨hsel, hpred⟩
  refine ⟨hsel, ?_⟩
  rw [phase7OneStepModelResidual, hpred]

theorem phase7OneStepModelResidual_is_alpha_selected_root_scalar_sub_codataGap
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    phase7OneStepModelResidual R =
      Complex.re
        (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver) /
        alphaPhaseObserverModelNormalization - alphaCodata2022Gap := by
  rcases alphaPhaseObserverNormalizedRealCorrection_one_sub_codataGap_eq_alpha_selected_root_scalar_sub_codataGap
      (R := R) hR hRlt with ⟨hsel, hpred⟩
  refine ⟨hsel, ?_⟩
  rw [phase7OneStepModelResidual, hpred]

/--
There is no terminal scale for the running/projection picture: the recursive
descent never stops.
-/
theorem no_terminal_scale_for_alpha_running (s : Scale) :
    ∃ s' : Scale, s' < s :=
  no_first_step s

/--
For every prime `p`, the all-scale projection tower is coherent.

This is the concurrency statement behind the local residue channel: every prime
starts the same never-stopping projection story across all finite depths.
-/
theorem prime_tower_is_coherent
    (p : ℕ) [Fact (Nat.Prime p)] (x : ℤ_[p]) :
    IsCoherent p (fun n => PadicInt.toZModPow n x) :=
  padic_is_coherent p x

/--
For every prime `p`, the projection tower starts with unity at depth `1` and
then resolves each coarse point into exactly `p` positions at the next depth.

This is the formal version of the user-facing pattern "0 to 1, then 1 to p,
forever" in the prime tower.
-/
theorem prime_start_pattern
    (p : ℕ) [Fact (Nat.Prime p)] :
    UFRF.Padic.universal_projection p (1 : ℤ_[p]) = (1 : ZMod p) ∧
    Fintype.card (ZMod (p ^ 2)) / Fintype.card (ZMod p) = p := by
  constructor
  · exact UFRF.Padic.universal_unity (p := p)
  · have hp : Nat.Prime p := Fact.out
    haveI : NeZero p := ⟨hp.ne_zero⟩
    exact resolution_multiplicity_universal p

/--
Specialized to the UFRF position, the same start pattern is exactly
`1` at depth `13` and `13` subpositions at the next depth.
-/
theorem ufrf_start_pattern :
    UFRF.Padic.ufrf_projection (1 : ℤ_[13]) = (1 : ZMod 13) ∧
    Fintype.card (ZMod (13 ^ 2)) / Fintype.card (ZMod 13) = 13 := by
  constructor
  · change UFRF.Padic.universal_projection 13 (1 : ℤ_[13]) = (1 : ZMod 13)
    exact UFRF.Padic.universal_unity (p := 13)
  · exact resolution_multiplicity_universal 13

/--
The smallest breathing step really is `0 -> 1`.

This is the cycle-side seed statement that pairs with the tower-side
`1 -> p` start pattern.
-/
theorem cycle_seed_zero_to_one :
    BreathingCycle.neg (BreathingCycle.comp 0) = (1 : BreathingCycle.CyclePos) :=
  BreathingCycle.prism_generates_from_zero

private abbrev CyclePrime3VisitOrder : Prop :=
  (0 * 3 : ZMod 13) = 0 ∧ (1 * 3 : ZMod 13) = 3 ∧
    (2 * 3 : ZMod 13) = 6 ∧ (3 * 3 : ZMod 13) = 9 ∧
    (4 * 3 : ZMod 13) = 12 ∧ (5 * 3 : ZMod 13) = 2 ∧
    (6 * 3 : ZMod 13) = 5 ∧ (7 * 3 : ZMod 13) = 8 ∧
    (8 * 3 : ZMod 13) = 11 ∧ (9 * 3 : ZMod 13) = 1 ∧
    (10 * 3 : ZMod 13) = 4 ∧ (11 * 3 : ZMod 13) = 7 ∧
    (12 * 3 : ZMod 13) = 10

private abbrev CyclePrime5VisitOrder : Prop :=
  (0 * 5 : ZMod 13) = 0 ∧ (1 * 5 : ZMod 13) = 5 ∧
    (2 * 5 : ZMod 13) = 10 ∧ (3 * 5 : ZMod 13) = 2 ∧
    (4 * 5 : ZMod 13) = 7 ∧ (5 * 5 : ZMod 13) = 12 ∧
    (6 * 5 : ZMod 13) = 4 ∧ (7 * 5 : ZMod 13) = 9 ∧
    (8 * 5 : ZMod 13) = 1 ∧ (9 * 5 : ZMod 13) = 6 ∧
    (10 * 5 : ZMod 13) = 11 ∧ (11 * 5 : ZMod 13) = 3 ∧
    (12 * 5 : ZMod 13) = 8

private abbrev CyclePrime7VisitOrder : Prop :=
  (0 * 7 : ZMod 13) = 0 ∧ (1 * 7 : ZMod 13) = 7 ∧
    (2 * 7 : ZMod 13) = 1 ∧ (3 * 7 : ZMod 13) = 8 ∧
    (4 * 7 : ZMod 13) = 2 ∧ (5 * 7 : ZMod 13) = 9 ∧
    (6 * 7 : ZMod 13) = 3 ∧ (7 * 7 : ZMod 13) = 10 ∧
    (8 * 7 : ZMod 13) = 4 ∧ (9 * 7 : ZMod 13) = 11 ∧
    (10 * 7 : ZMod 13) = 5 ∧ (11 * 7 : ZMod 13) = 12 ∧
    (12 * 7 : ZMod 13) = 6

private abbrev CyclePrime11VisitOrder : Prop :=
  (0 * 11 : ZMod 13) = 0 ∧ (1 * 11 : ZMod 13) = 11 ∧
    (2 * 11 : ZMod 13) = 9 ∧ (3 * 11 : ZMod 13) = 7 ∧
    (4 * 11 : ZMod 13) = 5 ∧ (5 * 11 : ZMod 13) = 3 ∧
    (6 * 11 : ZMod 13) = 1 ∧ (7 * 11 : ZMod 13) = 12 ∧
    (8 * 11 : ZMod 13) = 10 ∧ (9 * 11 : ZMod 13) = 8 ∧
    (10 * 11 : ZMod 13) = 6 ∧ (11 * 11 : ZMod 13) = 4 ∧
    (12 * 11 : ZMod 13) = 2

private abbrev CyclePrimePathsCloseAfterThirteen : Prop :=
  (13 * 3 : ZMod 13) = 0 ∧ (13 * 5 : ZMod 13) = 0 ∧
    (13 * 7 : ZMod 13) = 0 ∧ (13 * 11 : ZMod 13) = 0

/--
Each cycle prime determines a full 13-position visit order on the breathing
cycle before returning to the seed.

This keeps the universal prime-tower start pattern separate from the local
13-cycle concurrency statement.
-/
theorem cycle_prime_paths_cover_all_positions :
    CyclePrime3VisitOrder ∧
    CyclePrime5VisitOrder ∧
    CyclePrime7VisitOrder ∧
    CyclePrime11VisitOrder := by
  exact ⟨UFRF.StarPolygon.visit_order_3, UFRF.StarPolygon.visit_order_5,
    UFRF.StarPolygon.visit_order_7, UFRF.StarPolygon.visit_order_11⟩

/--
Every local cycle-prime channel hits the selected phase-7 observer.

This is the local concurrency statement specialized to the alpha observer:
phase `7` is not exclusive to the `7`-channel, but a shared position visited by
all four cycle-prime paths.
-/
theorem cycle_prime_channels_hit_alphaPhaseObserver :
    ∃ n3 n5 n7 n11 : ℕ,
      (n3 * 3 : ZMod 13) = alphaPhaseObserver ∧
      (n5 * 5 : ZMod 13) = alphaPhaseObserver ∧
      (n7 * 7 : ZMod 13) = alphaPhaseObserver ∧
      (n11 * 11 : ZMod 13) = alphaPhaseObserver := by
  refine ⟨11, 4, 1, 3, ?_, ?_, ?_, ?_⟩ <;>
    rw [alphaPhaseObserver_eq_phase7] <;> decide

/--
All four cycle-prime paths close after 13 steps.

Together with `cycle_prime_paths_cover_all_positions`, this records the local
concurrency picture: every cycle-prime channel traverses the full 13-position
geometry and then returns to the seed.
-/
theorem cycle_prime_paths_close_after_thirteen :
    CyclePrimePathsCloseAfterThirteen :=
  UFRF.StarPolygon.paths_all_close

end UFRF.AlphaRunning
