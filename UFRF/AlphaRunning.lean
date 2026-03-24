import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
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

theorem norm_standardModePhaseShift_le_two_pi_div_thirteen :
    ‖standardModePhaseShift‖ ≤ 2 * Real.pi / 13 := by
  rw [standardModePhaseShift_eq_breathingCharacter_one_sub_one]
  change ‖breathingRoot (1 : ZMod CycleLen) - 1‖ ≤ 2 * Real.pi / 13
  rw [breathingRoot_eq_exp (1 : ZMod CycleLen)]
  have hone : (((1 : ZMod CycleLen).val : ℂ)) = 1 := by
    letI : Fact (1 < CycleLen) := ⟨by
      norm_num [CycleLen, UFRF.CircleIntegralBreathing.CycleLen,
        UFRF.ComplexBreathing.CycleLen, FourierCycleLen,
        BreathingCycle.cycle_len, UFRF.Foundation.derived_cycle_length,
        UFRF.Foundation.trinity_dimension, UFRF.Structure13.projective_order]⟩
    exact_mod_cast (ZMod.val_one CycleLen)
  rw [hone]
  have harg :
      2 * Real.pi * Complex.I * (1 : ℂ) / CycleLen =
        Complex.I * ((2 * Real.pi / 13 : ℝ) : ℂ) := by
    simp [UFRF.ResidueDefinition.cycleLen_eq_thirteen, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm]
  rw [harg]
  have hnonneg : 0 ≤ 2 * Real.pi / 13 := by positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg Real.pi_pos.le] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi / 13))

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

This is the global cancellation statement for the running increments in the
current residue-driven model.
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
The observer channel selected by the existing arithmetic-addressing layer:
the fine-structure floor reduces to label `7` modulo `13`.
-/
def alphaPhaseObserver : ZMod CycleLen := UFRF.Phenomena.alpha_coordinate_refined.phase

theorem alphaPhaseObserver_eq_seven :
    alphaPhaseObserver = (7 : ZMod CycleLen) := rfl

/--
The selected observer channel is exactly the phase picked out by the integer
projection of the static UFRF inverse fine-structure value.

This is the safe arithmetic-selection statement for the current layer: phase
`7` is not chosen ad hoc, but inherited from
`Phenomena.alpha_inv_floor_mod_13_eq_seven`.
-/
theorem alphaPhaseObserver_selected_by_alpha_arithmetic :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver := by
  rw [alphaPhaseObserver_eq_seven]
  exact UFRF.Phenomena.alpha_inv_floor_mod_13_eq_seven

/--
The selected observer channel reaches the terminal handoff in fixed unit
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
    rw [alphaPhaseObserver_eq_seven] <;> decide

/--
The selected observer label is a point on the universal seed orbit, not a
separate absolute origin.

The same `0 -> 1 -> 2 -> ...` successor law that generates the whole cycle
from the seed reaches the observer after seven unit steps.
-/
theorem alphaPhaseObserver_is_seven_steps_on_seed_orbit :
    ((fun x : BreathingCycle.CyclePos => BreathingCycle.neg (BreathingCycle.comp x))^[7]) 0 =
      (7 : BreathingCycle.CyclePos) := by
  exact BreathingCycle.prism_step_iterate_from_zero 7

/--
The local observer correction is the deviation of the selected observer channel
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
  rw [alphaPhaseObserverCorrection_eq, alphaPhaseObserver_eq_seven]

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
  rw [alphaPhaseObserver_eq_seven]
  exact alphaPhaseObserverCorrection_eq_phase7_scalar_mul_residueCandidate
    (n := n) (R := R) hR hRlt

/--
A real-valued observable extracted from the selected observer
correction.
-/
def alphaPhaseObserverRealCorrection (n : ℤ) (R : ℝ) : ℝ :=
  Complex.re (alphaPhaseObserverCorrection n R)

/--
Model normalization for the selected-observer comparison observable.

This packages the existing simplex boundary factor `4` together with the
selected label `7` into the explicit scalar used by the external
legacy one-step check.
-/
def alphaPhaseObserverModelNormalization : ℝ :=
  (simplex3_boundary_face_count : ℝ) * 7

theorem alphaPhaseObserverModelNormalization_eq_twenty_eight :
    alphaPhaseObserverModelNormalization = 28 := by
  unfold alphaPhaseObserverModelNormalization simplex3_boundary_face_count
  norm_num [simplex3_face_count]

/--
Normalized real-valued selected-observer correction used for model comparison.
-/
def alphaPhaseObserverNormalizedRealCorrection (n : ℤ) (R : ℝ) : ℝ :=
  alphaPhaseObserverRealCorrection n R / alphaPhaseObserverModelNormalization

/--
Fixed one-step model prediction, expressed without a radius parameter.

This is the explicit real scalar extracted from the selected observer residue
channel after one running step and the current model normalization. The
identifier is retained as a legacy wrapper name.
-/
def phase7OneStepModelPrediction : ℝ :=
  Complex.re
    (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
      UFRF.ResidueDefinition.residueCandidateAt (7 : ZMod CycleLen)) /
    alphaPhaseObserverModelNormalization

/--
Observer-indexed name for the current one-step comparison scalar.

This is definitionally the same quantity as the historical
`phase7OneStepModelPrediction` wrapper, but keeps the public surface aligned
with the arithmetic-selected observer language.
-/
def alphaPhaseObserverOneStepComparison : ℝ :=
  phase7OneStepModelPrediction

theorem phase7OneStepModelPrediction_eq_cos_pi_div_thirteen_sub_cos_three_pi_div_thirteen :
    phase7OneStepModelPrediction =
      (Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13)) / 728 := by
  rw [phase7OneStepModelPrediction, standardModePhaseShift_eq_breathingCharacter_one_sub_one,
    UFRF.ResidueDefinition.residueCandidateAt_eq_div,
    alphaPhaseObserverModelNormalization_eq_twenty_eight]
  change Complex.re
      (((1 : ℂ) * ((midpointWeight : ℂ) * (breathingRoot (1 : ZMod CycleLen) - 1))) *
        (breathingRoot (7 : ZMod CycleLen) / CycleLen)) / 28 =
      (Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13)) / 728
  have hone : (((1 : ZMod CycleLen).val : ℂ)) = 1 := by
    letI : Fact (1 < CycleLen) := ⟨by
      norm_num [CycleLen, UFRF.CircleIntegralBreathing.CycleLen,
        UFRF.ComplexBreathing.CycleLen, FourierCycleLen,
        BreathingCycle.cycle_len, UFRF.Foundation.derived_cycle_length,
        UFRF.Foundation.trinity_dimension, UFRF.Structure13.projective_order]⟩
    exact_mod_cast (ZMod.val_one CycleLen)
  have hseven : (((7 : ZMod CycleLen).val : ℂ)) = 7 := by
    have h7lt : (7 : ℕ) < CycleLen := by
      norm_num [CycleLen, UFRF.CircleIntegralBreathing.CycleLen,
        UFRF.ComplexBreathing.CycleLen, FourierCycleLen,
        BreathingCycle.cycle_len, UFRF.Foundation.derived_cycle_length,
        UFRF.Foundation.trinity_dimension, UFRF.Structure13.projective_order]
    exact_mod_cast (ZMod.val_natCast_of_lt h7lt)
  rw [breathingRoot_eq_exp (1 : ZMod CycleLen), breathingRoot_eq_exp (7 : ZMod CycleLen),
    hone, hseven]
  have harg1 :
      2 * Real.pi * Complex.I * (1 : ℂ) / CycleLen =
        ((2 * Real.pi / 13 : ℝ) : ℂ) * Complex.I := by
    simp [UFRF.ResidueDefinition.cycleLen_eq_thirteen, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm]
  have harg7 :
      2 * Real.pi * Complex.I * (7 : ℂ) / CycleLen =
        ((14 * Real.pi / 13 : ℝ) : ℂ) * Complex.I := by
    simp [UFRF.ResidueDefinition.cycleLen_eq_thirteen, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm]
    ring
  have hcycle : ((CycleLen : ℕ) : ℂ) = 13 := by
    norm_num [CycleLen, UFRF.CircleIntegralBreathing.CycleLen,
      UFRF.ComplexBreathing.CycleLen, FourierCycleLen,
      BreathingCycle.cycle_len, UFRF.Foundation.derived_cycle_length,
      UFRF.Foundation.trinity_dimension, UFRF.Structure13.projective_order]
  rw [harg1, harg7, hcycle]
  have hmulExp :
      Complex.exp (((2 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((14 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((16 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hmain :
      (((1 : ℂ) * ((midpointWeight : ℂ) *
          (Complex.exp (((2 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) - 1))) *
        (Complex.exp (((14 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) / 13)) =
        (Complex.exp (((16 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((14 * Real.pi / 13 : ℝ) : ℂ) * Complex.I)) / 26 := by
    calc
      (((1 : ℂ) * ((midpointWeight : ℂ) *
          (Complex.exp (((2 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) - 1))) *
        (Complex.exp (((14 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) / 13)) =
          ((Complex.exp (((2 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) - 1) *
            Complex.exp (((14 * Real.pi / 13 : ℝ) : ℂ) * Complex.I)) / 26 := by
              simp [midpointWeight, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
              ring_nf
      _ =
          (Complex.exp (((2 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((14 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((14 * Real.pi / 13 : ℝ) : ℂ) * Complex.I)) / 26 := by
              ring
      _ =
          (Complex.exp (((16 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((14 * Real.pi / 13 : ℝ) : ℂ) * Complex.I)) / 26 := by
              rw [hmulExp]
  rw [hmain]
  have hcos :
      Complex.re
          ((Complex.exp (((16 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((14 * Real.pi / 13 : ℝ) : ℂ) * Complex.I)) / 26) / 28 =
        (Real.cos (16 * Real.pi / 13) - Real.cos (14 * Real.pi / 13)) / 728 := by
    rw [div_eq_mul_inv]
    have hdiv26 :
        (Complex.exp (((16 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((14 * Real.pi / 13 : ℝ) : ℂ) * Complex.I)) / 26 =
          (Complex.exp (((16 * Real.pi / 13 : ℝ) : ℂ) * Complex.I) -
              Complex.exp (((14 * Real.pi / 13 : ℝ) : ℂ) * Complex.I)) *
            (((1 / 26 : ℝ) : ℂ)) := by
      norm_num [div_eq_mul_inv]
    rw [hdiv26, Complex.re_mul_ofReal, Complex.sub_re,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re]
    ring
  rw [hcos]
  have h16 : 16 * Real.pi / 13 = 3 * Real.pi / 13 + Real.pi := by ring
  have h14 : 14 * Real.pi / 13 = Real.pi / 13 + Real.pi := by ring
  rw [h16, h14, Real.cos_add_pi, Real.cos_add_pi]
  ring

theorem phase7OneStepModelPrediction_eq_sin_sq_pi_div_thirteen_mul_cos_pi_div_thirteen :
    phase7OneStepModelPrediction =
      Real.sin (Real.pi / 13) ^ 2 * Real.cos (Real.pi / 13) / 182 := by
  rw [phase7OneStepModelPrediction_eq_cos_pi_div_thirteen_sub_cos_three_pi_div_thirteen]
  have hthree :
      Real.cos (3 * (Real.pi / 13)) =
        4 * Real.cos (Real.pi / 13) ^ 3 - 3 * Real.cos (Real.pi / 13) := by
    simpa using Real.cos_three_mul (Real.pi / 13)
  have hsq : Real.sin (Real.pi / 13) ^ 2 = 1 - Real.cos (Real.pi / 13) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 13)]
  rw [show 3 * Real.pi / 13 = 3 * (Real.pi / 13) by ring, hthree, hsq]
  ring

set_option maxHeartbeats 2000000 in
theorem phase7OneStepModelPrediction_bounds_micro :
    (0.000305520017 : ℝ) < phase7OneStepModelPrediction ∧
    phase7OneStepModelPrediction < 0.000305545269 := by
  let y : ℝ := Real.pi / 52
  have hy_eq : Real.pi / 13 = 4 * y := by
    dsimp [y]
    ring
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    positivity
  have hy_abs : |y| ≤ 1 := by
    rw [abs_of_nonneg hy_nonneg]
    dsimp [y]
    have hpi : Real.pi < 4 := Real.pi_lt_four
    nlinarith
  have hyabs_eq : |y| = y := abs_of_nonneg hy_nonneg
  have hylo : (0.0604152433 : ℝ) < y := by
    dsimp [y]
    have hpi : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
    nlinarith
  have hyhi : y < (0.0604152434 : ℝ) := by
    dsimp [y]
    have hpi : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
    nlinarith
  have hsin := Real.sin_bound (x := y) hy_abs
  have hcos := Real.cos_bound (x := y) hy_abs
  have hsin_lower :
      y - y ^ 3 / 6 - y ^ 4 * (5 / 96) ≤ Real.sin y := by
    have h := abs_sub_le_iff.mp (by simpa [hyabs_eq] using hsin)
    linarith
  have hsin_upper :
      Real.sin y ≤ y - y ^ 3 / 6 + y ^ 4 * (5 / 96) := by
    have h := abs_sub_le_iff.mp (by simpa [hyabs_eq] using hsin)
    linarith
  have hcos_lower :
      1 - y ^ 2 / 2 - y ^ 4 * (5 / 96) ≤ Real.cos y := by
    have h := abs_sub_le_iff.mp (by simpa [hyabs_eq] using hcos)
    linarith
  have hcos_upper :
      Real.cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 * (5 / 96) := by
    have h := abs_sub_le_iff.mp (by simpa [hyabs_eq] using hcos)
    linarith
  have hy2_lo : (0.0604152433 : ℝ) ^ 2 < y ^ 2 := by
    nlinarith [hylo, hy_nonneg]
  have hy2_hi : y ^ 2 < (0.0604152434 : ℝ) ^ 2 := by
    nlinarith [hyhi, hy_nonneg]
  have hy3_lo : (0.0604152433 : ℝ) ^ 3 < y ^ 3 := by
    nlinarith [hylo, hy_nonneg]
  have hy3_hi : y ^ 3 < (0.0604152434 : ℝ) ^ 3 := by
    nlinarith [hyhi, hy_nonneg]
  have hy4_hi : y ^ 4 < (0.0604152434 : ℝ) ^ 4 := by
    nlinarith [hyhi, hy_nonneg]
  have hsin_y :
      (0.0603777961 : ℝ) < Real.sin y ∧ Real.sin y < 0.06037918466 := by
    constructor
    · have hpoly :
          (0.0604152433 : ℝ) - (0.0604152434 : ℝ) ^ 3 / 6 -
              (0.0604152434 : ℝ) ^ 4 * (5 / 96) <
            Real.sin y := by
        nlinarith [hsin_lower, hylo, hy3_hi, hy4_hi]
      have hconst :
          (0.0603777961 : ℝ) <
            (0.0604152433 : ℝ) - (0.0604152434 : ℝ) ^ 3 / 6 -
              (0.0604152434 : ℝ) ^ 4 * (5 / 96) := by
        norm_num
      exact lt_trans hconst hpoly
    · have hpoly :
          Real.sin y <
            (0.0604152434 : ℝ) - (0.0604152433 : ℝ) ^ 3 / 6 +
              (0.0604152434 : ℝ) ^ 4 * (5 / 96) := by
        nlinarith [hsin_upper, hyhi, hy3_lo, hy4_hi]
      have hconst :
          (0.0604152434 : ℝ) - (0.0604152433 : ℝ) ^ 3 / 6 +
              (0.0604152434 : ℝ) ^ 4 * (5 / 96) <
            0.06037918466 := by
        norm_num
      exact lt_trans hpoly hconst
  have hcos_y :
      (0.998174305 : ℝ) < Real.cos y ∧ Real.cos y < 0.99817569307 := by
    constructor
    · have hpoly :
          1 - (0.0604152434 : ℝ) ^ 2 / 2 - (0.0604152434 : ℝ) ^ 4 * (5 / 96) <
            Real.cos y := by
        nlinarith [hcos_lower, hy2_hi, hy4_hi]
      have hconst :
          (0.998174305 : ℝ) <
            1 - (0.0604152434 : ℝ) ^ 2 / 2 - (0.0604152434 : ℝ) ^ 4 * (5 / 96) := by
        norm_num
      exact lt_trans hconst hpoly
    · have hpoly :
          Real.cos y <
            1 - (0.0604152433 : ℝ) ^ 2 / 2 + (0.0604152434 : ℝ) ^ 4 * (5 / 96) := by
        nlinarith [hcos_upper, hy2_lo, hy4_hi]
      have hconst :
          1 - (0.0604152433 : ℝ) ^ 2 / 2 + (0.0604152434 : ℝ) ^ 4 * (5 / 96) <
            0.99817569307 := by
        norm_num
      exact lt_trans hpoly hconst
  have hsin_2y :
      (0.1205351293 : ℝ) < Real.sin (2 * y) ∧
      Real.sin (2 * y) < 0.120538069 := by
    rw [Real.sin_two_mul]
    rcases hsin_y with ⟨hslo, hshi⟩
    rcases hcos_y with ⟨hclo, hchi⟩
    have hc_pos : 0 < Real.cos y := by
      nlinarith [hclo]
    have hprod_lo :
        (0.0603777961 : ℝ) * 0.998174305 < Real.sin y * Real.cos y := by
      nlinarith [hslo, hclo]
    have hprod_hi :
        Real.sin y * Real.cos y < (0.06037918466 : ℝ) * 0.99817569307 := by
      nlinarith [hshi, hchi, hc_pos]
    have hlo' :
        (2 : ℝ) * ((0.0603777961 : ℝ) * 0.998174305) <
          2 * Real.sin y * Real.cos y := by
      simpa [mul_assoc] using
        (mul_lt_mul_of_pos_left hprod_lo (show (0 : ℝ) < 2 by norm_num))
    have hhi' :
        2 * Real.sin y * Real.cos y <
          (2 : ℝ) * ((0.06037918466 : ℝ) * 0.99817569307) := by
      simpa [mul_assoc] using
        (mul_lt_mul_of_pos_left hprod_hi (show (0 : ℝ) < 2 by norm_num))
    have hlo_const :
        (0.1205351293 : ℝ) < (2 : ℝ) * ((0.0603777961 : ℝ) * 0.998174305) := by
      norm_num
    have hhi_const :
        (2 : ℝ) * ((0.06037918466 : ℝ) * 0.99817569307) < 0.120538069 := by
      norm_num
    exact ⟨lt_trans hlo_const hlo', lt_trans hhi' hhi_const⟩
  have hcos_2y :
      (0.9927038863 : ℝ) < Real.cos (2 * y) ∧
      Real.cos (2 * y) < 0.9927094285 := by
    rw [Real.cos_two_mul]
    rcases hcos_y with ⟨hclo, hchi⟩
    have hc_pos : 0 < Real.cos y := by
      nlinarith [hclo]
    have hc_nonneg : 0 ≤ Real.cos y := le_of_lt hc_pos
    have hsq_lo : (0.998174305 : ℝ) ^ 2 < Real.cos y ^ 2 := by
      nlinarith [hclo, hc_nonneg]
    have hsq_hi : Real.cos y ^ 2 < (0.99817569307 : ℝ) ^ 2 := by
      nlinarith [hchi, hc_nonneg]
    have hlo' :
        (2 : ℝ) * (0.998174305 : ℝ) ^ 2 - 1 < 2 * Real.cos y ^ 2 - 1 := by
      nlinarith [hsq_lo]
    have hhi' :
        2 * Real.cos y ^ 2 - 1 < (2 : ℝ) * (0.99817569307 : ℝ) ^ 2 - 1 := by
      nlinarith [hsq_hi]
    have hlo_const :
        (0.9927038863 : ℝ) < (2 : ℝ) * (0.998174305 : ℝ) ^ 2 - 1 := by
      norm_num
    have hhi_const :
        (2 : ℝ) * (0.99817569307 : ℝ) ^ 2 - 1 < 0.9927094285 := by
      norm_num
    exact ⟨lt_trans hlo_const hlo', lt_trans hhi' hhi_const⟩
  have hsin_4y :
      (0.2393113825 : ℝ) < Real.sin (4 * y) ∧
      Real.sin (4 * y) < 0.2393185559 := by
    rw [show 4 * y = 2 * (2 * y) by ring, Real.sin_two_mul]
    rcases hsin_2y with ⟨hslo, hshi⟩
    rcases hcos_2y with ⟨hclo, hchi⟩
    have hc_pos : 0 < Real.cos (2 * y) := by
      nlinarith [hclo]
    have hprod_lo :
        (0.1205351293 : ℝ) * 0.9927038863 <
          Real.sin (2 * y) * Real.cos (2 * y) := by
      nlinarith [hslo, hclo]
    have hprod_hi :
        Real.sin (2 * y) * Real.cos (2 * y) <
          (0.120538069 : ℝ) * 0.9927094285 := by
      nlinarith [hshi, hchi, hc_pos]
    have hlo' :
        (2 : ℝ) * ((0.1205351293 : ℝ) * 0.9927038863) <
          2 * Real.sin (2 * y) * Real.cos (2 * y) := by
      simpa [mul_assoc] using
        (mul_lt_mul_of_pos_left hprod_lo (show (0 : ℝ) < 2 by norm_num))
    have hhi' :
        2 * Real.sin (2 * y) * Real.cos (2 * y) <
          (2 : ℝ) * ((0.120538069 : ℝ) * 0.9927094285) := by
      simpa [mul_assoc] using
        (mul_lt_mul_of_pos_left hprod_hi (show (0 : ℝ) < 2 by norm_num))
    have hlo_const :
        (0.2393113825 : ℝ) <
          (2 : ℝ) * ((0.1205351293 : ℝ) * 0.9927038863) := by
      norm_num
    have hhi_const :
        (2 : ℝ) * ((0.120538069 : ℝ) * 0.9927094285) < 0.2393185559 := by
      norm_num
    exact ⟨lt_trans hlo_const hlo', lt_trans hhi' hhi_const⟩
  have hcos_4y :
      (0.9709220117 : ℝ) < Real.cos (4 * y) ∧
      Real.cos (4 * y) < 0.9709440189 := by
    rw [show 4 * y = 2 * (2 * y) by ring, Real.cos_two_mul]
    rcases hcos_2y with ⟨hclo, hchi⟩
    have hc_pos : 0 < Real.cos (2 * y) := by
      nlinarith [hclo]
    have hc_nonneg : 0 ≤ Real.cos (2 * y) := le_of_lt hc_pos
    have hsq_lo : (0.9927038863 : ℝ) ^ 2 < Real.cos (2 * y) ^ 2 := by
      nlinarith [hclo, hc_nonneg]
    have hsq_hi : Real.cos (2 * y) ^ 2 < (0.9927094285 : ℝ) ^ 2 := by
      nlinarith [hchi, hc_nonneg]
    have hlo' :
        (2 : ℝ) * (0.9927038863 : ℝ) ^ 2 - 1 < 2 * Real.cos (2 * y) ^ 2 - 1 := by
      nlinarith [hsq_lo]
    have hhi' :
        2 * Real.cos (2 * y) ^ 2 - 1 < (2 : ℝ) * (0.9927094285 : ℝ) ^ 2 - 1 := by
      nlinarith [hsq_hi]
    have hlo_const :
        (0.9709220117 : ℝ) < (2 : ℝ) * (0.9927038863 : ℝ) ^ 2 - 1 := by
      norm_num
    have hhi_const :
        (2 : ℝ) * (0.9927094285 : ℝ) ^ 2 - 1 < 0.9709440189 := by
      norm_num
    exact ⟨lt_trans hlo_const hlo', lt_trans hhi' hhi_const⟩
  rw [phase7OneStepModelPrediction_eq_sin_sq_pi_div_thirteen_mul_cos_pi_div_thirteen, hy_eq]
  rcases hsin_4y with ⟨hslo, hshi⟩
  rcases hcos_4y with ⟨hclo, hchi⟩
  have hs_pos : 0 < Real.sin (4 * y) := by
    nlinarith [hslo]
  have hc_pos : 0 < Real.cos (4 * y) := by
    nlinarith [hclo]
  have hs_nonneg : 0 ≤ Real.sin (4 * y) := le_of_lt hs_pos
  have hc_nonneg : 0 ≤ Real.cos (4 * y) := le_of_lt hc_pos
  have hsq_lo : (0.2393113825 : ℝ) ^ 2 < Real.sin (4 * y) ^ 2 := by
    nlinarith [hslo, hs_nonneg]
  have hsq_hi : Real.sin (4 * y) ^ 2 < (0.2393185559 : ℝ) ^ 2 := by
    nlinarith [hshi, hs_nonneg]
  have hprod_lo :
      (0.2393113825 : ℝ) ^ 2 * 0.9709220117 <
        Real.sin (4 * y) ^ 2 * Real.cos (4 * y) := by
    nlinarith [hsq_lo, hclo]
  have hprod_hi :
      Real.sin (4 * y) ^ 2 * Real.cos (4 * y) <
        (0.2393185559 : ℝ) ^ 2 * 0.9709440189 := by
    nlinarith [hsq_hi, hchi, hc_pos]
  have hpred_lo :
      ((0.2393113825 : ℝ) ^ 2 * 0.9709220117) / 182 <
        Real.sin (4 * y) ^ 2 * Real.cos (4 * y) / 182 := by
    exact div_lt_div_of_pos_right hprod_lo (show (0 : ℝ) < 182 by norm_num)
  have hpred_hi :
      Real.sin (4 * y) ^ 2 * Real.cos (4 * y) / 182 <
        ((0.2393185559 : ℝ) ^ 2 * 0.9709440189) / 182 := by
    exact div_lt_div_of_pos_right hprod_hi (show (0 : ℝ) < 182 by norm_num)
  have hlo_const :
      (0.000305520017 : ℝ) <
        ((0.2393113825 : ℝ) ^ 2 * 0.9709220117) / 182 := by
    norm_num
  have hhi_const :
      ((0.2393185559 : ℝ) ^ 2 * 0.9709440189) / 182 <
        0.000305545269 := by
    norm_num
  exact ⟨lt_trans hlo_const hpred_lo, lt_trans hpred_hi hhi_const⟩

theorem phase7OneStepModelPrediction_rounds_to_0_0003055 :
    |phase7OneStepModelPrediction - 0.0003055| < 0.00000005 := by
  rcases phase7OneStepModelPrediction_bounds_micro with ⟨hlo, hhi⟩
  rw [abs_lt]
  constructor <;> linarith

theorem alphaPhaseObserverOneStepComparison_rounds_to_0_0003055 :
    |alphaPhaseObserverOneStepComparison - 0.0003055| < 0.00000005 := by
  simpa [alphaPhaseObserverOneStepComparison] using
    phase7OneStepModelPrediction_rounds_to_0_0003055

theorem phase7OneStepModelPrediction_is_alpha_selected_root_scalar :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    phase7OneStepModelPrediction =
      Complex.re
        (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver) /
        alphaPhaseObserverModelNormalization := by
  refine ⟨alphaPhaseObserver_selected_by_alpha_arithmetic, ?_⟩
  rw [phase7OneStepModelPrediction, alphaPhaseObserver_eq_seven]

theorem alphaPhaseObserverOneStepComparison_is_alpha_selected_root_scalar :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverOneStepComparison =
      Complex.re
        (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver) /
        alphaPhaseObserverModelNormalization := by
  simpa [alphaPhaseObserverOneStepComparison] using
    phase7OneStepModelPrediction_is_alpha_selected_root_scalar

/--
The static UFRF-to-CODATA 2022 gap used for comparison.
-/
def alphaCodata2022Gap : ℝ :=
  ufrf_alpha_inv - codata_alpha_inv

theorem alphaCodata2022Gap_bounds_d6 :
    (0.000304598 : ℝ) < alphaCodata2022Gap ∧
    alphaCodata2022Gap < 0.000304599 := by
  rcases alpha_inv_bounds_d9 with ⟨hlo, hhi⟩
  unfold alphaCodata2022Gap codata_alpha_inv
  constructor <;> linarith

theorem alphaCodata2022Gap_bounds_d13 :
    (0.0003045988784 : ℝ) < alphaCodata2022Gap ∧
    alphaCodata2022Gap < 0.0003045988785 := by
  rcases alpha_inv_bounds_d13 with ⟨hlo, hhi⟩
  unfold alphaCodata2022Gap codata_alpha_inv
  constructor <;> linarith

theorem alphaCodata2022Gap_rounds_to_0_000304598878 :
    |alphaCodata2022Gap - 0.000304598878| < 0.0000000000005 := by
  rcases alphaCodata2022Gap_bounds_d13 with ⟨hlo, hhi⟩
  rw [abs_lt]
  constructor <;> linarith

/--
Exact residual between the one-step normalized legacy prediction wrapper and the
static CODATA 2022 gap.
-/
def phase7OneStepModelResidual (R : ℝ) : ℝ :=
  alphaPhaseObserverNormalizedRealCorrection 1 R - alphaCodata2022Gap

/--
Observer-indexed name for the current one-step comparison residual against the
static CODATA 2022 gap.

This is definitionally the same quantity as the historical
`phase7OneStepModelResidual` wrapper.
-/
def alphaPhaseObserverOneStepResidual (R : ℝ) : ℝ :=
  phase7OneStepModelResidual R

/--
Absolute error quantity checked by `scripts/alpha_phase7_residue_check.py`.

This mirrors the script's comparison between the current selected-observer
one-step comparison scalar and the static CODATA 2022 gap, while keeping the
Lean surface on the observer-indexed name.
-/
def alphaPhaseObserverResidueCheckAbsError : ℝ :=
  |alphaCodata2022Gap - alphaPhaseObserverOneStepComparison|

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
  rw [alphaPhaseObserver_eq_seven]
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
  rw [alphaPhaseObserver_eq_seven]
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

theorem alphaPhaseObserverNormalizedRealCorrection_one_eq_oneStepComparison
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverNormalizedRealCorrection 1 R = alphaPhaseObserverOneStepComparison := by
  simpa [alphaPhaseObserverOneStepComparison] using
    alphaPhaseObserverNormalizedRealCorrection_one_eq_modelPrediction
      (R := R) hR hRlt

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

theorem alphaPhaseObserverOneStepResidual_eq_oneStepComparison_sub_codataGap
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverOneStepResidual R =
      alphaPhaseObserverOneStepComparison - alphaCodata2022Gap := by
  simpa [alphaPhaseObserverOneStepResidual, alphaPhaseObserverOneStepComparison] using
    phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap
      (R := R) hR hRlt

/--
The current one-step residual against the static CODATA 2022 gap lies in a
micro-scale positive interval.

This is still a model-layer numeric theorem: it sharpens the residual estimate
without promoting a broader projection-law or physical-selection claim.
-/
theorem phase7OneStepModelResidual_bounds_micro
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.000000921017 : ℝ) < phase7OneStepModelResidual R ∧
    phase7OneStepModelResidual R < 0.000000947269 := by
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  rcases phase7OneStepModelPrediction_bounds_micro with ⟨hpred_lo, hpred_hi⟩
  rcases alphaCodata2022Gap_bounds_d6 with ⟨hgap_lo, hgap_hi⟩
  constructor <;> linarith

theorem alphaPhaseObserverOneStepResidual_bounds_micro
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.000000921017 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.000000947269 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_micro (R := R) hR hRlt

theorem phase7OneStepModelResidual_abs_lt_one_millionth
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    |phase7OneStepModelResidual R| < 0.000001 := by
  rcases phase7OneStepModelResidual_bounds_micro (R := R) hR hRlt with ⟨hlo, hhi⟩
  have hpos : 0 < phase7OneStepModelResidual R := by
    nlinarith [hlo]
  rw [abs_of_pos hpos]
  linarith

theorem alphaPhaseObserverOneStepResidual_abs_lt_one_millionth
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    |alphaPhaseObserverOneStepResidual R| < 0.000001 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_abs_lt_one_millionth (R := R) hR hRlt

theorem alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverResidueCheckAbsError =
      |alphaPhaseObserverOneStepResidual R| := by
  rw [alphaPhaseObserverResidueCheckAbsError,
    alphaPhaseObserverOneStepResidual_eq_oneStepComparison_sub_codataGap
      (R := R) hR hRlt]
  simp [abs_sub_comm]

theorem alphaPhaseObserverResidueCheckAbsError_bounds_micro :
    (0.000000921017 : ℝ) < alphaPhaseObserverResidueCheckAbsError ∧
    alphaPhaseObserverResidueCheckAbsError < 0.000000947269 := by
  let R : ℝ := ((Set.range breathingRoot : Set ℂ).infsep / 4)
  have hInfsepPos : 0 < (Set.range breathingRoot : Set ℂ).infsep :=
    UFRF.CircleIntegralBreathing.breathingRootSet_infsep_pos
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    dsimp [R]
    linarith
  rcases alphaPhaseObserverOneStepResidual_bounds_micro (R := R) hR hRlt with
    ⟨hlo, hhi⟩
  have hpos : 0 < alphaPhaseObserverOneStepResidual R := by
    linarith
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt, abs_of_pos hpos]
  exact ⟨hlo, hhi⟩

theorem alphaPhaseObserverResidueCheckAbsError_lt_one_millionth :
    alphaPhaseObserverResidueCheckAbsError < 0.000001 := by
  rcases alphaPhaseObserverResidueCheckAbsError_bounds_micro with ⟨_, hhi⟩
  linarith

theorem alphaPhaseObserverResidueCheckAbsError_rounds_to_0_0000009 :
    |alphaPhaseObserverResidueCheckAbsError - 0.0000009| < 0.00000005 := by
  rcases alphaPhaseObserverResidueCheckAbsError_bounds_micro with ⟨hlo, hhi⟩
  rw [abs_lt]
  constructor <;> linarith

/--
The current one-step residual against the static CODATA 2022 gap is bounded by
`10⁻³` in absolute value.

This is a first honest numeric theorem for the exposed comparison quantity. It
stays intentionally coarse: the repo proves a milliscale model bound, not the
much sharper external script tolerance.
-/
theorem phase7OneStepModelResidual_abs_lt_one_thousandth
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    |phase7OneStepModelResidual R| < 0.001 := by
  have hgap : |alphaCodata2022Gap| < 0.00031 := by
    simpa [alphaCodata2022Gap] using ufrf_matches_codata
  have hresidue :
      ‖UFRF.ResidueDefinition.residueCandidateAt (7 : ZMod CycleLen)‖ = 1 / 13 := by
    rw [UFRF.ResidueDefinition.residueCandidateAt_eq_div, norm_div,
      UFRF.CircleIntegralBreathing.norm_breathingRoot_eq_one]
    simp [UFRF.ResidueDefinition.cycleLen_eq_thirteen]
  have hpred_le :
      |phase7OneStepModelPrediction| ≤
        (((1 / 2 : ℝ) * (2 * Real.pi / 13) * (1 / 13)) / 28) := by
    rw [phase7OneStepModelPrediction, abs_div,
      alphaPhaseObserverModelNormalization_eq_twenty_eight]
    have hre :
        |Complex.re
            (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
              UFRF.ResidueDefinition.residueCandidateAt (7 : ZMod CycleLen))|
          ≤ (1 / 2 : ℝ) * ‖standardModePhaseShift‖ * (1 / 13) := by
      calc
        |Complex.re
            (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
              UFRF.ResidueDefinition.residueCandidateAt (7 : ZMod CycleLen))|
            ≤ ‖(((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
                UFRF.ResidueDefinition.residueCandidateAt (7 : ZMod CycleLen))‖ :=
              abs_re_le_norm _
        _ = ‖(1 : ℂ)‖ * ‖(midpointWeight : ℂ)‖ * ‖standardModePhaseShift‖ *
              ‖UFRF.ResidueDefinition.residueCandidateAt (7 : ZMod CycleLen)‖ := by
              rw [norm_mul, norm_mul, norm_mul]
              ring
        _ = (1 / 2 : ℝ) * ‖standardModePhaseShift‖ * (1 / 13) := by
              rw [hresidue]
              norm_num [midpointWeight]
    have hphase_scaled :
        (1 / 2 : ℝ) * ‖standardModePhaseShift‖ * (1 / 13) ≤
          (1 / 2 : ℝ) * (2 * Real.pi / 13) * (1 / 13) := by
      nlinarith [norm_standardModePhaseShift_le_two_pi_div_thirteen]
    have habs_twenty_eight : |(28 : ℝ)| = 28 := by norm_num
    rw [habs_twenty_eight]
    exact div_le_div_of_nonneg_right (le_trans hre hphase_scaled) (by norm_num)
  have hpred : |phase7OneStepModelPrediction| < 0.00069 := by
    have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
    exact lt_of_le_of_lt hpred_le (by nlinarith)
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  calc
    |phase7OneStepModelPrediction - alphaCodata2022Gap|
      ≤ |phase7OneStepModelPrediction| + |alphaCodata2022Gap| := by
          simpa using (abs_sub_le phase7OneStepModelPrediction (0 : ℝ) alphaCodata2022Gap)
    _ < 0.00069 + 0.00031 := add_lt_add hpred hgap
    _ = 0.001 := by norm_num

theorem alphaPhaseObserverOneStepResidual_abs_lt_one_thousandth
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    |alphaPhaseObserverOneStepResidual R| < 0.001 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_abs_lt_one_thousandth
      (R := R) hR hRlt

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

theorem alphaPhaseObserverOneStepResidual_eq_of_le_lt_half_infsep
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverOneStepResidual R = alphaPhaseObserverOneStepResidual r := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_eq_of_le_lt_half_infsep
      (r := r) (R := R) hr hrR hRlt

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
  rw [alphaPhaseObserver_eq_seven]
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
  rw [alphaPhaseObserver_eq_seven]
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

/--
The centered observer comparison and the explicit observer root/scalar formula
are the same normalized real quantity.

This is the direct bridge between the two current candidate presentations,
without adding any stronger physical-selection claim.
-/
theorem alpha_selected_centered_comparison_eq_alpha_selected_root_scalar
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    Complex.re
        (alphaInvRunningModel n alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R)) /
        alphaPhaseObserverModelNormalization =
      Complex.re
        (((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver) /
        alphaPhaseObserverModelNormalization := by
  rcases alphaPhaseObserverNormalizedRealCorrection_is_alpha_selected_centered_comparison
      (n := n) (R := R) hR hRlt with ⟨_, hcenter⟩
  calc
    Complex.re
        (alphaInvRunningModel n alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R)) /
        alphaPhaseObserverModelNormalization =
        alphaPhaseObserverNormalizedRealCorrection n R := by
          simpa using hcenter.symm
    _ =
      Complex.re
        (((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver) /
        alphaPhaseObserverModelNormalization := by
          exact alphaPhaseObserverNormalizedRealCorrection_eq_re_alpha_selected_scalar_mul_residueCandidate
            (n := n) (R := R) hR hRlt

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

theorem alphaPhaseObserverOneStepComparison_eq_alpha_selected_centered_comparison
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverOneStepComparison =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) /
        alphaPhaseObserverModelNormalization := by
  simpa [alphaPhaseObserverOneStepComparison] using
    phase7OneStepModelPrediction_eq_alpha_selected_centered_comparison
      (R := R) hR hRlt

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

theorem alphaPhaseObserverNormalizedRealCorrection_eq_centered_comparison_of_floor_eq
    {k : ZMod CycleLen} (n : ℤ)
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k)
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverNormalizedRealCorrection n R =
      Complex.re
        (alphaInvRunningModel n k R -
          ((13 : ℂ)⁻¹) * (∑ j : ZMod CycleLen, alphaInvRunningModel n j R)) /
        alphaPhaseObserverModelNormalization := by
  have hk' : k = alphaPhaseObserver := hk.symm.trans alphaPhaseObserver_selected_by_alpha_arithmetic
  rcases alphaPhaseObserverNormalizedRealCorrection_is_alpha_selected_centered_comparison
      (n := n) (R := R) hR hRlt with ⟨_, hcmp⟩
  simpa [hk'] using hcmp

theorem alphaPhaseObserverNormalizedRealCorrection_eq_root_scalar_of_floor_eq
    {k : ZMod CycleLen} (n : ℤ)
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k)
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverNormalizedRealCorrection n R =
      Complex.re
        (((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt k) /
        alphaPhaseObserverModelNormalization := by
  have hk' : k = alphaPhaseObserver := hk.symm.trans alphaPhaseObserver_selected_by_alpha_arithmetic
  simpa [hk'] using
    alphaPhaseObserverNormalizedRealCorrection_eq_re_alpha_selected_scalar_mul_residueCandidate
      (n := n) (R := R) hR hRlt

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
  simpa using alphaPhaseObserverNormalizedRealCorrection_eq_centered_comparison_of_floor_eq
    (k := k) (n := 1) hk hR hRlt

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
  simpa using alphaPhaseObserverNormalizedRealCorrection_eq_root_scalar_of_floor_eq
    (k := k) (n := 1) hk hR hRlt

theorem alpha_selected_centered_observable_eq_root_scalar_of_floor_eq
    {k : ZMod CycleLen} (n : ℤ)
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k)
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    Complex.re
      (alphaInvRunningModel n k R -
        ((13 : ℂ)⁻¹) * (∑ j : ZMod CycleLen, alphaInvRunningModel n j R)) /
      alphaPhaseObserverModelNormalization =
      Complex.re
        (((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt k) /
        alphaPhaseObserverModelNormalization := by
  calc
    Complex.re
        (alphaInvRunningModel n k R -
          ((13 : ℂ)⁻¹) * (∑ j : ZMod CycleLen, alphaInvRunningModel n j R)) /
        alphaPhaseObserverModelNormalization =
        alphaPhaseObserverNormalizedRealCorrection n R := by
          symm
          exact alphaPhaseObserverNormalizedRealCorrection_eq_centered_comparison_of_floor_eq
            (k := k) (n := n) hk hR hRlt
    _ =
      Complex.re
        (((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt k) /
        alphaPhaseObserverModelNormalization :=
      alphaPhaseObserverNormalizedRealCorrection_eq_root_scalar_of_floor_eq
        (k := k) (n := n) hk hR hRlt

/--
If a channel `k` is selected by the alpha arithmetic, then the centered
one-step comparison and the root/scalar one-step formula are the same scalar
written in two equivalent forms.
-/
theorem alpha_selected_centered_comparison_eq_root_scalar_of_floor_eq
    {k : ZMod CycleLen}
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k)
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    Complex.re
      (alphaInvRunningModel 1 k R -
        ((13 : ℂ)⁻¹) * (∑ j : ZMod CycleLen, alphaInvRunningModel 1 j R)) /
      alphaPhaseObserverModelNormalization =
      Complex.re
        (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt k) /
        alphaPhaseObserverModelNormalization := by
  simpa using alpha_selected_centered_observable_eq_root_scalar_of_floor_eq
    (k := k) (n := 1) hk hR hRlt

theorem alpha_selected_centered_observable_unique_by_arithmetic
    {k : ZMod CycleLen} (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k) :
    k = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection n R =
      Complex.re
        (alphaInvRunningModel n k R -
          ((13 : ℂ)⁻¹) * (∑ j : ZMod CycleLen, alphaInvRunningModel n j R)) /
        alphaPhaseObserverModelNormalization := by
  have hk' : k = alphaPhaseObserver := hk.symm.trans alphaPhaseObserver_selected_by_alpha_arithmetic
  refine ⟨hk', ?_⟩
  exact alphaPhaseObserverNormalizedRealCorrection_eq_centered_comparison_of_floor_eq
    (k := k) (n := n) hk hR hRlt

theorem alpha_selected_root_scalar_observable_unique_by_arithmetic
    {k : ZMod CycleLen} (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k) :
    k = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection n R =
      Complex.re
        (((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt k) /
        alphaPhaseObserverModelNormalization := by
  have hk' : k = alphaPhaseObserver := hk.symm.trans alphaPhaseObserver_selected_by_alpha_arithmetic
  refine ⟨hk', ?_⟩
  exact alphaPhaseObserverNormalizedRealCorrection_eq_root_scalar_of_floor_eq
    (k := k) (n := n) hk hR hRlt

theorem alpha_selected_centered_comparison_unique_by_arithmetic
    {k : ZMod CycleLen} {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k) :
    k = alphaPhaseObserver ∧
    alphaPhaseObserverOneStepComparison =
      Complex.re
        (alphaInvRunningModel 1 k R -
          ((13 : ℂ)⁻¹) * (∑ j : ZMod CycleLen, alphaInvRunningModel 1 j R)) /
        alphaPhaseObserverModelNormalization := by
  rcases alpha_selected_centered_observable_unique_by_arithmetic
      (k := k) (n := 1) hR hRlt hk with ⟨hk', hobs⟩
  refine ⟨hk', ?_⟩
  calc
    alphaPhaseObserverOneStepComparison = alphaPhaseObserverNormalizedRealCorrection 1 R := by
      symm
      exact alphaPhaseObserverNormalizedRealCorrection_one_eq_oneStepComparison
        (R := R) hR hRlt
    _ =
      Complex.re
        (alphaInvRunningModel 1 k R -
          ((13 : ℂ)⁻¹) * (∑ j : ZMod CycleLen, alphaInvRunningModel 1 j R)) /
        alphaPhaseObserverModelNormalization := hobs

theorem alpha_selected_root_scalar_unique_by_arithmetic
    {k : ZMod CycleLen}
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k) :
    k = alphaPhaseObserver ∧
    alphaPhaseObserverOneStepComparison =
      Complex.re
        (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt k) /
        alphaPhaseObserverModelNormalization := by
  have hk' : k = alphaPhaseObserver := hk.symm.trans alphaPhaseObserver_selected_by_alpha_arithmetic
  rcases alphaPhaseObserverOneStepComparison_is_alpha_selected_root_scalar with ⟨_, hroot⟩
  refine ⟨hk', ?_⟩
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

/--
The same selector-aware equivalence persists after subtracting the static
CODATA comparison gap.
-/
theorem alpha_selected_centered_comparison_sub_codataGap_eq_root_scalar_sub_codataGap_of_floor_eq
    {k : ZMod CycleLen}
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k)
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    Complex.re
      (alphaInvRunningModel 1 k R -
        ((13 : ℂ)⁻¹) * (∑ j : ZMod CycleLen, alphaInvRunningModel 1 j R)) /
      alphaPhaseObserverModelNormalization - alphaCodata2022Gap =
      Complex.re
        (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt k) /
        alphaPhaseObserverModelNormalization - alphaCodata2022Gap := by
  rw [alpha_selected_centered_comparison_eq_root_scalar_of_floor_eq
    (k := k) hk hR hRlt]

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

theorem alphaPhaseObserverOneStepResidual_eq_alpha_selected_centered_comparison_sub_codataGap
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverOneStepResidual R =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) /
        alphaPhaseObserverModelNormalization - alphaCodata2022Gap := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_eq_alpha_selected_centered_comparison_sub_codataGap
      (R := R) hR hRlt

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

theorem alphaPhaseObserverOneStepResidual_is_alpha_selected_root_scalar_sub_codataGap
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverOneStepResidual R =
      Complex.re
        (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver) /
        alphaPhaseObserverModelNormalization - alphaCodata2022Gap := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_is_alpha_selected_root_scalar_sub_codataGap
      (R := R) hR hRlt

theorem alpha_selected_centered_residual_unique_by_arithmetic
    {k : ZMod CycleLen} {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k) :
    k = alphaPhaseObserver ∧
    alphaPhaseObserverOneStepResidual R =
      Complex.re
        (alphaInvRunningModel 1 k R -
          ((13 : ℂ)⁻¹) * (∑ j : ZMod CycleLen, alphaInvRunningModel 1 j R)) /
        alphaPhaseObserverModelNormalization - alphaCodata2022Gap := by
  have hk' : k = alphaPhaseObserver := hk.symm.trans alphaPhaseObserver_selected_by_alpha_arithmetic
  rcases alphaPhaseObserverOneStepResidual_eq_alpha_selected_centered_comparison_sub_codataGap
      (R := R) hR hRlt with ⟨_, hres⟩
  refine ⟨hk', ?_⟩
  simpa [hk'] using hres

theorem alpha_selected_root_scalar_residual_unique_by_arithmetic
    {k : ZMod CycleLen} {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (hk : (Int.floor ufrf_alpha_inv : ZMod CycleLen) = k) :
    k = alphaPhaseObserver ∧
    alphaPhaseObserverOneStepResidual R =
      Complex.re
        (((1 : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt k) /
        alphaPhaseObserverModelNormalization - alphaCodata2022Gap := by
  have hk' : k = alphaPhaseObserver := hk.symm.trans alphaPhaseObserver_selected_by_alpha_arithmetic
  rcases alphaPhaseObserverOneStepResidual_is_alpha_selected_root_scalar_sub_codataGap
      (R := R) hR hRlt with ⟨_, hres⟩
  refine ⟨hk', ?_⟩
  simpa [hk'] using hres

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
Every local cycle-prime channel hits the selected observer label.

This is the local concurrency statement specialized to the alpha observer:
label `7` is not exclusive to the `7`-channel, but a shared position visited by
all four cycle-prime paths.
-/
theorem cycle_prime_channels_hit_alphaPhaseObserver :
    ∃ n3 n5 n7 n11 : ℕ,
      (n3 * 3 : ZMod 13) = alphaPhaseObserver ∧
      (n5 * 5 : ZMod 13) = alphaPhaseObserver ∧
      (n7 * 7 : ZMod 13) = alphaPhaseObserver ∧
      (n11 * 11 : ZMod 13) = alphaPhaseObserver := by
  refine ⟨11, 4, 1, 3, ?_, ?_, ?_, ?_⟩ <;>
    rw [alphaPhaseObserver_eq_seven] <;> decide

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
