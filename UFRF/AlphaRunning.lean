import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Exp
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
The current model normalization inherits the simplex boundary factor together
with the arithmetic-selected observer label.

This is a structural inheritance theorem for the present `/ 28` rule, not a
uniqueness theorem about all possible normalizations.
-/
theorem alphaPhaseObserverModelNormalization_inherits_simplex_boundary_and_selected_label :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverModelNormalization =
      (simplex3_boundary_face_count : ℝ) * (alphaPhaseObserver.val : ℝ) := by
  refine ⟨alphaPhaseObserver_selected_by_alpha_arithmetic, ?_⟩
  have hval : alphaPhaseObserver.val = 7 := by
    rw [alphaPhaseObserver_eq_seven]
    have h7lt : (7 : ℕ) < CycleLen := by
      norm_num [CycleLen, UFRF.CircleIntegralBreathing.CycleLen,
        UFRF.ComplexBreathing.CycleLen, FourierCycleLen,
        BreathingCycle.cycle_len, UFRF.Foundation.derived_cycle_length,
        UFRF.Foundation.trinity_dimension, UFRF.Structure13.projective_order]
    exact ZMod.val_natCast_of_lt h7lt
  rw [alphaPhaseObserverModelNormalization, hval]
  norm_num

/--
Normalized real-valued selected-observer correction used for model comparison.
-/
def alphaPhaseObserverNormalizedRealCorrection (n : ℤ) (R : ℝ) : ℝ :=
  alphaPhaseObserverRealCorrection n R / alphaPhaseObserverModelNormalization

theorem alphaPhaseObserverNormalizedRealCorrection_eq_realCorrection_div_inherited_normalization
    (n : ℤ) (R : ℝ) :
    alphaPhaseObserverNormalizedRealCorrection n R =
      alphaPhaseObserverRealCorrection n R /
        ((simplex3_boundary_face_count : ℝ) * (alphaPhaseObserver.val : ℝ)) := by
  rw [alphaPhaseObserverNormalizedRealCorrection]
  rcases alphaPhaseObserverModelNormalization_inherits_simplex_boundary_and_selected_label with
    ⟨_, hnorm⟩
  rw [hnorm]

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

private theorem abs_cos_sub_taylor10_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x -
        (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800)| ≤
      |x| ^ 12 * (13 / ((Nat.factorial 12 : ℝ) * 12)) := by
  have hx' : ‖((x : ℂ) * Complex.I)‖ ≤ 1 := by
    simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs, mul_comm] using hx
  have hsum :
      (∑ m ∈ Finset.range 12, ((((x : ℂ) * Complex.I) ^ m) / m.factorial : ℂ)) =
        (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800) +
          (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800) *
            Complex.I := by
    apply Complex.ext <;>
      simp [Finset.sum_range_succ, Nat.factorial, pow_succ,
        Complex.mul_re, Complex.mul_im] <;>
      ring
  have hbound := Complex.exp_bound (x := (x : ℂ) * Complex.I) hx' (n := 12) (by norm_num : 0 < 12)
  rw [hsum] at hbound
  have hbound' :
      ‖Complex.exp ((x : ℂ) * Complex.I) -
          ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800) +
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800) *
              Complex.I)‖ ≤
        |x| ^ 12 * (13 / ((Nat.factorial 12 : ℝ) * 12)) := by
    simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using hbound
  have hre :
      (Complex.exp ((x : ℂ) * Complex.I) -
          ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800) +
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800) *
              Complex.I)).re =
        Real.cos x -
          (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800) := by
    simp [Complex.exp_ofReal_mul_I, Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, Complex.cos_ofReal_re]
  have hcos_raw :
      |(Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800) *
                Complex.I)).re| ≤
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800) *
                Complex.I)‖ :=
    Complex.abs_re_le_norm _
  have hcos :
      |Real.cos x -
          (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800)| ≤
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800) *
                Complex.I)‖ := by
    simpa [hre] using hcos_raw
  exact hcos.trans hbound'

private theorem abs_cos_sub_taylor12_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x -
        (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
          x ^ 12 / 479001600)| ≤
      |x| ^ 14 * (15 / ((Nat.factorial 14 : ℝ) * 14)) := by
  have hx' : ‖((x : ℂ) * Complex.I)‖ ≤ 1 := by
    simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs, mul_comm] using hx
  have hsum :
      (∑ m ∈ Finset.range 14, ((((x : ℂ) * Complex.I) ^ m) / m.factorial : ℂ)) =
        (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600) +
          (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
              x ^ 13 / 6227020800) *
            Complex.I := by
    apply Complex.ext <;>
      simp [Finset.sum_range_succ, Nat.factorial, pow_succ,
        Complex.mul_re, Complex.mul_im] <;>
      ring
  have hbound := Complex.exp_bound (x := (x : ℂ) * Complex.I) hx' (n := 14) (by norm_num : 0 < 14)
  rw [hsum] at hbound
  have hbound' :
      ‖Complex.exp ((x : ℂ) * Complex.I) -
          ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                x ^ 12 / 479001600) +
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                x ^ 13 / 6227020800) *
              Complex.I)‖ ≤
        |x| ^ 14 * (15 / ((Nat.factorial 14 : ℝ) * 14)) := by
    simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using hbound
  have hre :
      (Complex.exp ((x : ℂ) * Complex.I) -
          ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                x ^ 12 / 479001600) +
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                x ^ 13 / 6227020800) *
              Complex.I)).re =
        Real.cos x -
          (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600) := by
    simp [Complex.exp_ofReal_mul_I, Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, Complex.cos_ofReal_re]
  have hcos_raw :
      |(Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800) *
                Complex.I)).re| ≤
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800) *
                Complex.I)‖ :=
    Complex.abs_re_le_norm _
  have hcos :
      |Real.cos x -
          (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600)| ≤
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800) *
                Complex.I)‖ := by
    simpa [hre] using hcos_raw
  exact hcos.trans hbound'

private theorem abs_cos_sub_taylor14_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x -
        (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
          x ^ 12 / 479001600 - x ^ 14 / 87178291200)| ≤
      |x| ^ 16 * (17 / ((Nat.factorial 16 : ℝ) * 16)) := by
  have hx' : ‖((x : ℂ) * Complex.I)‖ ≤ 1 := by
    simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs, mul_comm] using hx
  have hsum :
      (∑ m ∈ Finset.range 16, ((((x : ℂ) * Complex.I) ^ m) / m.factorial : ℂ)) =
        (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600 - x ^ 14 / 87178291200) +
          (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
              x ^ 13 / 6227020800 - x ^ 15 / 1307674368000) *
            Complex.I := by
    apply Complex.ext <;>
      simp [Finset.sum_range_succ, Nat.factorial, pow_succ,
        Complex.mul_re, Complex.mul_im] <;>
      ring
  have hbound := Complex.exp_bound (x := (x : ℂ) * Complex.I) hx' (n := 16) (by norm_num : 0 < 16)
  rw [hsum] at hbound
  have hbound' :
      ‖Complex.exp ((x : ℂ) * Complex.I) -
          ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                x ^ 12 / 479001600 - x ^ 14 / 87178291200) +
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                x ^ 13 / 6227020800 - x ^ 15 / 1307674368000) *
              Complex.I)‖ ≤
        |x| ^ 16 * (17 / ((Nat.factorial 16 : ℝ) * 16)) := by
    simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using hbound
  have hre :
      (Complex.exp ((x : ℂ) * Complex.I) -
          ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                x ^ 12 / 479001600 - x ^ 14 / 87178291200) +
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                x ^ 13 / 6227020800 - x ^ 15 / 1307674368000) *
              Complex.I)).re =
        Real.cos x -
          (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600 - x ^ 14 / 87178291200) := by
    simp [Complex.exp_ofReal_mul_I, Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, Complex.cos_ofReal_re]
  have hcos_raw :
      |(Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600 - x ^ 14 / 87178291200) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800 - x ^ 15 / 1307674368000) *
                Complex.I)).re| ≤
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600 - x ^ 14 / 87178291200) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800 - x ^ 15 / 1307674368000) *
                Complex.I)‖ :=
    Complex.abs_re_le_norm _
  have hcos :
      |Real.cos x -
          (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600 - x ^ 14 / 87178291200)| ≤
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600 - x ^ 14 / 87178291200) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800 - x ^ 15 / 1307674368000) *
                Complex.I)‖ := by
    simpa [hre] using hcos_raw
  exact hcos.trans hbound'

private theorem abs_cos_sub_taylor16_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x -
        (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
          x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000)| ≤
      |x| ^ 18 * (19 / ((Nat.factorial 18 : ℝ) * 18)) := by
  have hx' : ‖((x : ℂ) * Complex.I)‖ ≤ 1 := by
    simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs, mul_comm] using hx
  have hsum :
      (∑ m ∈ Finset.range 18, ((((x : ℂ) * Complex.I) ^ m) / m.factorial : ℂ)) =
        (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000) +
          (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
              x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000) *
            Complex.I := by
    apply Complex.ext <;>
      simp [Finset.sum_range_succ, Nat.factorial, pow_succ,
        Complex.mul_re, Complex.mul_im] <;>
      ring
  have hbound := Complex.exp_bound (x := (x : ℂ) * Complex.I) hx' (n := 18) (by norm_num : 0 < 18)
  rw [hsum] at hbound
  have hbound' :
      ‖Complex.exp ((x : ℂ) * Complex.I) -
          ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000) +
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000) *
              Complex.I)‖ ≤
        |x| ^ 18 * (19 / ((Nat.factorial 18 : ℝ) * 18)) := by
    simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using hbound
  have hre :
      (Complex.exp ((x : ℂ) * Complex.I) -
          ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000) +
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000) *
              Complex.I)).re =
        Real.cos x -
          (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000) := by
    simp [Complex.exp_ofReal_mul_I, Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, Complex.cos_ofReal_re]
  have hcos_raw :
      |(Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000) *
                Complex.I)).re| ≤
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000) *
                Complex.I)‖ :=
    Complex.abs_re_le_norm _
  have hcos :
      |Real.cos x -
          (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000)| ≤
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000) *
                Complex.I)‖ := by
    simpa [hre] using hcos_raw
  exact hcos.trans hbound'

private theorem abs_cos_sub_taylor18_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x -
        (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
          x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
          x ^ 18 / 6402373705728000)| ≤
      |x| ^ 20 * (21 / ((Nat.factorial 20 : ℝ) * 20)) := by
  have hx' : ‖((x : ℂ) * Complex.I)‖ ≤ 1 := by
    simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs, mul_comm] using hx
  have hsum :
      (∑ m ∈ Finset.range 20, ((((x : ℂ) * Complex.I) ^ m) / m.factorial : ℂ)) =
        (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
            x ^ 18 / 6402373705728000) +
          (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
              x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000 -
              x ^ 19 / 121645100408832000) *
            Complex.I := by
    apply Complex.ext <;>
      simp [Finset.sum_range_succ, Nat.factorial, pow_succ,
        Complex.mul_re, Complex.mul_im] <;>
      ring
  have hbound := Complex.exp_bound (x := (x : ℂ) * Complex.I) hx' (n := 20) (by norm_num : 0 < 20)
  rw [hsum] at hbound
  have hbound' :
      ‖Complex.exp ((x : ℂ) * Complex.I) -
          ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
                x ^ 18 / 6402373705728000) +
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000 -
                x ^ 19 / 121645100408832000) *
              Complex.I)‖ ≤
        |x| ^ 20 * (21 / ((Nat.factorial 20 : ℝ) * 20)) := by
    simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using hbound
  have hre :
      (Complex.exp ((x : ℂ) * Complex.I) -
          ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
                x ^ 18 / 6402373705728000) +
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000 -
                x ^ 19 / 121645100408832000) *
              Complex.I)).re =
        Real.cos x -
          (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
            x ^ 18 / 6402373705728000) := by
    simp [Complex.exp_ofReal_mul_I, Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, Complex.cos_ofReal_re]
  have hcos_raw :
      |(Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
                  x ^ 18 / 6402373705728000) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000 -
                  x ^ 19 / 121645100408832000) *
                Complex.I)).re| ≤
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
                  x ^ 18 / 6402373705728000) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000 -
                  x ^ 19 / 121645100408832000) *
                Complex.I)‖ :=
    Complex.abs_re_le_norm _
  have hcos :
      |Real.cos x -
          (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
            x ^ 18 / 6402373705728000)| ≤
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
                  x ^ 18 / 6402373705728000) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000 -
                  x ^ 19 / 121645100408832000) *
                Complex.I)‖ := by
    simpa [hre] using hcos_raw
  exact hcos.trans hbound'

private theorem abs_cos_sub_taylor20_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x -
        (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
          x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
          x ^ 18 / 6402373705728000 + x ^ 20 / 2432902008176640000)| ≤
      |x| ^ 22 * (23 / ((Nat.factorial 22 : ℝ) * 22)) := by
  have hx' : ‖((x : ℂ) * Complex.I)‖ ≤ 1 := by
    simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs, mul_comm] using hx
  have hsum :
      (∑ m ∈ Finset.range 22, ((((x : ℂ) * Complex.I) ^ m) / m.factorial : ℂ)) =
        (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
            x ^ 18 / 6402373705728000 + x ^ 20 / 2432902008176640000) +
          (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
              x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000 -
              x ^ 19 / 121645100408832000 + x ^ 21 / 51090942171709440000) *
            Complex.I := by
    apply Complex.ext <;>
      simp [Finset.sum_range_succ, Nat.factorial, pow_succ,
        Complex.mul_re, Complex.mul_im] <;>
      ring
  have hbound := Complex.exp_bound (x := (x : ℂ) * Complex.I) hx' (n := 22) (by norm_num : 0 < 22)
  rw [hsum] at hbound
  have hbound' :
      ‖Complex.exp ((x : ℂ) * Complex.I) -
          ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
                x ^ 18 / 6402373705728000 + x ^ 20 / 2432902008176640000) +
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000 -
                x ^ 19 / 121645100408832000 + x ^ 21 / 51090942171709440000) *
              Complex.I)‖ ≤
        |x| ^ 22 * (23 / ((Nat.factorial 22 : ℝ) * 22)) := by
    simpa [Complex.norm_mul, Complex.norm_I, Real.norm_eq_abs, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using hbound
  have hre :
      (Complex.exp ((x : ℂ) * Complex.I) -
          ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
                x ^ 18 / 6402373705728000 + x ^ 20 / 2432902008176640000) +
            (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000 -
                x ^ 19 / 121645100408832000 + x ^ 21 / 51090942171709440000) *
              Complex.I)).re =
        Real.cos x -
          (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
            x ^ 18 / 6402373705728000 + x ^ 20 / 2432902008176640000) := by
    simp [Complex.exp_ofReal_mul_I, Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, Complex.cos_ofReal_re]
  have hcos_raw :
      |(Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
                  x ^ 18 / 6402373705728000 + x ^ 20 / 2432902008176640000) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000 -
                  x ^ 19 / 121645100408832000 + x ^ 21 / 51090942171709440000) *
                Complex.I)).re| ≤
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
                  x ^ 18 / 6402373705728000 + x ^ 20 / 2432902008176640000) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000 -
                  x ^ 19 / 121645100408832000 + x ^ 21 / 51090942171709440000) *
                Complex.I)‖ :=
    Complex.abs_re_le_norm _
  have hcos :
      |Real.cos x -
          (1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
            x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
            x ^ 18 / 6402373705728000 + x ^ 20 / 2432902008176640000)| ≤
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            ((1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800 +
                  x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000 -
                  x ^ 18 / 6402373705728000 + x ^ 20 / 2432902008176640000) +
              (x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800 +
                  x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 + x ^ 17 / 355687428096000 -
                  x ^ 19 / 121645100408832000 + x ^ 21 / 51090942171709440000) *
                Complex.I)‖ := by
    simpa [hre] using hcos_raw
  exact hcos.trans hbound'

set_option maxHeartbeats 2000000 in
private theorem cos_pi_div_thirteen_bounds_tight :
    (0.970941817426052027 : ℝ) < Real.cos (Real.pi / 13) ∧
    Real.cos (Real.pi / 13) < (0.970941817426052028 : ℝ) := by
  let poly12 : ℝ → ℝ := fun t =>
    1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 +
      t ^ 12 / 479001600
  let remCoeff14 : ℝ := 15 / ((Nat.factorial 14 : ℝ) * 14)
  have hpi1_nonneg : 0 ≤ Real.pi / 13 := by positivity
  have hpi1_abs : |Real.pi / 13| ≤ 1 := by
    rw [abs_of_nonneg hpi1_nonneg]
    have hpi : Real.pi < 4 := Real.pi_lt_four
    nlinarith
  have hpi1_lo : (0.24166097335306101834 : ℝ) < Real.pi / 13 := by
    have hpi : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
    nlinarith
  have hpi1_hi : Real.pi / 13 < (0.24166097335306101835 : ℝ) := by
    have hpi : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
    nlinarith
  have hpi1_2_lo : (0.24166097335306101834 : ℝ) ^ 2 ≤ (Real.pi / 13) ^ 2 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_2_hi : (Real.pi / 13) ^ 2 ≤ (0.24166097335306101835 : ℝ) ^ 2 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_4_lo : (0.24166097335306101834 : ℝ) ^ 4 ≤ (Real.pi / 13) ^ 4 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_4_hi : (Real.pi / 13) ^ 4 ≤ (0.24166097335306101835 : ℝ) ^ 4 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_6_lo : (0.24166097335306101834 : ℝ) ^ 6 ≤ (Real.pi / 13) ^ 6 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_6_hi : (Real.pi / 13) ^ 6 ≤ (0.24166097335306101835 : ℝ) ^ 6 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_8_lo : (0.24166097335306101834 : ℝ) ^ 8 ≤ (Real.pi / 13) ^ 8 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_8_hi : (Real.pi / 13) ^ 8 ≤ (0.24166097335306101835 : ℝ) ^ 8 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_10_lo : (0.24166097335306101834 : ℝ) ^ 10 ≤ (Real.pi / 13) ^ 10 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_10_hi : (Real.pi / 13) ^ 10 ≤ (0.24166097335306101835 : ℝ) ^ 10 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_12_lo : (0.24166097335306101834 : ℝ) ^ 12 ≤ (Real.pi / 13) ^ 12 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_12_hi : (Real.pi / 13) ^ 12 ≤ (0.24166097335306101835 : ℝ) ^ 12 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_14_hi : (Real.pi / 13) ^ 14 ≤ (0.24166097335306101835 : ℝ) ^ 14 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpoly1_lo : (0.97094181742605202718 : ℝ) < poly12 (Real.pi / 13) := by
    dsimp [poly12]
    nlinarith [hpi1_2_hi, hpi1_4_lo, hpi1_6_hi, hpi1_8_lo, hpi1_10_hi, hpi1_12_lo]
  have hpoly1_hi : poly12 (Real.pi / 13) < (0.97094181742605202719 : ℝ) := by
    dsimp [poly12]
    nlinarith [hpi1_2_lo, hpi1_4_hi, hpi1_6_lo, hpi1_8_hi, hpi1_10_lo, hpi1_12_hi]
  have hrem1 : (Real.pi / 13) ^ 14 * remCoeff14 < (0.00000000000000000003 : ℝ) := by
    have htmp :
        (Real.pi / 13) ^ 14 * remCoeff14 ≤
          (0.24166097335306101835 : ℝ) ^ 14 * remCoeff14 := by
      have hcoeff_nonneg : 0 ≤ remCoeff14 := by
        dsimp [remCoeff14]
        positivity
      nlinarith [hpi1_14_hi, hcoeff_nonneg]
    have hconst :
        (0.24166097335306101835 : ℝ) ^ 14 * remCoeff14 <
          (0.00000000000000000003 : ℝ) := by
      dsimp [remCoeff14]
      norm_num
    exact lt_of_le_of_lt htmp hconst
  have hcos1_err := abs_cos_sub_taylor12_le (x := Real.pi / 13) hpi1_abs
  rcases
      abs_sub_le_iff.mp
        (by
          simpa [poly12, remCoeff14, abs_of_nonneg hpi1_nonneg] using hcos1_err) with
    ⟨hcos1_sub_upper, hcos1_sub_lower⟩
  have hcos1_lower :
      poly12 (Real.pi / 13) - (Real.pi / 13) ^ 14 * remCoeff14 ≤ Real.cos (Real.pi / 13) := by
    dsimp [poly12, remCoeff14] at hcos1_sub_lower ⊢
    apply (sub_le_iff_le_add').2
    nlinarith [hcos1_sub_lower]
  have hcos1_upper :
      Real.cos (Real.pi / 13) ≤ poly12 (Real.pi / 13) + (Real.pi / 13) ^ 14 * remCoeff14 := by
    dsimp [poly12, remCoeff14] at hcos1_sub_upper ⊢
    exact (sub_le_iff_le_add').1 hcos1_sub_upper
  constructor
  · nlinarith [hpoly1_lo, hrem1, hcos1_lower]
  · nlinarith [hpoly1_hi, hrem1, hcos1_upper]

set_option maxHeartbeats 2000000 in
private theorem cos_pi_div_thirteen_bounds_refined :
    (0.970941817426052027 : ℝ) < Real.cos (Real.pi / 13) ∧
    Real.cos (Real.pi / 13) < (0.970941817426052028 : ℝ) := by
  exact cos_pi_div_thirteen_bounds_tight

set_option maxHeartbeats 2000000 in
theorem phase7OneStepModelPrediction_bounds_d13 :
    (0.00030553718304 : ℝ) < phase7OneStepModelPrediction ∧
    phase7OneStepModelPrediction < 0.00030553718305 := by
  let poly10 : ℝ → ℝ := fun t =>
    1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800
  let remCoeff12 : ℝ := 13 / ((Nat.factorial 12 : ℝ) * 12)
  let poly12 : ℝ → ℝ := fun t => poly10 t + t ^ 12 / 479001600
  let remCoeff14 : ℝ := 15 / ((Nat.factorial 14 : ℝ) * 14)
  have hpi1_nonneg : 0 ≤ Real.pi / 13 := by positivity
  have hpi1_abs : |Real.pi / 13| ≤ 1 := by
    rw [abs_of_nonneg hpi1_nonneg]
    have hpi : Real.pi < 4 := Real.pi_lt_four
    nlinarith
  have hpi1_lo : (0.24166097335306101834 : ℝ) < Real.pi / 13 := by
    have hpi : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
    nlinarith
  have hpi1_hi : Real.pi / 13 < (0.24166097335306101835 : ℝ) := by
    have hpi : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
    nlinarith
  have hpi1_2_lo : (0.24166097335306101834 : ℝ) ^ 2 ≤ (Real.pi / 13) ^ 2 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_2_hi : (Real.pi / 13) ^ 2 ≤ (0.24166097335306101835 : ℝ) ^ 2 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_4_lo : (0.24166097335306101834 : ℝ) ^ 4 ≤ (Real.pi / 13) ^ 4 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_4_hi : (Real.pi / 13) ^ 4 ≤ (0.24166097335306101835 : ℝ) ^ 4 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_6_lo : (0.24166097335306101834 : ℝ) ^ 6 ≤ (Real.pi / 13) ^ 6 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_6_hi : (Real.pi / 13) ^ 6 ≤ (0.24166097335306101835 : ℝ) ^ 6 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_8_lo : (0.24166097335306101834 : ℝ) ^ 8 ≤ (Real.pi / 13) ^ 8 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_8_hi : (Real.pi / 13) ^ 8 ≤ (0.24166097335306101835 : ℝ) ^ 8 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_10_lo : (0.24166097335306101834 : ℝ) ^ 10 ≤ (Real.pi / 13) ^ 10 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_10_hi : (Real.pi / 13) ^ 10 ≤ (0.24166097335306101835 : ℝ) ^ 10 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_12_hi : (Real.pi / 13) ^ 12 ≤ (0.24166097335306101835 : ℝ) ^ 12 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpoly1_lo : (0.9709418174260519 : ℝ) < poly10 (Real.pi / 13) := by
    dsimp [poly10]
    nlinarith [hpi1_2_hi, hpi1_4_lo, hpi1_6_hi, hpi1_8_lo, hpi1_10_hi]
  have hpoly1_hi : poly10 (Real.pi / 13) < (0.970941817426052 : ℝ) := by
    dsimp [poly10]
    nlinarith [hpi1_2_lo, hpi1_4_hi, hpi1_6_lo, hpi1_8_hi, hpi1_10_lo]
  have hrem1 : (Real.pi / 13) ^ 12 * remCoeff12 < (0.0000000000000001 : ℝ) := by
    have htmp :
        (Real.pi / 13) ^ 12 * remCoeff12 ≤
          (0.24166097335306101835 : ℝ) ^ 12 * remCoeff12 := by
      have hcoeff_nonneg : 0 ≤ remCoeff12 := by
        dsimp [remCoeff12]
        positivity
      nlinarith [hpi1_12_hi, hcoeff_nonneg]
    have hconst :
        (0.24166097335306101835 : ℝ) ^ 12 * remCoeff12 <
          (0.0000000000000001 : ℝ) := by
      dsimp [remCoeff12]
      norm_num
    exact lt_of_le_of_lt htmp hconst
  have hcos1_err := abs_cos_sub_taylor10_le (x := Real.pi / 13) hpi1_abs
  rcases
      abs_sub_le_iff.mp
        (by
          simpa [poly10, remCoeff12, abs_of_nonneg hpi1_nonneg] using hcos1_err) with
    ⟨hcos1_sub_upper, hcos1_sub_lower⟩
  have hcos1_lower :
      poly10 (Real.pi / 13) - (Real.pi / 13) ^ 12 * remCoeff12 ≤ Real.cos (Real.pi / 13) := by
    dsimp [poly10, remCoeff12] at hcos1_sub_lower ⊢
    apply (sub_le_iff_le_add').2
    nlinarith [hcos1_sub_lower]
  have hcos1_upper :
      Real.cos (Real.pi / 13) ≤ poly10 (Real.pi / 13) + (Real.pi / 13) ^ 12 * remCoeff12 := by
    dsimp [poly10, remCoeff12] at hcos1_sub_upper ⊢
    exact (sub_le_iff_le_add').1 hcos1_sub_upper
  have hcos1 :
      (0.9709418174260518 : ℝ) < Real.cos (Real.pi / 13) ∧
      Real.cos (Real.pi / 13) < (0.9709418174260521 : ℝ) := by
    constructor
    · nlinarith [hpoly1_lo, hrem1, hcos1_lower]
    · nlinarith [hpoly1_hi, hrem1, hcos1_upper]
  have hpi3_nonneg : 0 ≤ 3 * Real.pi / 13 := by positivity
  have hpi3_abs : |3 * Real.pi / 13| ≤ 1 := by
    rw [abs_of_nonneg hpi3_nonneg]
    have hpi : Real.pi < 4 := Real.pi_lt_four
    nlinarith
  have hpi3_lo : (0.72498292005918305502 : ℝ) < 3 * Real.pi / 13 := by
    have hpi : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
    nlinarith
  have hpi3_hi : 3 * Real.pi / 13 < (0.72498292005918305504 : ℝ) := by
    have hpi : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
    nlinarith
  have hpi3_2_lo : (0.72498292005918305502 : ℝ) ^ 2 ≤ (3 * Real.pi / 13) ^ 2 := by
    nlinarith [hpi3_lo, hpi3_nonneg]
  have hpi3_2_hi : (3 * Real.pi / 13) ^ 2 ≤ (0.72498292005918305504 : ℝ) ^ 2 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpi3_4_lo : (0.72498292005918305502 : ℝ) ^ 4 ≤ (3 * Real.pi / 13) ^ 4 := by
    nlinarith [hpi3_lo, hpi3_nonneg]
  have hpi3_4_hi : (3 * Real.pi / 13) ^ 4 ≤ (0.72498292005918305504 : ℝ) ^ 4 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpi3_6_lo : (0.72498292005918305502 : ℝ) ^ 6 ≤ (3 * Real.pi / 13) ^ 6 := by
    nlinarith [hpi3_lo, hpi3_nonneg]
  have hpi3_6_hi : (3 * Real.pi / 13) ^ 6 ≤ (0.72498292005918305504 : ℝ) ^ 6 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpi3_8_lo : (0.72498292005918305502 : ℝ) ^ 8 ≤ (3 * Real.pi / 13) ^ 8 := by
    nlinarith [hpi3_lo, hpi3_nonneg]
  have hpi3_8_hi : (3 * Real.pi / 13) ^ 8 ≤ (0.72498292005918305504 : ℝ) ^ 8 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpi3_10_lo : (0.72498292005918305502 : ℝ) ^ 10 ≤ (3 * Real.pi / 13) ^ 10 := by
    nlinarith [hpi3_lo, hpi3_nonneg]
  have hpi3_10_hi : (3 * Real.pi / 13) ^ 10 ≤ (0.72498292005918305504 : ℝ) ^ 10 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpi3_12_lo : (0.72498292005918305502 : ℝ) ^ 12 ≤ (3 * Real.pi / 13) ^ 12 := by
    nlinarith [hpi3_lo, hpi3_nonneg]
  have hpi3_12_hi : (3 * Real.pi / 13) ^ 12 ≤ (0.72498292005918305504 : ℝ) ^ 12 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpi3_14_hi : (3 * Real.pi / 13) ^ 14 ≤ (0.72498292005918305504 : ℝ) ^ 14 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpoly3_lo : (0.74851074817122 : ℝ) < poly12 (3 * Real.pi / 13) := by
    dsimp [poly12, poly10]
    nlinarith [hpi3_2_hi, hpi3_4_lo, hpi3_6_hi, hpi3_8_lo, hpi3_10_hi, hpi3_12_lo]
  have hpoly3_hi : poly12 (3 * Real.pi / 13) < (0.74851074817123 : ℝ) := by
    dsimp [poly12, poly10]
    nlinarith [hpi3_2_lo, hpi3_4_hi, hpi3_6_lo, hpi3_8_hi, hpi3_10_lo, hpi3_12_hi]
  have hrem3 : (3 * Real.pi / 13) ^ 14 * remCoeff14 < (0.00000000000014 : ℝ) := by
    have htmp :
        (3 * Real.pi / 13) ^ 14 * remCoeff14 ≤
          (0.72498292005918305504 : ℝ) ^ 14 * remCoeff14 := by
      have hcoeff_nonneg : 0 ≤ remCoeff14 := by
        dsimp [remCoeff14]
        positivity
      nlinarith [hpi3_14_hi, hcoeff_nonneg]
    have hconst :
        (0.72498292005918305504 : ℝ) ^ 14 * remCoeff14 <
          (0.00000000000014 : ℝ) := by
      dsimp [remCoeff14]
      norm_num
    exact lt_of_le_of_lt htmp hconst
  have hcos3_err := abs_cos_sub_taylor12_le (x := 3 * Real.pi / 13) hpi3_abs
  rcases
      abs_sub_le_iff.mp
        (by
          simpa [poly12, remCoeff14, abs_of_nonneg hpi3_nonneg] using hcos3_err) with
    ⟨hcos3_sub_upper, hcos3_sub_lower⟩
  have hcos3_lower :
      poly12 (3 * Real.pi / 13) - (3 * Real.pi / 13) ^ 14 * remCoeff14 ≤
        Real.cos (3 * Real.pi / 13) := by
    dsimp [poly12, poly10, remCoeff14] at hcos3_sub_lower ⊢
    apply (sub_le_iff_le_add').2
    nlinarith [hcos3_sub_lower]
  have hcos3_upper :
      Real.cos (3 * Real.pi / 13) ≤
        poly12 (3 * Real.pi / 13) + (3 * Real.pi / 13) ^ 14 * remCoeff14 := by
    dsimp [poly12, poly10, remCoeff14] at hcos3_sub_upper ⊢
    exact (sub_le_iff_le_add').1 hcos3_sub_upper
  have hcos3 :
      (0.7485107481710 : ℝ) < Real.cos (3 * Real.pi / 13) ∧
      Real.cos (3 * Real.pi / 13) < (0.7485107481714 : ℝ) := by
    constructor
    · nlinarith [hpoly3_lo, hrem3, hcos3_lower]
    · nlinarith [hpoly3_hi, hrem3, hcos3_upper]
  rw [phase7OneStepModelPrediction_eq_cos_pi_div_thirteen_sub_cos_three_pi_div_thirteen]
  rcases hcos1 with ⟨hcos1_lo, hcos1_hi⟩
  rcases hcos3 with ⟨hcos3_lo, hcos3_hi⟩
  constructor
  · have hnum :
        (0.9709418174260518 : ℝ) - 0.7485107481714 <
          Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13) := by
      nlinarith
    have hdiv :
        ((0.9709418174260518 : ℝ) - 0.7485107481714) / 728 <
          (Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13)) / 728 := by
      exact div_lt_div_of_pos_right hnum (show (0 : ℝ) < 728 by norm_num)
    have hconst :
        (0.00030553718304 : ℝ) <
          ((0.9709418174260518 : ℝ) - 0.7485107481714) / 728 := by
      norm_num
    exact lt_trans hconst hdiv
  · have hnum :
        Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13) <
          (0.9709418174260521 : ℝ) - 0.7485107481710 := by
      nlinarith
    have hdiv :
        (Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13)) / 728 <
          ((0.9709418174260521 : ℝ) - 0.7485107481710) / 728 := by
      exact div_lt_div_of_pos_right hnum (show (0 : ℝ) < 728 by norm_num)
    have hconst :
        ((0.9709418174260521 : ℝ) - 0.7485107481710) / 728 <
          (0.00030553718305 : ℝ) := by
      norm_num
    exact lt_trans hdiv hconst

set_option maxHeartbeats 2000000 in
private theorem cos_three_pi_div_thirteen_bounds_tight :
    (0.7485107481711010986 : ℝ) < Real.cos (3 * Real.pi / 13) ∧
    Real.cos (3 * Real.pi / 13) < (0.7485107481711010997 : ℝ) := by
  let poly16 : ℝ → ℝ := fun t =>
    1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 +
      t ^ 12 / 479001600 - t ^ 14 / 87178291200 + t ^ 16 / 20922789888000
  let remCoeff18 : ℝ := 19 / ((Nat.factorial 18 : ℝ) * 18)
  have hpi3_nonneg : 0 ≤ 3 * Real.pi / 13 := by positivity
  have hpi3_abs : |3 * Real.pi / 13| ≤ 1 := by
    rw [abs_of_nonneg hpi3_nonneg]
    have hpi : Real.pi < 4 := Real.pi_lt_four
    nlinarith
  have hpi3_lo : (0.72498292005918305502 : ℝ) < 3 * Real.pi / 13 := by
    have hpi : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
    nlinarith
  have hpi3_hi : 3 * Real.pi / 13 < (0.72498292005918305504 : ℝ) := by
    have hpi : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
    nlinarith
  have hpi3_2_lo : (0.72498292005918305502 : ℝ) ^ 2 ≤ (3 * Real.pi / 13) ^ 2 := by
    nlinarith [hpi3_lo, hpi3_nonneg]
  have hpi3_2_hi : (3 * Real.pi / 13) ^ 2 ≤ (0.72498292005918305504 : ℝ) ^ 2 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpi3_4_lo : (0.72498292005918305502 : ℝ) ^ 4 ≤ (3 * Real.pi / 13) ^ 4 := by
    nlinarith [hpi3_lo, hpi3_nonneg]
  have hpi3_4_hi : (3 * Real.pi / 13) ^ 4 ≤ (0.72498292005918305504 : ℝ) ^ 4 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpi3_6_lo : (0.72498292005918305502 : ℝ) ^ 6 ≤ (3 * Real.pi / 13) ^ 6 := by
    nlinarith [hpi3_lo, hpi3_nonneg]
  have hpi3_6_hi : (3 * Real.pi / 13) ^ 6 ≤ (0.72498292005918305504 : ℝ) ^ 6 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpi3_8_lo : (0.72498292005918305502 : ℝ) ^ 8 ≤ (3 * Real.pi / 13) ^ 8 := by
    nlinarith [hpi3_lo, hpi3_nonneg]
  have hpi3_8_hi : (3 * Real.pi / 13) ^ 8 ≤ (0.72498292005918305504 : ℝ) ^ 8 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpi3_10_lo : (0.72498292005918305502 : ℝ) ^ 10 ≤ (3 * Real.pi / 13) ^ 10 := by
    nlinarith [hpi3_lo, hpi3_nonneg]
  have hpi3_10_hi : (3 * Real.pi / 13) ^ 10 ≤ (0.72498292005918305504 : ℝ) ^ 10 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpi3_12_lo : (0.72498292005918305502 : ℝ) ^ 12 ≤ (3 * Real.pi / 13) ^ 12 := by
    nlinarith [hpi3_lo, hpi3_nonneg]
  have hpi3_12_hi : (3 * Real.pi / 13) ^ 12 ≤ (0.72498292005918305504 : ℝ) ^ 12 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpi3_14_lo : (0.72498292005918305502 : ℝ) ^ 14 ≤ (3 * Real.pi / 13) ^ 14 := by
    nlinarith [hpi3_lo, hpi3_nonneg]
  have hpi3_14_hi : (3 * Real.pi / 13) ^ 14 ≤ (0.72498292005918305504 : ℝ) ^ 14 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpi3_16_lo : (0.72498292005918305502 : ℝ) ^ 16 ≤ (3 * Real.pi / 13) ^ 16 := by
    nlinarith [hpi3_lo, hpi3_nonneg]
  have hpi3_16_hi : (3 * Real.pi / 13) ^ 16 ≤ (0.72498292005918305504 : ℝ) ^ 16 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpi3_18_hi : (3 * Real.pi / 13) ^ 18 ≤ (0.72498292005918305504 : ℝ) ^ 18 := by
    nlinarith [hpi3_hi, hpi3_nonneg]
  have hpoly3_lo : (0.74851074817110109910 : ℝ) < poly16 (3 * Real.pi / 13) := by
    dsimp [poly16]
    nlinarith [hpi3_2_hi, hpi3_4_lo, hpi3_6_hi, hpi3_8_lo, hpi3_10_hi, hpi3_12_lo,
      hpi3_14_hi, hpi3_16_lo]
  have hpoly3_hi : poly16 (3 * Real.pi / 13) < (0.74851074817110109912 : ℝ) := by
    dsimp [poly16]
    nlinarith [hpi3_2_lo, hpi3_4_hi, hpi3_6_lo, hpi3_8_hi, hpi3_10_lo, hpi3_12_hi,
      hpi3_14_lo, hpi3_16_hi]
  have hrem3 : (3 * Real.pi / 13) ^ 18 * remCoeff18 < (0.00000000000000000051 : ℝ) := by
    have htmp :
        (3 * Real.pi / 13) ^ 18 * remCoeff18 ≤
          (0.72498292005918305504 : ℝ) ^ 18 * remCoeff18 := by
      have hcoeff_nonneg : 0 ≤ remCoeff18 := by
        dsimp [remCoeff18]
        positivity
      nlinarith [hpi3_18_hi, hcoeff_nonneg]
    have hconst :
        (0.72498292005918305504 : ℝ) ^ 18 * remCoeff18 <
          (0.00000000000000000051 : ℝ) := by
      dsimp [remCoeff18]
      norm_num
    exact lt_of_le_of_lt htmp hconst
  have hcos3_err := abs_cos_sub_taylor16_le (x := 3 * Real.pi / 13) hpi3_abs
  rcases
      abs_sub_le_iff.mp
        (by
          simpa [poly16, remCoeff18, abs_of_nonneg hpi3_nonneg] using hcos3_err) with
    ⟨hcos3_sub_upper, hcos3_sub_lower⟩
  have hcos3_lower :
      poly16 (3 * Real.pi / 13) - (3 * Real.pi / 13) ^ 18 * remCoeff18 ≤
        Real.cos (3 * Real.pi / 13) := by
    dsimp [poly16, remCoeff18] at hcos3_sub_lower ⊢
    apply (sub_le_iff_le_add').2
    nlinarith [hcos3_sub_lower]
  have hcos3_upper :
      Real.cos (3 * Real.pi / 13) ≤
        poly16 (3 * Real.pi / 13) + (3 * Real.pi / 13) ^ 18 * remCoeff18 := by
    dsimp [poly16, remCoeff18] at hcos3_sub_upper ⊢
    exact (sub_le_iff_le_add').1 hcos3_sub_upper
  have hcos3 :
      (0.7485107481711010986 : ℝ) < Real.cos (3 * Real.pi / 13) ∧
      Real.cos (3 * Real.pi / 13) < (0.7485107481711010997 : ℝ) := by
    constructor
    · nlinarith [hpoly3_lo, hrem3, hcos3_lower]
    · nlinarith [hpoly3_hi, hrem3, hcos3_upper]
  exact hcos3

set_option maxHeartbeats 2000000 in
private theorem cos_three_pi_div_thirteen_bounds_refined :
    (0.7485107481711010986 : ℝ) < Real.cos (3 * Real.pi / 13) ∧
    Real.cos (3 * Real.pi / 13) < (0.7485107481711010997 : ℝ) := by
  exact cos_three_pi_div_thirteen_bounds_tight

theorem phase7OneStepModelPrediction_bounds_d16 :
    (0.0003055371830425 : ℝ) < phase7OneStepModelPrediction ∧
    phase7OneStepModelPrediction < 0.0003055371830426 := by
  have hcos1 := cos_pi_div_thirteen_bounds_tight
  have hcos3 := cos_three_pi_div_thirteen_bounds_tight
  rw [phase7OneStepModelPrediction_eq_cos_pi_div_thirteen_sub_cos_three_pi_div_thirteen]
  rcases hcos1 with ⟨hcos1_lo, hcos1_hi⟩
  rcases hcos3 with ⟨hcos3_lo, hcos3_hi⟩
  constructor
  · have hnum :
        (0.9709418174260518 : ℝ) - 0.7485107481711012 <
          Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13) := by
      nlinarith
    have hdiv :
        ((0.9709418174260518 : ℝ) - 0.7485107481711012) / 728 <
          (Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13)) / 728 := by
      exact div_lt_div_of_pos_right hnum (show (0 : ℝ) < 728 by norm_num)
    have hconst :
        (0.0003055371830425 : ℝ) <
          ((0.9709418174260518 : ℝ) - 0.7485107481711012) / 728 := by
      norm_num
    exact lt_trans hconst hdiv
  · have hnum :
        Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13) <
          (0.9709418174260521 : ℝ) - 0.7485107481711005 := by
      nlinarith
    have hdiv :
        (Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13)) / 728 <
          ((0.9709418174260521 : ℝ) - 0.7485107481711005) / 728 := by
      exact div_lt_div_of_pos_right hnum (show (0 : ℝ) < 728 by norm_num)
    have hconst :
        ((0.9709418174260521 : ℝ) - 0.7485107481711005) / 728 <
          (0.0003055371830426 : ℝ) := by
      norm_num
    exact lt_trans hdiv hconst

theorem phase7OneStepModelPrediction_bounds_d18 :
    (0.000305537183042514 : ℝ) < phase7OneStepModelPrediction ∧
    phase7OneStepModelPrediction < (0.000305537183042516 : ℝ) := by
  have hcos1 := cos_pi_div_thirteen_bounds_tight
  have hcos3 := cos_three_pi_div_thirteen_bounds_tight
  rw [phase7OneStepModelPrediction_eq_cos_pi_div_thirteen_sub_cos_three_pi_div_thirteen]
  rcases hcos1 with ⟨hcos1_lo, hcos1_hi⟩
  rcases hcos3 with ⟨hcos3_lo, hcos3_hi⟩
  constructor
  · have hnum :
        (0.9709418174260518 : ℝ) - 0.7485107481711012 <
          Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13) := by
      nlinarith
    have hdiv :
        ((0.9709418174260518 : ℝ) - 0.7485107481711012) / 728 <
          (Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13)) / 728 := by
      exact div_lt_div_of_pos_right hnum (show (0 : ℝ) < 728 by norm_num)
    have hconst :
        (0.000305537183042514 : ℝ) <
          ((0.9709418174260518 : ℝ) - 0.7485107481711012) / 728 := by
      norm_num
    exact lt_trans hconst hdiv
  · have hnum :
        Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13) <
          (0.9709418174260521 : ℝ) - 0.7485107481711005 := by
      nlinarith
    have hdiv :
        (Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13)) / 728 <
          ((0.9709418174260521 : ℝ) - 0.7485107481711005) / 728 := by
      exact div_lt_div_of_pos_right hnum (show (0 : ℝ) < 728 by norm_num)
    have hconst :
        ((0.9709418174260521 : ℝ) - 0.7485107481711005) / 728 <
          (0.000305537183042516 : ℝ) := by
      norm_num
    exact lt_trans hdiv hconst

theorem phase7OneStepModelPrediction_bounds_d19 :
    (0.0003055371830425148 : ℝ) < phase7OneStepModelPrediction ∧
    phase7OneStepModelPrediction < (0.0003055371830425159 : ℝ) := by
  have hcos1 := cos_pi_div_thirteen_bounds_tight
  have hcos3 := cos_three_pi_div_thirteen_bounds_tight
  rw [phase7OneStepModelPrediction_eq_cos_pi_div_thirteen_sub_cos_three_pi_div_thirteen]
  rcases hcos1 with ⟨hcos1_lo, hcos1_hi⟩
  rcases hcos3 with ⟨hcos3_lo, hcos3_hi⟩
  constructor
  · have hnum :
        (0.970941817426052027 : ℝ) - 0.7485107481711012 <
          Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13) := by
      nlinarith
    have hdiv :
        ((0.970941817426052027 : ℝ) - 0.7485107481711012) / 728 <
          (Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13)) / 728 := by
      exact div_lt_div_of_pos_right hnum (show (0 : ℝ) < 728 by norm_num)
    have hconst :
        (0.0003055371830425148 : ℝ) <
          ((0.970941817426052027 : ℝ) - 0.7485107481711012) / 728 := by
      norm_num
    exact lt_trans hconst hdiv
  · have hnum :
        Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13) <
          (0.970941817426052028 : ℝ) - 0.7485107481711005 := by
      nlinarith
    have hdiv :
        (Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13)) / 728 <
          ((0.970941817426052028 : ℝ) - 0.7485107481711005) / 728 := by
      exact div_lt_div_of_pos_right hnum (show (0 : ℝ) < 728 by norm_num)
    have hconst :
        ((0.970941817426052028 : ℝ) - 0.7485107481711005) / 728 <
          (0.0003055371830425159 : ℝ) := by
      norm_num
    exact lt_trans hdiv hconst

theorem phase7OneStepModelPrediction_bounds_d20 :
    (0.00030553718304251501 : ℝ) < phase7OneStepModelPrediction ∧
    phase7OneStepModelPrediction < (0.00030553718304251502 : ℝ) := by
  have hcos1 := cos_pi_div_thirteen_bounds_tight
  have hcos3 := cos_three_pi_div_thirteen_bounds_tight
  rw [phase7OneStepModelPrediction_eq_cos_pi_div_thirteen_sub_cos_three_pi_div_thirteen]
  rcases hcos1 with ⟨hcos1_lo, hcos1_hi⟩
  rcases hcos3 with ⟨hcos3_lo, hcos3_hi⟩
  constructor
  · have hnum :
        (0.970941817426052027 : ℝ) - 0.7485107481711010997 <
          Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13) := by
      nlinarith
    have hdiv :
        ((0.970941817426052027 : ℝ) - 0.7485107481711010997) / 728 <
          (Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13)) / 728 := by
      exact div_lt_div_of_pos_right hnum (show (0 : ℝ) < 728 by norm_num)
    have hconst :
        (0.00030553718304251501 : ℝ) <
          ((0.970941817426052027 : ℝ) - 0.7485107481711010997) / 728 := by
      norm_num
    exact lt_trans hconst hdiv
  · have hnum :
        Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13) <
          (0.970941817426052028 : ℝ) - 0.7485107481711010986 := by
      nlinarith
    have hdiv :
        (Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13)) / 728 <
          ((0.970941817426052028 : ℝ) - 0.7485107481711010986) / 728 := by
      exact div_lt_div_of_pos_right hnum (show (0 : ℝ) < 728 by norm_num)
    have hconst :
        ((0.970941817426052028 : ℝ) - 0.7485107481711010986) / 728 <
          (0.00030553718304251502 : ℝ) := by
      norm_num
    exact lt_trans hdiv hconst

set_option maxHeartbeats 2000000 in
theorem phase7OneStepModelPrediction_bounds_d27 :
    (0.000305537183042515011706524 : ℝ) < phase7OneStepModelPrediction ∧
    phase7OneStepModelPrediction < (0.000305537183042515011706528 : ℝ) := by
  let poly20 : ℝ → ℝ := fun t =>
    1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - t ^ 10 / 3628800 +
      t ^ 12 / 479001600 - t ^ 14 / 87178291200 + t ^ 16 / 20922789888000 -
      t ^ 18 / 6402373705728000 + t ^ 20 / 2432902008176640000
  let poly20Diff : ℝ → ℝ := fun t =>
    4 * t ^ 2 - 10 * t ^ 4 / 3 + 91 * t ^ 6 / 90 - 41 * t ^ 8 / 252 +
      7381 * t ^ 10 / 453600 - 949 * t ^ 12 / 855360 +
      597871 * t ^ 14 / 10897286400 - 134521 * t ^ 16 / 65383718400 +
      532171 * t ^ 18 / 8794469376000 - 792451 * t ^ 20 / 552932274585600
  let remCoeff22 : ℝ := 23 / ((Nat.factorial 22 : ℝ) * 22)
  have hpi1_nonneg : 0 ≤ Real.pi / 13 := by positivity
  have hpi1_abs : |Real.pi / 13| ≤ 1 := by
    rw [abs_of_nonneg hpi1_nonneg]
    have hpi : Real.pi < 4 := Real.pi_lt_four
    nlinarith
  have hpi3_nonneg : 0 ≤ 3 * Real.pi / 13 := by positivity
  have hpi3_abs : |3 * Real.pi / 13| ≤ 1 := by
    rw [abs_of_nonneg hpi3_nonneg]
    have hpi : Real.pi < 4 := Real.pi_lt_four
    nlinarith
  have hpi1_lo : (0.24166097335306101834328025 : ℝ) < Real.pi / 13 := by
    have hpi : (3.1415926535897932384626433 : ℝ) < Real.pi := pi_gt_d25_ufrf
    nlinarith
  have hpi1_hi : Real.pi / 13 < (0.24166097335306101834328027 : ℝ) := by
    have hpi : Real.pi < (3.1415926535897932384626434 : ℝ) := pi_lt_d25_ufrf
    nlinarith
  have hpi3_hi : 3 * Real.pi / 13 < (0.72498292005918305502984079 : ℝ) := by
    have hpi : Real.pi < (3.1415926535897932384626434 : ℝ) := pi_lt_d25_ufrf
    nlinarith
  have hpi1_2_lo :
      (0.24166097335306101834328025 : ℝ) ^ 2 ≤ (Real.pi / 13) ^ 2 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_2_hi :
      (Real.pi / 13) ^ 2 ≤ (0.24166097335306101834328027 : ℝ) ^ 2 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_4_lo :
      (0.24166097335306101834328025 : ℝ) ^ 4 ≤ (Real.pi / 13) ^ 4 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_4_hi :
      (Real.pi / 13) ^ 4 ≤ (0.24166097335306101834328027 : ℝ) ^ 4 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_6_lo :
      (0.24166097335306101834328025 : ℝ) ^ 6 ≤ (Real.pi / 13) ^ 6 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_6_hi :
      (Real.pi / 13) ^ 6 ≤ (0.24166097335306101834328027 : ℝ) ^ 6 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_8_lo :
      (0.24166097335306101834328025 : ℝ) ^ 8 ≤ (Real.pi / 13) ^ 8 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_8_hi :
      (Real.pi / 13) ^ 8 ≤ (0.24166097335306101834328027 : ℝ) ^ 8 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_10_lo :
      (0.24166097335306101834328025 : ℝ) ^ 10 ≤ (Real.pi / 13) ^ 10 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_10_hi :
      (Real.pi / 13) ^ 10 ≤ (0.24166097335306101834328027 : ℝ) ^ 10 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_12_lo :
      (0.24166097335306101834328025 : ℝ) ^ 12 ≤ (Real.pi / 13) ^ 12 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_12_hi :
      (Real.pi / 13) ^ 12 ≤ (0.24166097335306101834328027 : ℝ) ^ 12 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_14_lo :
      (0.24166097335306101834328025 : ℝ) ^ 14 ≤ (Real.pi / 13) ^ 14 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_14_hi :
      (Real.pi / 13) ^ 14 ≤ (0.24166097335306101834328027 : ℝ) ^ 14 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_16_lo :
      (0.24166097335306101834328025 : ℝ) ^ 16 ≤ (Real.pi / 13) ^ 16 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_16_hi :
      (Real.pi / 13) ^ 16 ≤ (0.24166097335306101834328027 : ℝ) ^ 16 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_18_lo :
      (0.24166097335306101834328025 : ℝ) ^ 18 ≤ (Real.pi / 13) ^ 18 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_18_hi :
      (Real.pi / 13) ^ 18 ≤ (0.24166097335306101834328027 : ℝ) ^ 18 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_20_lo :
      (0.24166097335306101834328025 : ℝ) ^ 20 ≤ (Real.pi / 13) ^ 20 := by
    nlinarith [hpi1_lo, hpi1_nonneg]
  have hpi1_20_hi :
      (Real.pi / 13) ^ 20 ≤ (0.24166097335306101834328027 : ℝ) ^ 20 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hpi1_22_hi :
      (Real.pi / 13) ^ 22 ≤ (0.24166097335306101834328027 : ℝ) ^ 22 := by
    nlinarith [hpi1_hi, hpi1_nonneg]
  have hq_lo_base :
      (0.222431069254950928522350903 : ℝ) <
        4 * (0.24166097335306101834328025 : ℝ) ^ 2 -
          10 * (0.24166097335306101834328027 : ℝ) ^ 4 / 3 +
          91 * (0.24166097335306101834328025 : ℝ) ^ 6 / 90 -
          41 * (0.24166097335306101834328027 : ℝ) ^ 8 / 252 +
          7381 * (0.24166097335306101834328025 : ℝ) ^ 10 / 453600 -
          949 * (0.24166097335306101834328027 : ℝ) ^ 12 / 855360 +
          597871 * (0.24166097335306101834328025 : ℝ) ^ 14 / 10897286400 -
          134521 * (0.24166097335306101834328027 : ℝ) ^ 16 / 65383718400 +
          532171 * (0.24166097335306101834328025 : ℝ) ^ 18 / 8794469376000 -
          792451 * (0.24166097335306101834328027 : ℝ) ^ 20 / 552932274585600 := by
    norm_num
  have hq_lo :
      (0.222431069254950928522350903 : ℝ) < poly20Diff (Real.pi / 13) := by
    have htmp :
        4 * (0.24166097335306101834328025 : ℝ) ^ 2 -
          10 * (0.24166097335306101834328027 : ℝ) ^ 4 / 3 +
          91 * (0.24166097335306101834328025 : ℝ) ^ 6 / 90 -
          41 * (0.24166097335306101834328027 : ℝ) ^ 8 / 252 +
          7381 * (0.24166097335306101834328025 : ℝ) ^ 10 / 453600 -
          949 * (0.24166097335306101834328027 : ℝ) ^ 12 / 855360 +
          597871 * (0.24166097335306101834328025 : ℝ) ^ 14 / 10897286400 -
          134521 * (0.24166097335306101834328027 : ℝ) ^ 16 / 65383718400 +
          532171 * (0.24166097335306101834328025 : ℝ) ^ 18 / 8794469376000 -
          792451 * (0.24166097335306101834328027 : ℝ) ^ 20 / 552932274585600 ≤
        poly20Diff (Real.pi / 13) := by
      dsimp [poly20Diff]
      nlinarith [hpi1_2_lo, hpi1_4_hi, hpi1_6_lo, hpi1_8_hi, hpi1_10_lo, hpi1_12_hi,
        hpi1_14_lo, hpi1_16_hi, hpi1_18_lo, hpi1_20_hi]
    exact lt_of_lt_of_le hq_lo_base htmp
  have hq_hi_base :
      4 * (0.24166097335306101834328027 : ℝ) ^ 2 -
        10 * (0.24166097335306101834328025 : ℝ) ^ 4 / 3 +
        91 * (0.24166097335306101834328027 : ℝ) ^ 6 / 90 -
        41 * (0.24166097335306101834328025 : ℝ) ^ 8 / 252 +
        7381 * (0.24166097335306101834328027 : ℝ) ^ 10 / 453600 -
        949 * (0.24166097335306101834328025 : ℝ) ^ 12 / 855360 +
        597871 * (0.24166097335306101834328027 : ℝ) ^ 14 / 10897286400 -
        134521 * (0.24166097335306101834328025 : ℝ) ^ 16 / 65383718400 +
        532171 * (0.24166097335306101834328027 : ℝ) ^ 18 / 8794469376000 -
        792451 * (0.24166097335306101834328025 : ℝ) ^ 20 / 552932274585600 <
      (0.222431069254950928522350946 : ℝ) := by
    norm_num
  have hq_hi :
      poly20Diff (Real.pi / 13) < (0.222431069254950928522350946 : ℝ) := by
    have htmp :
        poly20Diff (Real.pi / 13) ≤
          4 * (0.24166097335306101834328027 : ℝ) ^ 2 -
            10 * (0.24166097335306101834328025 : ℝ) ^ 4 / 3 +
            91 * (0.24166097335306101834328027 : ℝ) ^ 6 / 90 -
            41 * (0.24166097335306101834328025 : ℝ) ^ 8 / 252 +
            7381 * (0.24166097335306101834328027 : ℝ) ^ 10 / 453600 -
            949 * (0.24166097335306101834328025 : ℝ) ^ 12 / 855360 +
            597871 * (0.24166097335306101834328027 : ℝ) ^ 14 / 10897286400 -
            134521 * (0.24166097335306101834328025 : ℝ) ^ 16 / 65383718400 +
            532171 * (0.24166097335306101834328027 : ℝ) ^ 18 / 8794469376000 -
            792451 * (0.24166097335306101834328025 : ℝ) ^ 20 / 552932274585600 := by
      dsimp [poly20Diff]
      nlinarith [hpi1_2_hi, hpi1_4_lo, hpi1_6_hi, hpi1_8_lo, hpi1_10_hi, hpi1_12_lo,
        hpi1_14_hi, hpi1_16_lo, hpi1_18_hi, hpi1_20_lo]
    exact lt_of_le_of_lt htmp hq_hi_base
  have hrem1 :
      (Real.pi / 13) ^ 22 * remCoeff22 < (0.0000000000000000000000000000000001 : ℝ) := by
    have htmp :
        (Real.pi / 13) ^ 22 * remCoeff22 ≤
          (0.24166097335306101834328027 : ℝ) ^ 22 * remCoeff22 := by
      have hcoeff_nonneg : 0 ≤ remCoeff22 := by
        dsimp [remCoeff22]
        positivity
      nlinarith [hpi1_22_hi, hcoeff_nonneg]
    have hconst :
        (0.24166097335306101834328027 : ℝ) ^ 22 * remCoeff22 <
          (0.0000000000000000000000000000000001 : ℝ) := by
      dsimp [remCoeff22]
      norm_num
    exact lt_of_le_of_lt htmp hconst
  have hrem3 :
      (3 * Real.pi / 13) ^ 22 * remCoeff22 < (0.00000000000000000000000079 : ℝ) := by
    have hpi3_le : 3 * Real.pi / 13 ≤ (0.72498292005918305502984079 : ℝ) := by
      linarith [hpi3_hi]
    have hpi3_22_hi :
        (3 * Real.pi / 13) ^ 22 ≤ (0.72498292005918305502984079 : ℝ) ^ 22 := by
      exact pow_le_pow_left₀ hpi3_nonneg hpi3_le 22
    have htmp :
        (3 * Real.pi / 13) ^ 22 * remCoeff22 ≤
          (0.72498292005918305502984079 : ℝ) ^ 22 * remCoeff22 := by
      have hcoeff_nonneg : 0 ≤ remCoeff22 := by
        dsimp [remCoeff22]
        positivity
      nlinarith [hpi3_22_hi, hcoeff_nonneg]
    have hconst :
        (0.72498292005918305502984079 : ℝ) ^ 22 * remCoeff22 <
          (0.00000000000000000000000079 : ℝ) := by
      dsimp [remCoeff22]
      norm_num
    exact lt_of_le_of_lt htmp hconst
  have hrem_total :
      (Real.pi / 13) ^ 22 * remCoeff22 + (3 * Real.pi / 13) ^ 22 * remCoeff22 <
        (0.0000000000000000000000008 : ℝ) := by
    nlinarith [hrem1, hrem3]
  have hcos1_err := abs_cos_sub_taylor20_le (x := Real.pi / 13) hpi1_abs
  rcases
      abs_sub_le_iff.mp
        (by
          simpa [poly20, remCoeff22, abs_of_nonneg hpi1_nonneg] using hcos1_err) with
    ⟨hcos1_sub_upper, hcos1_sub_lower⟩
  have hcos1_lower :
      poly20 (Real.pi / 13) - (Real.pi / 13) ^ 22 * remCoeff22 ≤ Real.cos (Real.pi / 13) := by
    dsimp [poly20, remCoeff22] at hcos1_sub_lower ⊢
    apply (sub_le_iff_le_add').2
    nlinarith [hcos1_sub_lower]
  have hcos1_upper :
      Real.cos (Real.pi / 13) ≤ poly20 (Real.pi / 13) + (Real.pi / 13) ^ 22 * remCoeff22 := by
    dsimp [poly20, remCoeff22] at hcos1_sub_upper ⊢
    exact (sub_le_iff_le_add').1 hcos1_sub_upper
  have hcos3_err := abs_cos_sub_taylor20_le (x := 3 * Real.pi / 13) hpi3_abs
  rcases
      abs_sub_le_iff.mp
        (by
          simpa [poly20, remCoeff22, abs_of_nonneg hpi3_nonneg] using hcos3_err) with
    ⟨hcos3_sub_upper, hcos3_sub_lower⟩
  have hcos3_lower :
      poly20 (3 * Real.pi / 13) - (3 * Real.pi / 13) ^ 22 * remCoeff22 ≤
        Real.cos (3 * Real.pi / 13) := by
    dsimp [poly20, remCoeff22] at hcos3_sub_lower ⊢
    apply (sub_le_iff_le_add').2
    nlinarith [hcos3_sub_lower]
  have hcos3_upper :
      Real.cos (3 * Real.pi / 13) ≤
        poly20 (3 * Real.pi / 13) + (3 * Real.pi / 13) ^ 22 * remCoeff22 := by
    dsimp [poly20, remCoeff22] at hcos3_sub_upper ⊢
    exact (sub_le_iff_le_add').1 hcos3_sub_upper
  have hnum_lower :
      poly20Diff (Real.pi / 13) -
          ((Real.pi / 13) ^ 22 * remCoeff22 + (3 * Real.pi / 13) ^ 22 * remCoeff22) ≤
        Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13) := by
    dsimp [poly20Diff, poly20] at hcos1_lower hcos3_upper ⊢
    nlinarith [hcos1_lower, hcos3_upper]
  have hnum_upper :
      Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13) ≤
        poly20Diff (Real.pi / 13) +
          ((Real.pi / 13) ^ 22 * remCoeff22 + (3 * Real.pi / 13) ^ 22 * remCoeff22) := by
    dsimp [poly20Diff, poly20] at hcos1_upper hcos3_lower ⊢
    nlinarith [hcos1_upper, hcos3_lower]
  rw [phase7OneStepModelPrediction_eq_cos_pi_div_thirteen_sub_cos_three_pi_div_thirteen]
  constructor
  · have hnum :
        (0.222431069254950928522350903 : ℝ) - (0.0000000000000000000000008 : ℝ) <
          Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13) := by
      nlinarith [hq_lo, hrem_total, hnum_lower]
    have hdiv :
        ((0.222431069254950928522350903 : ℝ) - (0.0000000000000000000000008 : ℝ)) / 728 <
          (Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13)) / 728 := by
      exact div_lt_div_of_pos_right hnum (show (0 : ℝ) < 728 by norm_num)
    have hconst :
        (0.000305537183042515011706524 : ℝ) <
          ((0.222431069254950928522350903 : ℝ) -
              (0.0000000000000000000000008 : ℝ)) / 728 := by
      norm_num
    exact lt_trans hconst hdiv
  · have hnum :
        Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13) <
          (0.222431069254950928522350946 : ℝ) + (0.0000000000000000000000008 : ℝ) := by
      nlinarith [hq_hi, hrem_total, hnum_upper]
    have hdiv :
        (Real.cos (Real.pi / 13) - Real.cos (3 * Real.pi / 13)) / 728 <
          ((0.222431069254950928522350946 : ℝ) +
              (0.0000000000000000000000008 : ℝ)) / 728 := by
      exact div_lt_div_of_pos_right hnum (show (0 : ℝ) < 728 by norm_num)
    have hconst :
        ((0.222431069254950928522350946 : ℝ) +
            (0.0000000000000000000000008 : ℝ)) / 728 <
          (0.000305537183042515011706528 : ℝ) := by
      norm_num
    exact lt_trans hdiv hconst

theorem phase7OneStepModelPrediction_bounds_d25 :
    (0.0003055371830425150117064 : ℝ) < phase7OneStepModelPrediction ∧
    phase7OneStepModelPrediction < (0.0003055371830425150117084 : ℝ) := by
  rcases phase7OneStepModelPrediction_bounds_d27 with ⟨hlo, hhi⟩
  constructor <;> linarith

theorem phase7OneStepModelPrediction_bounds_d24 :
    (0.000305537183042515011706 : ℝ) < phase7OneStepModelPrediction ∧
    phase7OneStepModelPrediction < (0.000305537183042515011709 : ℝ) := by
  rcases phase7OneStepModelPrediction_bounds_d25 with ⟨hlo, hhi⟩
  constructor <;> linarith

theorem phase7OneStepModelPrediction_bounds_d23 :
    (0.0003055371830425150117 : ℝ) < phase7OneStepModelPrediction ∧
    phase7OneStepModelPrediction < (0.00030553718304251501171 : ℝ) := by
  rcases phase7OneStepModelPrediction_bounds_d25 with ⟨hlo, hhi⟩
  constructor <;> linarith

theorem phase7OneStepModelPrediction_bounds_d22 :
    (0.0003055371830425150117 : ℝ) < phase7OneStepModelPrediction ∧
    phase7OneStepModelPrediction < (0.0003055371830425150118 : ℝ) := by
  rcases phase7OneStepModelPrediction_bounds_d25 with ⟨hlo, hhi⟩
  constructor <;> linarith

theorem phase7OneStepModelPrediction_bounds_d21 :
    (0.00030553718304251501169 : ℝ) < phase7OneStepModelPrediction ∧
    phase7OneStepModelPrediction < (0.00030553718304251501180 : ℝ) := by
  rcases phase7OneStepModelPrediction_bounds_d25 with ⟨hlo, hhi⟩
  constructor <;> linarith

theorem phase7OneStepModelPrediction_bounds_d12 :
    (0.0003055371830 : ℝ) < phase7OneStepModelPrediction ∧
    phase7OneStepModelPrediction < 0.0003055371832 := by
  rcases phase7OneStepModelPrediction_bounds_d13 with ⟨hlo, hhi⟩
  constructor <;> linarith

theorem phase7OneStepModelPrediction_bounds_micro :
    (0.000305520017 : ℝ) < phase7OneStepModelPrediction ∧
    phase7OneStepModelPrediction < 0.000305545269 := by
  rcases phase7OneStepModelPrediction_bounds_d13 with ⟨hlo, hhi⟩
  constructor <;> linarith

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
  simpa [alphaCodata2022Gap] using ufrf_codata2022_gap_bounds_d13

theorem alphaCodata2022Gap_rounds_to_0_000304598878 :
    |alphaCodata2022Gap - 0.000304598878| < 0.0000000000005 := by
  simpa [alphaCodata2022Gap] using ufrf_codata2022_gap_rounds_to_0_000304598878

theorem alphaCodata2022Gap_bounds_d14 :
    (0.00030459887843 : ℝ) < alphaCodata2022Gap ∧
    alphaCodata2022Gap < 0.00030459887844 := by
  simpa [alphaCodata2022Gap] using ufrf_codata2022_gap_bounds_d14

theorem alphaCodata2022Gap_bounds_d15 :
    (0.000304598878432 : ℝ) < alphaCodata2022Gap ∧
    alphaCodata2022Gap < 0.000304598878433 := by
  simpa [alphaCodata2022Gap] using ufrf_codata2022_gap_bounds_d15

theorem alphaCodata2022Gap_bounds_d16 :
    (0.0003045988784325 : ℝ) < alphaCodata2022Gap ∧
    alphaCodata2022Gap < 0.0003045988784326 := by
  simpa [alphaCodata2022Gap] using ufrf_codata2022_gap_bounds_d16

theorem alphaCodata2022Gap_bounds_d17 :
    (0.00030459887843255 : ℝ) < alphaCodata2022Gap ∧
    alphaCodata2022Gap < 0.00030459887843257 := by
  simpa [alphaCodata2022Gap] using ufrf_codata2022_gap_bounds_d17

theorem alphaCodata2022Gap_bounds_d18 :
    (0.000304598878432558 : ℝ) < alphaCodata2022Gap ∧
    alphaCodata2022Gap < 0.000304598878432561 := by
  simpa [alphaCodata2022Gap] using ufrf_codata2022_gap_bounds_d18

theorem alphaCodata2022Gap_bounds_d19 :
    (0.0003045988784325588 : ℝ) < alphaCodata2022Gap ∧
    alphaCodata2022Gap < 0.0003045988784325602 := by
  simpa [alphaCodata2022Gap] using ufrf_codata2022_gap_bounds_d19

theorem alphaCodata2022Gap_bounds_d20 :
    (0.00030459887843255887 : ℝ) < alphaCodata2022Gap ∧
    alphaCodata2022Gap < 0.00030459887843256013 := by
  simpa [alphaCodata2022Gap] using ufrf_codata2022_gap_bounds_d20

theorem alphaCodata2022Gap_bounds_d21 :
    (0.000304598878432559201 : ℝ) < alphaCodata2022Gap ∧
    alphaCodata2022Gap < 0.000304598878432559204 := by
  simpa [alphaCodata2022Gap] using ufrf_codata2022_gap_bounds_d21

theorem alphaCodata2022Gap_bounds_d25 :
    (0.0003045988784325592023841 : ℝ) < alphaCodata2022Gap ∧
    alphaCodata2022Gap < 0.0003045988784325592023968 := by
  simpa [alphaCodata2022Gap] using ufrf_codata2022_gap_bounds_d25

theorem alphaCodata2022Gap_bounds_d26 :
    (0.00030459887843255920239461 : ℝ) < alphaCodata2022Gap ∧
    alphaCodata2022Gap < 0.00030459887843255920239475 := by
  simpa [alphaCodata2022Gap] using ufrf_codata2022_gap_bounds_d26

theorem alphaCodata2022Gap_bounds_d27 :
    (0.000304598878432559202394616 : ℝ) < alphaCodata2022Gap ∧
    alphaCodata2022Gap < 0.000304598878432559202394743 := by
  simpa [alphaCodata2022Gap] using ufrf_codata2022_gap_bounds_d27

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

theorem phase7OneStepModelResidual_bounds_d12
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.0000009383044 : ℝ) < phase7OneStepModelResidual R ∧
    phase7OneStepModelResidual R < 0.0000009383048 := by
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  rcases phase7OneStepModelPrediction_bounds_d12 with ⟨hpred_lo, hpred_hi⟩
  rcases alphaCodata2022Gap_bounds_d13 with ⟨hgap_lo, hgap_hi⟩
  constructor <;> linarith

theorem phase7OneStepModelResidual_bounds_d13
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.0000009383045 : ℝ) < phase7OneStepModelResidual R ∧
    phase7OneStepModelResidual R < 0.0000009383047 := by
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  rcases phase7OneStepModelPrediction_bounds_d13 with ⟨hpred_lo, hpred_hi⟩
  rcases alphaCodata2022Gap_bounds_d13 with ⟨hgap_lo, hgap_hi⟩
  constructor <;> linarith

theorem phase7OneStepModelResidual_bounds_d14
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.00000093830460 : ℝ) < phase7OneStepModelResidual R ∧
    phase7OneStepModelResidual R < 0.00000093830462 := by
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  rcases phase7OneStepModelPrediction_bounds_d13 with ⟨hpred_lo, hpred_hi⟩
  rcases alphaCodata2022Gap_bounds_d14 with ⟨hgap_lo, hgap_hi⟩
  constructor <;> linarith

theorem phase7OneStepModelResidual_bounds_d15
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.000000938304607 : ℝ) < phase7OneStepModelResidual R ∧
    phase7OneStepModelResidual R < 0.000000938304618 := by
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  rcases phase7OneStepModelPrediction_bounds_d13 with ⟨hpred_lo, hpred_hi⟩
  rcases alphaCodata2022Gap_bounds_d15 with ⟨hgap_lo, hgap_hi⟩
  constructor <;> linarith

theorem phase7OneStepModelResidual_bounds_d16
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.0000009383046099 : ℝ) < phase7OneStepModelResidual R ∧
    phase7OneStepModelResidual R < 0.0000009383046101 := by
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  rcases phase7OneStepModelPrediction_bounds_d16 with ⟨hpred_lo, hpred_hi⟩
  rcases alphaCodata2022Gap_bounds_d16 with ⟨hgap_lo, hgap_hi⟩
  constructor <;> linarith

theorem phase7OneStepModelResidual_bounds_d17
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.00000093830460994 : ℝ) < phase7OneStepModelResidual R ∧
    phase7OneStepModelResidual R < 0.00000093830460997 := by
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  rcases phase7OneStepModelPrediction_bounds_d18 with ⟨hpred_lo, hpred_hi⟩
  rcases alphaCodata2022Gap_bounds_d17 with ⟨hgap_lo, hgap_hi⟩
  constructor <;> linarith

theorem phase7OneStepModelResidual_bounds_d18
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.000000938304609953 : ℝ) < phase7OneStepModelResidual R ∧
    phase7OneStepModelResidual R < 0.000000938304609958 := by
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  rcases phase7OneStepModelPrediction_bounds_d18 with ⟨hpred_lo, hpred_hi⟩
  rcases alphaCodata2022Gap_bounds_d18 with ⟨hgap_lo, hgap_hi⟩
  constructor <;> linarith

theorem phase7OneStepModelResidual_bounds_d19
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.0000009383046099546 : ℝ) < phase7OneStepModelResidual R ∧
    phase7OneStepModelResidual R < 0.0000009383046099571 := by
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  rcases phase7OneStepModelPrediction_bounds_d19 with ⟨hpred_lo, hpred_hi⟩
  rcases alphaCodata2022Gap_bounds_d19 with ⟨hgap_lo, hgap_hi⟩
  constructor <;> linarith

theorem phase7OneStepModelResidual_bounds_d20
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.00000093830460995488 : ℝ) < phase7OneStepModelResidual R ∧
    phase7OneStepModelResidual R < 0.00000093830460995615 := by
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  rcases phase7OneStepModelPrediction_bounds_d20 with ⟨hpred_lo, hpred_hi⟩
  rcases alphaCodata2022Gap_bounds_d20 with ⟨hgap_lo, hgap_hi⟩
  constructor <;> linarith

theorem phase7OneStepModelResidual_bounds_d21
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.000000938304609955807 : ℝ) < phase7OneStepModelResidual R ∧
    phase7OneStepModelResidual R < 0.000000938304609955811 := by
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  rcases phase7OneStepModelPrediction_bounds_d21 with ⟨hpred_lo, hpred_hi⟩
  rcases alphaCodata2022Gap_bounds_d21 with ⟨hgap_lo, hgap_hi⟩
  constructor <;> linarith

theorem phase7OneStepModelResidual_bounds_d25
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.0000009383046099558092932 : ℝ) < phase7OneStepModelResidual R ∧
    phase7OneStepModelResidual R < 0.0000009383046099558094159 := by
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  rcases phase7OneStepModelPrediction_bounds_d21 with ⟨hpred_lo, hpred_hi⟩
  rcases alphaCodata2022Gap_bounds_d25 with ⟨hgap_lo, hgap_hi⟩
  constructor <;> linarith

theorem phase7OneStepModelResidual_bounds_d26
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.00000093830460995580931173 : ℝ) < phase7OneStepModelResidual R ∧
    phase7OneStepModelResidual R < 0.00000093830460995580931192 := by
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  rcases phase7OneStepModelPrediction_bounds_d27 with ⟨hpred_lo, hpred_hi⟩
  rcases alphaCodata2022Gap_bounds_d26 with ⟨hgap_lo, hgap_hi⟩
  constructor <;> linarith

theorem phase7OneStepModelResidual_bounds_d27
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.000000938304609955809311781 : ℝ) < phase7OneStepModelResidual R ∧
    phase7OneStepModelResidual R < 0.000000938304609955809311912 := by
  rw [phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap (R := R) hR hRlt]
  rcases phase7OneStepModelPrediction_bounds_d27 with ⟨hpred_lo, hpred_hi⟩
  rcases alphaCodata2022Gap_bounds_d27 with ⟨hgap_lo, hgap_hi⟩
  constructor <;> linarith

theorem alphaPhaseObserverOneStepResidual_bounds_micro
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.000000921017 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.000000947269 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_micro (R := R) hR hRlt

theorem alphaPhaseObserverOneStepResidual_bounds_d12
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.0000009383044 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.0000009383048 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_d12 (R := R) hR hRlt

theorem alphaPhaseObserverOneStepResidual_bounds_d13
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.0000009383045 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.0000009383047 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_d13 (R := R) hR hRlt

theorem alphaPhaseObserverOneStepResidual_bounds_d14
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.00000093830460 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.00000093830462 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_d14 (R := R) hR hRlt

theorem alphaPhaseObserverOneStepResidual_bounds_d15
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.000000938304607 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.000000938304618 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_d15 (R := R) hR hRlt

theorem alphaPhaseObserverOneStepResidual_bounds_d16
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.0000009383046099 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.0000009383046101 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_d16 (R := R) hR hRlt

theorem alphaPhaseObserverOneStepResidual_bounds_d17
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.00000093830460994 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.00000093830460997 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_d17 (R := R) hR hRlt

theorem alphaPhaseObserverOneStepResidual_bounds_d18
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.000000938304609953 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.000000938304609958 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_d18 (R := R) hR hRlt

theorem alphaPhaseObserverOneStepResidual_bounds_d19
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.0000009383046099546 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.0000009383046099571 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_d19 (R := R) hR hRlt

theorem alphaPhaseObserverOneStepResidual_bounds_d20
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.00000093830460995488 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.00000093830460995615 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_d20 (R := R) hR hRlt

theorem alphaPhaseObserverOneStepResidual_bounds_d21
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.000000938304609955807 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.000000938304609955811 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_d21 (R := R) hR hRlt

theorem alphaPhaseObserverOneStepResidual_bounds_d25
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.0000009383046099558092932 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.0000009383046099558094159 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_d25 (R := R) hR hRlt

theorem alphaPhaseObserverOneStepResidual_bounds_d26
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.00000093830460995580931173 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.00000093830460995580931192 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_d26 (R := R) hR hRlt

theorem alphaPhaseObserverOneStepResidual_bounds_d27
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (0.000000938304609955809311781 : ℝ) < alphaPhaseObserverOneStepResidual R ∧
    alphaPhaseObserverOneStepResidual R < 0.000000938304609955809311912 := by
  simpa [alphaPhaseObserverOneStepResidual] using
    phase7OneStepModelResidual_bounds_d27 (R := R) hR hRlt

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

theorem alphaPhaseObserverResidueCheckAbsError_eq_modelPrediction_sub_codataGap_abs
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    alphaPhaseObserverResidueCheckAbsError =
      |phase7OneStepModelPrediction - alphaCodata2022Gap| := by
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt,
    alphaPhaseObserverOneStepResidual,
    phase7OneStepModelResidual_eq_modelPrediction_sub_codataGap
      (R := R) hR hRlt]

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

theorem alphaPhaseObserverResidueCheckAbsError_bounds_d12 :
    (0.0000009383044 : ℝ) < alphaPhaseObserverResidueCheckAbsError ∧
    alphaPhaseObserverResidueCheckAbsError < 0.0000009383048 := by
  let R : ℝ := ((Set.range breathingRoot : Set ℂ).infsep / 4)
  have hInfsepPos : 0 < (Set.range breathingRoot : Set ℂ).infsep :=
    UFRF.CircleIntegralBreathing.breathingRootSet_infsep_pos
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    dsimp [R]
    linarith
  rcases alphaPhaseObserverOneStepResidual_bounds_d12 (R := R) hR hRlt with
    ⟨hlo, hhi⟩
  have hpos : 0 < alphaPhaseObserverOneStepResidual R := by
    linarith
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt, abs_of_pos hpos]
  exact ⟨hlo, hhi⟩

theorem alphaPhaseObserverResidueCheckAbsError_bounds_d13 :
    (0.0000009383045 : ℝ) < alphaPhaseObserverResidueCheckAbsError ∧
    alphaPhaseObserverResidueCheckAbsError < 0.0000009383047 := by
  let R : ℝ := ((Set.range breathingRoot : Set ℂ).infsep / 4)
  have hInfsepPos : 0 < (Set.range breathingRoot : Set ℂ).infsep :=
    UFRF.CircleIntegralBreathing.breathingRootSet_infsep_pos
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    dsimp [R]
    linarith
  rcases alphaPhaseObserverOneStepResidual_bounds_d13 (R := R) hR hRlt with
    ⟨hlo, hhi⟩
  have hpos : 0 < alphaPhaseObserverOneStepResidual R := by
    linarith
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt, abs_of_pos hpos]
  exact ⟨hlo, hhi⟩

theorem alphaPhaseObserverResidueCheckAbsError_bounds_d14 :
    (0.00000093830460 : ℝ) < alphaPhaseObserverResidueCheckAbsError ∧
    alphaPhaseObserverResidueCheckAbsError < 0.00000093830462 := by
  let R : ℝ := ((Set.range breathingRoot : Set ℂ).infsep / 4)
  have hInfsepPos : 0 < (Set.range breathingRoot : Set ℂ).infsep :=
    UFRF.CircleIntegralBreathing.breathingRootSet_infsep_pos
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    dsimp [R]
    linarith
  rcases alphaPhaseObserverOneStepResidual_bounds_d14 (R := R) hR hRlt with
    ⟨hlo, hhi⟩
  have hpos : 0 < alphaPhaseObserverOneStepResidual R := by
    linarith
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt, abs_of_pos hpos]
  exact ⟨hlo, hhi⟩

theorem alphaPhaseObserverResidueCheckAbsError_bounds_d15 :
    (0.000000938304607 : ℝ) < alphaPhaseObserverResidueCheckAbsError ∧
    alphaPhaseObserverResidueCheckAbsError < 0.000000938304618 := by
  let R : ℝ := ((Set.range breathingRoot : Set ℂ).infsep / 4)
  have hInfsepPos : 0 < (Set.range breathingRoot : Set ℂ).infsep :=
    UFRF.CircleIntegralBreathing.breathingRootSet_infsep_pos
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    dsimp [R]
    linarith
  rcases alphaPhaseObserverOneStepResidual_bounds_d15 (R := R) hR hRlt with
    ⟨hlo, hhi⟩
  have hpos : 0 < alphaPhaseObserverOneStepResidual R := by
    linarith
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt, abs_of_pos hpos]
  exact ⟨hlo, hhi⟩

theorem alphaPhaseObserverResidueCheckAbsError_bounds_d16 :
    (0.0000009383046099 : ℝ) < alphaPhaseObserverResidueCheckAbsError ∧
    alphaPhaseObserverResidueCheckAbsError < 0.0000009383046101 := by
  let R : ℝ := ((Set.range breathingRoot : Set ℂ).infsep / 4)
  have hInfsepPos : 0 < (Set.range breathingRoot : Set ℂ).infsep :=
    UFRF.CircleIntegralBreathing.breathingRootSet_infsep_pos
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    dsimp [R]
    linarith
  rcases alphaPhaseObserverOneStepResidual_bounds_d16 (R := R) hR hRlt with
    ⟨hlo, hhi⟩
  have hpos : 0 < alphaPhaseObserverOneStepResidual R := by
    linarith
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt, abs_of_pos hpos]
  exact ⟨hlo, hhi⟩

theorem alphaPhaseObserverResidueCheckAbsError_bounds_d17 :
    (0.00000093830460994 : ℝ) < alphaPhaseObserverResidueCheckAbsError ∧
    alphaPhaseObserverResidueCheckAbsError < 0.00000093830460997 := by
  let R : ℝ := ((Set.range breathingRoot : Set ℂ).infsep / 4)
  have hInfsepPos : 0 < (Set.range breathingRoot : Set ℂ).infsep :=
    UFRF.CircleIntegralBreathing.breathingRootSet_infsep_pos
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    dsimp [R]
    linarith
  rcases alphaPhaseObserverOneStepResidual_bounds_d17 (R := R) hR hRlt with
    ⟨hlo, hhi⟩
  have hpos : 0 < alphaPhaseObserverOneStepResidual R := by
    linarith
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt, abs_of_pos hpos]
  exact ⟨hlo, hhi⟩

theorem alphaPhaseObserverResidueCheckAbsError_bounds_d18 :
    (0.000000938304609953 : ℝ) < alphaPhaseObserverResidueCheckAbsError ∧
    alphaPhaseObserverResidueCheckAbsError < 0.000000938304609958 := by
  let R : ℝ := ((Set.range breathingRoot : Set ℂ).infsep / 4)
  have hInfsepPos : 0 < (Set.range breathingRoot : Set ℂ).infsep :=
    UFRF.CircleIntegralBreathing.breathingRootSet_infsep_pos
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    dsimp [R]
    linarith
  rcases alphaPhaseObserverOneStepResidual_bounds_d18 (R := R) hR hRlt with
    ⟨hlo, hhi⟩
  have hpos : 0 < alphaPhaseObserverOneStepResidual R := by
    linarith
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt, abs_of_pos hpos]
  exact ⟨hlo, hhi⟩

theorem alphaPhaseObserverResidueCheckAbsError_bounds_d19 :
    (0.0000009383046099546 : ℝ) < alphaPhaseObserverResidueCheckAbsError ∧
    alphaPhaseObserverResidueCheckAbsError < 0.0000009383046099571 := by
  let R : ℝ := ((Set.range breathingRoot : Set ℂ).infsep / 4)
  have hInfsepPos : 0 < (Set.range breathingRoot : Set ℂ).infsep :=
    UFRF.CircleIntegralBreathing.breathingRootSet_infsep_pos
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    dsimp [R]
    linarith
  rcases alphaPhaseObserverOneStepResidual_bounds_d19 (R := R) hR hRlt with
    ⟨hlo, hhi⟩
  have hpos : 0 < alphaPhaseObserverOneStepResidual R := by
    linarith
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt, abs_of_pos hpos]
  exact ⟨hlo, hhi⟩

theorem alphaPhaseObserverResidueCheckAbsError_bounds_d20 :
    (0.00000093830460995488 : ℝ) < alphaPhaseObserverResidueCheckAbsError ∧
    alphaPhaseObserverResidueCheckAbsError < 0.00000093830460995615 := by
  let R : ℝ := ((Set.range breathingRoot : Set ℂ).infsep / 4)
  have hInfsepPos : 0 < (Set.range breathingRoot : Set ℂ).infsep :=
    UFRF.CircleIntegralBreathing.breathingRootSet_infsep_pos
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    dsimp [R]
    linarith
  rcases alphaPhaseObserverOneStepResidual_bounds_d20 (R := R) hR hRlt with
    ⟨hlo, hhi⟩
  have hpos : 0 < alphaPhaseObserverOneStepResidual R := by
    linarith
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt, abs_of_pos hpos]
  exact ⟨hlo, hhi⟩

theorem alphaPhaseObserverResidueCheckAbsError_bounds_d21 :
    (0.000000938304609955807 : ℝ) < alphaPhaseObserverResidueCheckAbsError ∧
    alphaPhaseObserverResidueCheckAbsError < 0.000000938304609955811 := by
  let R : ℝ := ((Set.range breathingRoot : Set ℂ).infsep / 4)
  have hInfsepPos : 0 < (Set.range breathingRoot : Set ℂ).infsep :=
    UFRF.CircleIntegralBreathing.breathingRootSet_infsep_pos
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    dsimp [R]
    linarith
  rcases alphaPhaseObserverOneStepResidual_bounds_d21 (R := R) hR hRlt with
    ⟨hlo, hhi⟩
  have hpos : 0 < alphaPhaseObserverOneStepResidual R := by
    linarith
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt, abs_of_pos hpos]
  exact ⟨hlo, hhi⟩

theorem alphaPhaseObserverResidueCheckAbsError_bounds_d25 :
    (0.0000009383046099558092932 : ℝ) < alphaPhaseObserverResidueCheckAbsError ∧
    alphaPhaseObserverResidueCheckAbsError < 0.0000009383046099558094159 := by
  let R : ℝ := ((Set.range breathingRoot : Set ℂ).infsep / 4)
  have hInfsepPos : 0 < (Set.range breathingRoot : Set ℂ).infsep :=
    UFRF.CircleIntegralBreathing.breathingRootSet_infsep_pos
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    dsimp [R]
    linarith
  rcases alphaPhaseObserverOneStepResidual_bounds_d25 (R := R) hR hRlt with
    ⟨hlo, hhi⟩
  have hpos : 0 < alphaPhaseObserverOneStepResidual R := by
    linarith
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt, abs_of_pos hpos]
  exact ⟨hlo, hhi⟩

theorem alphaPhaseObserverResidueCheckAbsError_bounds_d26 :
    (0.00000093830460995580931173 : ℝ) < alphaPhaseObserverResidueCheckAbsError ∧
    alphaPhaseObserverResidueCheckAbsError < 0.00000093830460995580931192 := by
  let R : ℝ := ((Set.range breathingRoot : Set ℂ).infsep / 4)
  have hInfsepPos : 0 < (Set.range breathingRoot : Set ℂ).infsep :=
    UFRF.CircleIntegralBreathing.breathingRootSet_infsep_pos
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    dsimp [R]
    linarith
  rcases alphaPhaseObserverOneStepResidual_bounds_d26 (R := R) hR hRlt with
    ⟨hlo, hhi⟩
  have hpos : 0 < alphaPhaseObserverOneStepResidual R := by
    linarith
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt, abs_of_pos hpos]
  exact ⟨hlo, hhi⟩

theorem alphaPhaseObserverResidueCheckAbsError_bounds_d27 :
    (0.000000938304609955809311781 : ℝ) < alphaPhaseObserverResidueCheckAbsError ∧
    alphaPhaseObserverResidueCheckAbsError < 0.000000938304609955809311912 := by
  let R : ℝ := ((Set.range breathingRoot : Set ℂ).infsep / 4)
  have hInfsepPos : 0 < (Set.range breathingRoot : Set ℂ).infsep :=
    UFRF.CircleIntegralBreathing.breathingRootSet_infsep_pos
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    dsimp [R]
    linarith
  rcases alphaPhaseObserverOneStepResidual_bounds_d27 (R := R) hR hRlt with
    ⟨hlo, hhi⟩
  have hpos : 0 < alphaPhaseObserverOneStepResidual R := by
    linarith
  rw [alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt, abs_of_pos hpos]
  exact ⟨hlo, hhi⟩

theorem alphaCodata2022Gap_gt_three_hundred_projection_error :
    300 * alphaPhaseObserverResidueCheckAbsError < alphaCodata2022Gap := by
  rcases alphaCodata2022Gap_bounds_d20 with ⟨hgap_lo, hgap_hi⟩
  rcases alphaPhaseObserverResidueCheckAbsError_bounds_d20 with ⟨herr_lo, herr_hi⟩
  linarith

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
The running/projection layer inherits the same scale-indexed terminal handoff:
for every whole-cycle translate, `13` is the local closure point and `14` is
the immediate re-entry point, while the recursive descent itself has no bottom
scale.

This packages unbounded descent together with the local `13 ↦ 3`, `14 ↦ 4`
handoff chart, but does not promote a stronger simultaneous-all-scales claim.
-/
theorem alpha_running_no_terminal_scale_and_handoff (s : Scale) (t : ℕ) :
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 :=
  no_first_step_and_terminal_handoff_at_scale s t

/--
The alpha-selected observer channel reaches the recurring terminal handoff.

This packages three facts adjacently:
- alpha arithmetic selects the current observer channel;
- that observer reaches closure and restart in fixed successor steps;
- the closure/restart handoff persists at every indexed scale.

It is an observer-local convenience theorem, not a stronger physical-selection
or simultaneous-all-scales claim.
-/
theorem alpha_selected_observer_reaches_recurring_handoff
    (s : Scale) (t : ℕ) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserver + 5 = (12 : ZMod CycleLen) ∧
    alphaPhaseObserver + 6 = (0 : ZMod CycleLen) ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 := by
  rcases alphaPhaseObserver_enters_terminal_handoff_in_fixed_steps with
    ⟨_, _, _, hclose, hrestart⟩
  rcases alpha_running_no_terminal_scale_and_handoff s t with
    ⟨hscale, h13, h14⟩
  exact ⟨alphaPhaseObserver_selected_by_alpha_arithmetic, hclose, hrestart, hscale, h13, h14⟩

/--
The alpha-selected observer is a contextual point on the universal PRISM orbit
before the recurring closure/restart handoff.

This packages a second exposed structural consequence adjacent to, but distinct
from, the current one-step comparison/residual/error lane:
- the universal PRISM walk from `0` reaches every cycle position;
- the arithmetic-selected observer is specifically label `7` and is reached
  after seven successor steps from the seed;
- the closure point remains the contextual `13` / local `3` / cycle `0`
  location;
- five and six more observer steps land at the recurring closure/restart
  handoff, which persists at every indexed scale with no bottom scale.

It does not promote phase `7` into an absolute origin or collapse chart-
relative facts into one absolute coordinate claim; it only places the selected
observer inside the existing scale-indexed structural geometry.
-/
theorem alpha_selected_observer_sits_on_prism_orbit_before_recurring_handoff
    (s : Scale) (t : ℕ) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserver = (7 : ZMod CycleLen) ∧
    (∀ x : BreathingCycle.CyclePos,
      ∃ n : ℕ, ((fun y : BreathingCycle.CyclePos => BreathingCycle.neg (BreathingCycle.comp y))^[n]) 0 = x) ∧
    ((fun x : BreathingCycle.CyclePos => BreathingCycle.neg (BreathingCycle.comp x))^[7]) 0 =
      (7 : BreathingCycle.CyclePos) ∧
    BreathingCycle.labeledPosition 13 = BreathingCycle.seedPosition ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition 10)
        (BreathingCycle.labeledPosition 13) = 3 ∧
    ((13 : ℕ) : BreathingCycle.CyclePos) = 0 ∧
    alphaPhaseObserver + 5 = (12 : ZMod CycleLen) ∧
    alphaPhaseObserver + 6 = (0 : ZMod CycleLen) ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 ∧
    BreathingCycle.sameStep (13 + BreathingCycle.cycle_len * t)
      (14 + BreathingCycle.cycle_len * t) 0 1 := by
  rcases prism_walk_and_terminal_handoff_at_scale s t with
    ⟨_, hwalk, _, hscale, h13, h14, hsame⟩
  rcases BreathingCycle.position_thirteen_has_contextual_coordinates with
    ⟨hseed, hlocal13, hcycle13⟩
  rcases alpha_selected_observer_reaches_recurring_handoff s t with
    ⟨hsel, hclose, hrestart, _, _, _⟩
  exact ⟨hsel, alphaPhaseObserver_eq_seven, hwalk,
    alphaPhaseObserver_is_seven_steps_on_seed_orbit, hseed, hlocal13, hcycle13,
    hclose, hrestart, hscale, h13, h14, hsame⟩

/--
The centered complex deviation itself has a local origin and sits on the same
recurring handoff as the alpha-selected observer channel.

This packages the bridge one layer earlier than the measured real observable:
- the local chart is re-anchored so the current start point is `0`,
- the observer channel is still the arithmetic-selected alpha observer,
- the centered complex deviation is the explicit alpha-selected
  root/scalar-residue quantity,
- and that same observer still sits inside the recurring `13 ↦ 3`, `14 ↦ 4`
  closure/restart handoff at every indexed scale.

It does not promote a stronger measurement-correctness or physical-selection
claim; it only places the already-proved centered complex quantity on that same
recurring-handoff channel.
-/
theorem alpha_selected_centered_deviation_has_local_origin_and_recurring_handoff
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (s : Scale) (t : ℕ) :
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t)) = 0 ∧
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaInvRunningModel n alphaPhaseObserver R -
      ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R) =
        ((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver ∧
    alphaPhaseObserver + 5 = (12 : ZMod CycleLen) ∧
    alphaPhaseObserver + 6 = (0 : ZMod CycleLen) ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 := by
  have horigin :
      BreathingCycle.localCoordinate
          (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
          (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t)) = 0 :=
    (BreathingCycle.terminal_block_handoff_reindexes_at_scale t).1
  have hdev :=
    alphaPhaseObserverDeviationFromAverage_eq_alpha_selected_scalar_mul_residueCandidate
      (n := n) (R := R) hR hRlt
  rcases alpha_selected_observer_reaches_recurring_handoff s t with
    ⟨hsel, hclose, hrestart, hscale, h13, h14⟩
  exact ⟨horigin, hsel, hdev, hclose, hrestart, hscale, h13, h14⟩

/--
The unnormalized real selected-observer correction has a local origin, is
stable under allowed contour-radius changes, and sits on the same recurring
handoff as the alpha-selected observer channel.

This packages an earlier exposed observer-side quantity than the current `/ 28`
measurement rule:
- the local chart is re-anchored so the current start point is `0`,
- the observer channel is still the arithmetic-selected alpha observer,
- the real correction is both the real part of the centered running deviation
  and the real part of the explicit alpha-selected root/scalar-residue
  quantity,
- that real correction is unchanged when the contour radius varies from `r` to
  `R` in the admitted regime,
- and the same observer still sits inside the recurring `13 ↦ 3`, `14 ↦ 4`
  closure/restart handoff at every indexed scale.

It does not promote a stronger measurement-correctness, unique-normalization,
or physical-selection claim; it only packages the current unnormalized
observer-side real quantity on that same arithmetic-selected recurring-handoff
channel.
-/
theorem alpha_selected_real_correction_has_local_origin_radius_invariance_and_recurring_handoff
    (n : ℤ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (s : Scale) (t : ℕ) :
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t)) = 0 ∧
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverRealCorrection n R =
      Complex.re
        (alphaInvRunningModel n alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R)) ∧
    alphaPhaseObserverRealCorrection n R =
      Complex.re
        (((n : ℂ) * ((midpointWeight : ℂ) * standardModePhaseShift)) *
          UFRF.ResidueDefinition.residueCandidateAt alphaPhaseObserver) ∧
    alphaPhaseObserverRealCorrection n R = alphaPhaseObserverRealCorrection n r ∧
    alphaPhaseObserver + 5 = (12 : ZMod CycleLen) ∧
    alphaPhaseObserver + 6 = (0 : ZMod CycleLen) ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 := by
  have horigin :
      BreathingCycle.localCoordinate
          (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
          (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t)) = 0 :=
    (BreathingCycle.terminal_block_handoff_reindexes_at_scale t).1
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have hcenter :=
    alphaPhaseObserverRealCorrection_eq_re_deviationFromAverage
      (n := n) (R := R) hR hRlt
  have hroot :=
    alphaPhaseObserverRealCorrection_eq_re_alpha_selected_scalar_mul_residueCandidate
      (n := n) (R := R) hR hRlt
  have hinvar :
      alphaPhaseObserverRealCorrection n R = alphaPhaseObserverRealCorrection n r :=
    alphaPhaseObserverRealCorrection_eq_of_le_lt_half_infsep
      (n := n) (r := r) (R := R) hr hrR hRlt
  rcases alpha_selected_observer_reaches_recurring_handoff s t with
    ⟨hsel, hclose, hrestart, hscale, h13, h14⟩
  exact ⟨horigin, hsel, hcenter, hroot, hinvar, hclose, hrestart, hscale, h13, h14⟩

/--
The centered observer-local observable now also packages the conserved-average
story, allowed-radius stability, and the recurring handoff in one theorem.

This is a broader observer/measurement-side consequence than the one-step
CODATA bundle:
- the local chart is re-anchored so the current start point is `0`,
- the observer channel is still the arithmetic-selected alpha observer,
- the all-root average of the running model still collapses back to the static
  UFRF value,
- the centered observable is the normalized real part of the selected
  observer's deviation from that global average,
- that centered observable is unchanged when the contour radius varies from `r`
  to `R` in the admitted regime,
- and the same observer still sits inside the recurring `13 ↦ 3`, `14 ↦ 4`
  closure/restart handoff at every indexed scale.

It does not promote a stronger unique-normalization, measurement-correctness,
or physical-selection claim; it only packages the current conserved-average
observer-side story on that same arithmetic-selected recurring-handoff
channel.
-/
theorem alpha_selected_centered_observable_global_average_package_has_local_origin_radius_invariance_and_recurring_handoff
    (n : ℤ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (s : Scale) (t : ℕ) :
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t)) = 0 ∧
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R) = ufrf_alpha_inv ∧
    alphaPhaseObserverNormalizedRealCorrection n R =
      Complex.re
        (alphaInvRunningModel n alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R)) / 28 ∧
    alphaPhaseObserverNormalizedRealCorrection n R =
      alphaPhaseObserverNormalizedRealCorrection n r ∧
    alphaPhaseObserver + 5 = (12 : ZMod CycleLen) ∧
    alphaPhaseObserver + 6 = (0 : ZMod CycleLen) ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 := by
  have horigin :
      BreathingCycle.localCoordinate
          (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
          (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t)) = 0 :=
    (BreathingCycle.terminal_block_handoff_reindexes_at_scale t).1
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have havg :=
    avg_alphaInvRunningModel_allRoots_eq_static
      (n := n) (R := R) hR hRlt
  have hobs :=
    alphaPhaseObserverNormalizedRealCorrection_eq_re_deviationFromAverage_div_twenty_eight
      (n := n) (R := R) hR hRlt
  have hinvar :
      alphaPhaseObserverNormalizedRealCorrection n R =
        alphaPhaseObserverNormalizedRealCorrection n r :=
    alphaPhaseObserverNormalizedRealCorrection_eq_of_le_lt_half_infsep
      (n := n) (r := r) (R := R) hr hrR hRlt
  rcases alpha_selected_observer_reaches_recurring_handoff s t with
    ⟨hsel, hclose, hrestart, hscale, h13, h14⟩
  exact ⟨horigin, hsel, havg, hobs, hinvar, hclose, hrestart, hscale, h13, h14⟩

/--
The exposed centered observable itself sits on the same recurring handoff as
the alpha-selected observer channel.

This is the current repo-supported arbitrary-step bridge from the centered
measurement-side quantity back to the centerless recurring-handoff package:
- the normalized real centered observable is written at the arithmetic-selected
  observer channel,
- the selected observer still reaches closure/restart in fixed successor steps,
- and that same closure/restart handoff persists at every indexed scale.

It does not add a stronger physical-selection or measurement-correctness claim;
it only packages the already-proved centered observable on that same
arithmetic-selected recurring-handoff channel.
-/
theorem alpha_selected_centered_observable_reaches_recurring_handoff
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (s : Scale) (t : ℕ) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection n R =
      Complex.re
        (alphaInvRunningModel n alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R)) /
        alphaPhaseObserverModelNormalization ∧
    alphaPhaseObserver + 5 = (12 : ZMod CycleLen) ∧
    alphaPhaseObserver + 6 = (0 : ZMod CycleLen) ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 := by
  rcases alphaPhaseObserverNormalizedRealCorrection_is_alpha_selected_centered_comparison
      (n := n) (R := R) hR hRlt with ⟨hsel, hobs⟩
  rcases alpha_selected_observer_reaches_recurring_handoff s t with
    ⟨_, hclose, hrestart, hscale, h13, h14⟩
  exact ⟨hsel, hobs, hclose, hrestart, hscale, h13, h14⟩

/--
The centered observer-local measurement package has a local origin and the same
recurring handoff law.

This packages the user-facing structural reading in one theorem:
- the local chart is re-anchored so the current start point is `0`,
- the observer channel is the arithmetic-selected alpha observer,
- the measurement rule is the normalized real part of the centered observable,
- and the same observer still sits inside the recurring `13 ↦ 3`, `14 ↦ 4`
  closure/restart handoff at every indexed scale.

It does not promote a stronger claim that every possible measurement rule is
equivalent, or that the current rule is uniquely physically correct. It only
packages the current exposed rule on that same recurring-handoff channel.
-/
theorem alpha_selected_centered_observable_has_local_origin_and_recurring_handoff
    (n : ℤ) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (s : Scale) (t : ℕ) :
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t)) = 0 ∧
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection n R =
      Complex.re
        (alphaInvRunningModel n alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel n k R)) / 28 ∧
    alphaPhaseObserver + 5 = (12 : ZMod CycleLen) ∧
    alphaPhaseObserver + 6 = (0 : ZMod CycleLen) ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 := by
  have horigin :
      BreathingCycle.localCoordinate
          (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
          (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t)) = 0 :=
    (BreathingCycle.terminal_block_handoff_reindexes_at_scale t).1
  have hmeas :=
    alphaPhaseObserverNormalizedRealCorrection_eq_re_deviationFromAverage_div_twenty_eight
      (n := n) (R := R) hR hRlt
  rcases alpha_selected_observer_reaches_recurring_handoff s t with
    ⟨hsel, hclose, hrestart, hscale, h13, h14⟩
  exact ⟨horigin, hsel, hmeas, hclose, hrestart, hscale, h13, h14⟩

/--
The centered observer-local measurement package has a local origin, is stable
under allowed contour-radius changes, and still sits on the same recurring
handoff law.

This packages the measurement-side stability statement now supported by the
repo:
- the local chart is re-anchored so the current start point is `0`,
- the observer channel is still the arithmetic-selected alpha observer,
- the exposed centered observable is invariant under allowed radius changes,
- and the same observer still sits inside the recurring `13 ↦ 3`, `14 ↦ 4`
  closure/restart handoff at every indexed scale.

It does not promote a stronger claim that every measurement rule is equivalent
or uniquely correct; it only packages the current exposed centered observable
and its allowed-radius stability on that same recurring-handoff channel.
-/
theorem alpha_selected_centered_observable_has_local_origin_radius_invariance_and_recurring_handoff
    (n : ℤ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (s : Scale) (t : ℕ) :
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t)) = 0 ∧
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection n R =
      alphaPhaseObserverNormalizedRealCorrection n r ∧
    alphaPhaseObserver + 5 = (12 : ZMod CycleLen) ∧
    alphaPhaseObserver + 6 = (0 : ZMod CycleLen) ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 := by
  have horigin :
      BreathingCycle.localCoordinate
          (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
          (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t)) = 0 :=
    (BreathingCycle.terminal_block_handoff_reindexes_at_scale t).1
  have hinvar :
      alphaPhaseObserverNormalizedRealCorrection n R =
        alphaPhaseObserverNormalizedRealCorrection n r :=
    alphaPhaseObserverNormalizedRealCorrection_eq_of_le_lt_half_infsep
      (n := n) (r := r) (R := R) hr hrR hRlt
  rcases alpha_selected_observer_reaches_recurring_handoff s t with
    ⟨hsel, hclose, hrestart, hscale, h13, h14⟩
  exact ⟨horigin, hsel, hinvar, hclose, hrestart, hscale, h13, h14⟩

/--
The exposed observer-indexed comparison package sits on the same recurring
handoff as the alpha-selected channel.

This is the current repo-supported bridge from the centerless recurring-handoff
layer to the exposed measurement-side quantities:
- the one-step comparison is the alpha-selected centered observable;
- the one-step residual is that same centered quantity after subtracting the
  static CODATA gap;
- the selected observer still reaches closure/restart inside the recurring
  handoff package at every indexed scale.

It does not prove a stronger physical-selection or measurement-correctness
claim; it only packages the current exposed comparison quantities on that same
arithmetic-selected recurring-handoff channel.
-/
theorem alpha_selected_comparison_and_residual_reach_recurring_handoff
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (s : Scale) (t : ℕ) :
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverOneStepComparison =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) /
        alphaPhaseObserverModelNormalization ∧
    alphaPhaseObserverOneStepResidual R =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) /
        alphaPhaseObserverModelNormalization - alphaCodata2022Gap ∧
    alphaPhaseObserver + 5 = (12 : ZMod CycleLen) ∧
    alphaPhaseObserver + 6 = (0 : ZMod CycleLen) ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 := by
  rcases alpha_selected_centered_observable_reaches_recurring_handoff
      (n := 1) (R := R) hR hRlt s t with
    ⟨hsel, hcmp0, hclose, hrestart, hscale, h13, h14⟩
  have hcmp :
      alphaPhaseObserverOneStepComparison =
        Complex.re
          (alphaInvRunningModel 1 alphaPhaseObserver R -
            ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) /
          alphaPhaseObserverModelNormalization := by
    calc
      alphaPhaseObserverOneStepComparison = alphaPhaseObserverNormalizedRealCorrection 1 R := by
        symm
        exact alphaPhaseObserverNormalizedRealCorrection_one_eq_oneStepComparison
          (R := R) hR hRlt
      _ = Complex.re
            (alphaInvRunningModel 1 alphaPhaseObserver R -
              ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) /
            alphaPhaseObserverModelNormalization := hcmp0
  rcases alphaPhaseObserverOneStepResidual_eq_alpha_selected_centered_comparison_sub_codataGap
      (R := R) hR hRlt with ⟨_, hres⟩
  exact ⟨hsel, hcmp, hres, hclose, hrestart, hscale, h13, h14⟩

/--
The current one-step measurement package has a local origin and sits on the
same recurring handoff as the alpha-selected observer channel.

This is the smallest current one-step user-facing bundle in one theorem:
- the local chart is re-anchored so the current start point is `0`,
- the observer channel is still the arithmetic-selected alpha observer,
- the exposed one-step measurement rule is the normalized real part of the
  centered observable with explicit `/ 28` normalization,
- the one-step comparison alias is exactly that same quantity,
- the one-step residual alias is that same quantity minus the static CODATA
  gap,
- and the same observer still sits inside the recurring `13 ↦ 3`, `14 ↦ 4`
  closure/restart handoff at every indexed scale.

It does not promote a stronger measurement-correctness or physical-selection
claim; it only packages the current one-step observable aliases on that same
arithmetic-selected recurring-handoff channel.
-/
theorem alpha_selected_one_step_measurement_package_has_local_origin_and_recurring_handoff
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (s : Scale) (t : ℕ) :
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t)) = 0 ∧
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection 1 R =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) / 28 ∧
    alphaPhaseObserverOneStepComparison =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) / 28 ∧
    alphaPhaseObserverOneStepResidual R =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) / 28 -
        alphaCodata2022Gap ∧
    alphaPhaseObserver + 5 = (12 : ZMod CycleLen) ∧
    alphaPhaseObserver + 6 = (0 : ZMod CycleLen) ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 := by
  rcases alpha_selected_centered_observable_has_local_origin_and_recurring_handoff
      (n := 1) (R := R) hR hRlt s t with
    ⟨horigin, hsel, hmeas, hclose, hrestart, hscale, h13, h14⟩
  have hcmp :
      alphaPhaseObserverOneStepComparison =
        Complex.re
          (alphaInvRunningModel 1 alphaPhaseObserver R -
            ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) / 28 := by
    calc
      alphaPhaseObserverOneStepComparison = alphaPhaseObserverNormalizedRealCorrection 1 R := by
        symm
        exact alphaPhaseObserverNormalizedRealCorrection_one_eq_oneStepComparison
          (R := R) hR hRlt
      _ =
        Complex.re
          (alphaInvRunningModel 1 alphaPhaseObserver R -
            ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) / 28 := hmeas
  have hres :
      alphaPhaseObserverOneStepResidual R =
        Complex.re
          (alphaInvRunningModel 1 alphaPhaseObserver R -
            ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) / 28 -
          alphaCodata2022Gap := by
    calc
      alphaPhaseObserverOneStepResidual R =
          alphaPhaseObserverOneStepComparison - alphaCodata2022Gap := by
        exact alphaPhaseObserverOneStepResidual_eq_oneStepComparison_sub_codataGap
          (R := R) hR hRlt
      _ =
          Complex.re
            (alphaInvRunningModel 1 alphaPhaseObserver R -
              ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) / 28 -
            alphaCodata2022Gap := by
          rw [hcmp]
  exact ⟨horigin, hsel, hmeas, hcmp, hres, hclose, hrestart, hscale, h13, h14⟩

/--
The current one-step measurement package has a local origin, is stable under
allowed contour-radius changes, and sits on the same recurring handoff as the
alpha-selected observer channel.

This is the current one-step radius-stability bundle in one theorem:
- the local chart is re-anchored so the current start point is `0`,
- the observer channel is still the arithmetic-selected alpha observer,
- the exposed one-step measurement rule is still the normalized real part of
  the centered observable with explicit `/ 28` normalization,
- that exposed one-step measurement is unchanged when the contour radius moves
  from `r` to `R` in the admitted regime,
- the one-step comparison alias is exactly that same quantity,
- the one-step residual alias is that same quantity minus the static CODATA
  gap and is likewise unchanged when the contour radius moves from `r` to `R`,
- and the same observer still sits inside the recurring `13 ↦ 3`, `14 ↦ 4`
  closure/restart handoff at every indexed scale.

It does not promote a stronger measurement-correctness or physical-selection
claim; it only packages the current one-step observable aliases and their
allowed-radius stability on that same arithmetic-selected recurring-handoff
channel.
-/
theorem alpha_selected_one_step_measurement_package_has_local_origin_radius_invariance_and_recurring_handoff
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (s : Scale) (t : ℕ) :
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t)) = 0 ∧
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection 1 R =
      alphaPhaseObserverNormalizedRealCorrection 1 r ∧
    alphaPhaseObserverNormalizedRealCorrection 1 R =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) / 28 ∧
    alphaPhaseObserverOneStepComparison =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) / 28 ∧
    alphaPhaseObserverOneStepResidual R = alphaPhaseObserverOneStepResidual r ∧
    alphaPhaseObserverOneStepResidual R =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) / 28 -
        alphaCodata2022Gap ∧
    alphaPhaseObserver + 5 = (12 : ZMod CycleLen) ∧
    alphaPhaseObserver + 6 = (0 : ZMod CycleLen) ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 := by
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  rcases alpha_selected_one_step_measurement_package_has_local_origin_and_recurring_handoff
      (R := R) hR hRlt s t with
    ⟨horigin, hsel, hmeas, hcmp, hres, hclose, hrestart, hscale, h13, h14⟩
  have hinvarMeas :
      alphaPhaseObserverNormalizedRealCorrection 1 R =
        alphaPhaseObserverNormalizedRealCorrection 1 r :=
    alphaPhaseObserverNormalizedRealCorrection_eq_of_le_lt_half_infsep
      (n := 1) (r := r) (R := R) hr hrR hRlt
  have hinvarRes :
      alphaPhaseObserverOneStepResidual R = alphaPhaseObserverOneStepResidual r :=
    alphaPhaseObserverOneStepResidual_eq_of_le_lt_half_infsep
      (r := r) (R := R) hr hrR hRlt
  exact ⟨horigin, hsel, hinvarMeas, hmeas, hcmp, hinvarRes, hres,
    hclose, hrestart, hscale, h13, h14⟩

/--
The current one-step absolute-error package has a local origin and sits on the
same recurring handoff as the alpha-selected observer channel.

This extends the current one-step user-facing package by adding the
script-aligned absolute-error identity:
- the local chart is re-anchored so the current start point is `0`,
- the observer channel is still the arithmetic-selected alpha observer,
- the exposed one-step measurement rule is still the normalized real part of
  the centered observable with explicit `/ 28` normalization,
- the one-step comparison alias is exactly that same quantity,
- the one-step residual alias is that same quantity minus the static CODATA
  gap,
- the absolute error is exactly the absolute value of that one-step residual,
- and the same observer still sits inside the recurring `13 ↦ 3`, `14 ↦ 4`
  closure/restart handoff at every indexed scale.

It does not promote a stronger measurement-correctness or physical-selection
claim; it only packages the current one-step observable and absolute-error
aliases on that same arithmetic-selected recurring-handoff channel.
-/
theorem alpha_selected_one_step_absolute_error_package_has_local_origin_and_recurring_handoff
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (s : Scale) (t : ℕ) :
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t)) = 0 ∧
    (Int.floor ufrf_alpha_inv : ZMod CycleLen) = alphaPhaseObserver ∧
    alphaPhaseObserverNormalizedRealCorrection 1 R =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) / 28 ∧
    alphaPhaseObserverOneStepComparison =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) / 28 ∧
    alphaPhaseObserverOneStepResidual R =
      Complex.re
        (alphaInvRunningModel 1 alphaPhaseObserver R -
          ((13 : ℂ)⁻¹) * (∑ k : ZMod CycleLen, alphaInvRunningModel 1 k R)) / 28 -
        alphaCodata2022Gap ∧
    alphaPhaseObserverResidueCheckAbsError = |alphaPhaseObserverOneStepResidual R| ∧
    alphaPhaseObserver + 5 = (12 : ZMod CycleLen) ∧
    alphaPhaseObserver + 6 = (0 : ZMod CycleLen) ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 := by
  rcases alpha_selected_one_step_measurement_package_has_local_origin_and_recurring_handoff
      (R := R) hR hRlt s t with
    ⟨horigin, hsel, hmeas, hcmp, hres, hclose, hrestart, hscale, h13, h14⟩
  have herr :
      alphaPhaseObserverResidueCheckAbsError = |alphaPhaseObserverOneStepResidual R| :=
    alphaPhaseObserverResidueCheckAbsError_eq_oneStepResidual_abs
      (R := R) hR hRlt
  exact ⟨horigin, hsel, hmeas, hcmp, hres, herr, hclose, hrestart, hscale, h13, h14⟩

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

/--
The running/projection layer packages the nested start-and-handoff picture in
one place.

It keeps the claims separate but adjacent:
- the `13`-adic tower is coherent across finite depths;
- the exposed UFRF start pattern is `1` and then `13` subpositions;
- the cycle-side seed move is the literal `0 -> 1` step;
- there is no bottom scale;
- every whole-cycle translate still closes at local `3` and re-enters at local
  `4`.

This is a bundled scale-indexed package, not a coinductive simultaneous-all-
scales object.
-/
theorem alpha_running_coherent_start_and_handoff
    (s : Scale) (t : ℕ) (x : ℤ_[13]) :
    IsCoherent 13 (fun n => PadicInt.toZModPow n x) ∧
    UFRF.Padic.ufrf_projection (1 : ℤ_[13]) = (1 : ZMod 13) ∧
    Fintype.card (ZMod (13 ^ 2)) / Fintype.card (ZMod 13) = 13 ∧
    BreathingCycle.neg (BreathingCycle.comp 0) = (1 : BreathingCycle.CyclePos) ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 := by
  rcases ufrf_start_pattern with ⟨hstart, hbranch⟩
  rcases alpha_running_no_terminal_scale_and_handoff s t with ⟨hscale, hclose, hreenter⟩
  exact ⟨padic_is_coherent (p := 13) x, hstart, hbranch, cycle_seed_zero_to_one,
    hscale, hclose, hreenter⟩

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

/--
The current three-layer concurrency reading is mirrored here from `Recursion`.

The structural package itself now lives lower in
`prism_walk_and_terminal_handoff_at_scale`; this running-layer theorem keeps
the same statement available next to the observer/measurement bridge cluster
without promoting it into an observer-specific claim.
-/
theorem alpha_running_three_layer_concurrency_package
    (s : Scale) (t : ℕ) :
    BreathingCycle.neg (BreathingCycle.comp 0) = (1 : BreathingCycle.CyclePos) ∧
    (∀ x : BreathingCycle.CyclePos,
      ∃ n : ℕ, ((fun y : BreathingCycle.CyclePos => BreathingCycle.neg (BreathingCycle.comp y))^[n]) 0 = x) ∧
    ((13 : ℕ) : BreathingCycle.CyclePos) = 0 ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 ∧
    BreathingCycle.sameStep (13 + BreathingCycle.cycle_len * t)
      (14 + BreathingCycle.cycle_len * t) 0 1 :=
  prism_walk_and_terminal_handoff_at_scale s t

end UFRF.AlphaRunning
