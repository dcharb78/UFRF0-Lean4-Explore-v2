import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt
import UFRF.BreathingCycle
import UFRF.Constants
import UFRF.DoublingFlip
import UFRF.KeplerTriangle

/-!
# UFRF.NestedLearning

Named theorem surface for the Nested Learning outreach thread.

The claims here are intentionally structural: they expose results already
supported by UFRF cycle arithmetic, the UFRF-specific prime predicate, the
Kepler-derived rest amplitude, and the continuous flip theorem. The module does
not assert ML-side folklore or hide informal claims inside theorem names.
-/

noncomputable section

namespace UFRF.NestedLearning

open UFRF.Constants

/-! ## Tau-tier ceilings -/

/-- The 13-cycle length, kept tied to the existing UFRF derivation. -/
def cycleLength : ℕ := BreathingCycle.cycle_len

/-- Proven provenance for `cycleLength`. -/
theorem cycleLength_eq_13 : cycleLength = 13 := by
  unfold cycleLength
  exact BreathingCycle.cycle_has_13_positions

/-- Tier error term: one unresolved cell over `p` copies of the 13-cycle, phi-weighted. -/
def tauTierError (p : ℕ) : ℝ :=
  1 / ((p : ℝ) * (cycleLength : ℝ) * phi)

/-- Achievable tier ceiling after removing the phi-weighted unresolved cell. -/
def tauTierCeiling (p : ℕ) : ℝ :=
  1 - tauTierError p

/--
The top-level tau-tier ceiling formula.

This theorem is the citable form: the cycle length is not assumed here; it is
rewritten through `BreathingCycle.cycle_has_13_positions`.
-/
theorem tau_tier_ceiling (p : ℕ) :
    tauTierCeiling p = 1 - 1 / ((p : ℝ) * 13 * phi) := by
  unfold tauTierCeiling tauTierError cycleLength
  rw [BreathingCycle.cycle_has_13_positions]
  norm_num

/-- `2` is the mediator tier in UFRF, not a UFRF prime tier. -/
theorem M2_is_mediator_not_ufrf_prime : ¬ is_ufrf_prime 2 := by
  unfold is_ufrf_prime
  norm_num

/-- The M2 mediator ceiling formula. -/
theorem tau_ceiling_M2 :
    tauTierCeiling 2 = 1 - 1 / ((2 : ℝ) * 13 * phi) :=
  tau_tier_ceiling 2

/-- The M3 UFRF-prime ceiling formula. -/
theorem tau_ceiling_M3 :
    tauTierCeiling 3 = 1 - 1 / ((3 : ℝ) * 13 * phi) :=
  tau_tier_ceiling 3

/-- The M5 UFRF-prime ceiling formula. -/
theorem tau_ceiling_M5 :
    tauTierCeiling 5 = 1 - 1 / ((5 : ℝ) * 13 * phi) :=
  tau_tier_ceiling 5

private theorem sqrt5_lower : ((559 : ℝ) / 250) < Real.sqrt 5 := by
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 559 / 250)]
  norm_num

private theorem sqrt5_upper : Real.sqrt 5 < ((2237 : ℝ) / 1000) := by
  rw [Real.sqrt_lt
    (by norm_num : (0 : ℝ) ≤ 5)
    (by norm_num : (0 : ℝ) ≤ 2237 / 1000)]
  norm_num

private theorem phi_lower : ((809 : ℝ) / 500) < phi := by
  unfold phi
  linarith [sqrt5_lower]

private theorem phi_upper : phi < ((3237 : ℝ) / 2000) := by
  unfold phi
  linarith [sqrt5_upper]

/-- M2 mediator ceiling lies in the 97.62% to 97.63% window. -/
theorem tau_ceiling_M2_percent_window :
    (9762 : ℝ) / 10000 < tauTierCeiling 2 ∧
      tauTierCeiling 2 < (9763 : ℝ) / 10000 := by
  constructor
  · unfold tauTierCeiling tauTierError cycleLength
    rw [BreathingCycle.cycle_has_13_positions]
    have hden : (5000 : ℝ) / 119 < (2 : ℝ) * 13 * phi := by
      nlinarith [phi_lower]
    have hrec : 1 / ((2 : ℝ) * 13 * phi) < 1 / ((5000 : ℝ) / 119) := by
      exact one_div_lt_one_div_of_lt
        (by norm_num : (0 : ℝ) < 5000 / 119) hden
    norm_num at hrec ⊢
    linarith
  · unfold tauTierCeiling tauTierError cycleLength
    rw [BreathingCycle.cycle_has_13_positions]
    have hden_pos : 0 < (2 : ℝ) * 13 * phi := by
      nlinarith [phi_lower]
    have hden : (2 : ℝ) * 13 * phi < (10000 : ℝ) / 237 := by
      nlinarith [phi_upper]
    have hrec : 1 / ((10000 : ℝ) / 237) < 1 / ((2 : ℝ) * 13 * phi) := by
      exact one_div_lt_one_div_of_lt hden_pos hden
    norm_num at hrec ⊢
    linarith

/-- M3 UFRF-prime ceiling lies in the 98.41% to 98.42% window. -/
theorem tau_ceiling_M3_percent_window :
    (9841 : ℝ) / 10000 < tauTierCeiling 3 ∧
      tauTierCeiling 3 < (9842 : ℝ) / 10000 := by
  constructor
  · unfold tauTierCeiling tauTierError cycleLength
    rw [BreathingCycle.cycle_has_13_positions]
    have hden : (10000 : ℝ) / 159 < (3 : ℝ) * 13 * phi := by
      nlinarith [phi_lower]
    have hrec : 1 / ((3 : ℝ) * 13 * phi) < 1 / ((10000 : ℝ) / 159) := by
      exact one_div_lt_one_div_of_lt
        (by norm_num : (0 : ℝ) < 10000 / 159) hden
    norm_num at hrec ⊢
    linarith
  · unfold tauTierCeiling tauTierError cycleLength
    rw [BreathingCycle.cycle_has_13_positions]
    have hden_pos : 0 < (3 : ℝ) * 13 * phi := by
      nlinarith [phi_lower]
    have hden : (3 : ℝ) * 13 * phi < (5000 : ℝ) / 79 := by
      nlinarith [phi_upper]
    have hrec : 1 / ((5000 : ℝ) / 79) < 1 / ((3 : ℝ) * 13 * phi) := by
      exact one_div_lt_one_div_of_lt hden_pos hden
    norm_num at hrec ⊢
    linarith

/-- M5 UFRF-prime ceiling lies in the 99.04% to 99.05% window. -/
theorem tau_ceiling_M5_percent_window :
    (9904 : ℝ) / 10000 < tauTierCeiling 5 ∧
      tauTierCeiling 5 < (9905 : ℝ) / 10000 := by
  constructor
  · unfold tauTierCeiling tauTierError cycleLength
    rw [BreathingCycle.cycle_has_13_positions]
    have hden : (625 : ℝ) / 6 < (5 : ℝ) * 13 * phi := by
      nlinarith [phi_lower]
    have hrec : 1 / ((5 : ℝ) * 13 * phi) < 1 / ((625 : ℝ) / 6) := by
      exact one_div_lt_one_div_of_lt
        (by norm_num : (0 : ℝ) < 625 / 6) hden
    norm_num at hrec ⊢
    linarith
  · unfold tauTierCeiling tauTierError cycleLength
    rw [BreathingCycle.cycle_has_13_positions]
    have hden_pos : 0 < (5 : ℝ) * 13 * phi := by
      nlinarith [phi_lower]
    have hden : (5 : ℝ) * 13 * phi < (2000 : ℝ) / 19 := by
      nlinarith [phi_upper]
    have hrec : 1 / ((2000 : ℝ) / 19) < 1 / ((5 : ℝ) * 13 * phi) := by
      exact one_div_lt_one_div_of_lt hden_pos hden
    norm_num at hrec ⊢
    linarith

/-! ## Nested octave closure -/

/-- The transition edge between bridge and seed is the Kepler-derived rest amplitude. -/
def nestedTransitionWeight : ℝ := rest_amplitude

/--
Bridge positions 11, 12, and 13 of one 13-cycle become seed positions 1, 2,
and 3 of the next cycle under the three-step octave transition.

Lean uses zero-based `ZMod 13` indices, so this is the one-based statement
`Bridge(11,13) -> Seed(1,3)`.
-/
theorem nested_octave_closure :
    ((10 : BreathingCycle.CyclePos) + 3 = 0) ∧
      ((11 : BreathingCycle.CyclePos) + 3 = 1) ∧
      ((12 : BreathingCycle.CyclePos) + 3 = 2) ∧
      nestedTransitionWeight = Real.sqrt phi := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  unfold nestedTransitionWeight
  exact rest_is_sqrt_phi

/-! ## Prime frequency separation -/

/-- The mediator update frequency. It is deliberately not a UFRF-prime frequency. -/
def mediatorFrequency : ℕ := 2

/-- The named UFRF-prime update frequencies used by the nested-learning surface. -/
def ufrfPrimeFrequencies : List ℕ := [3, 5, 7, 11, 13]

/--
The named UFRF update frequencies separate the mediator `2` from UFRF primes,
and the UFRF-prime frequencies are pairwise distinct.
-/
theorem prime_frequency_separation :
    ¬ is_ufrf_prime 2 ∧
      is_ufrf_prime 3 ∧ is_ufrf_prime 5 ∧ is_ufrf_prime 7 ∧
      is_ufrf_prime 11 ∧ is_ufrf_prime 13 ∧
      List.Pairwise (· ≠ ·) [3, 5, 7, 11, 13] := by
  unfold is_ufrf_prime
  norm_num

/--
The reusable frequency-set form of `prime_frequency_separation`.

The mediator frequency is outside the UFRF-prime frequency list; every listed
frequency satisfies the UFRF-specific prime predicate; and the listed
frequencies are pairwise distinct.
-/
theorem prime_frequency_set_separates_mediator :
    mediatorFrequency ∉ ufrfPrimeFrequencies ∧
      (∀ n, n ∈ ufrfPrimeFrequencies → is_ufrf_prime n) ∧
      List.Pairwise (· ≠ ·) ufrfPrimeFrequencies := by
  unfold mediatorFrequency ufrfPrimeFrequencies
  refine ⟨by decide, ?_, by decide⟩
  intro n hn
  simp only [List.mem_cons, List.mem_nil_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | hfalse
  · unfold is_ufrf_prime
    norm_num
  · unfold is_ufrf_prime
    norm_num
  · unfold is_ufrf_prime
    norm_num
  · unfold is_ufrf_prime
    norm_num
  · unfold is_ufrf_prime
    norm_num
  · cases hfalse

/-! ## Epsilon at the flip -/

/-- The unresolved tau complement. -/
def epsilonResidual : ℝ := 1 - tau

/-- The flip absorption edge uses the same Kepler-derived rest amplitude. -/
def flipAbsorptionWeight : ℝ := rest_amplitude

/--
Structural epsilon-at-flip statement.

This proves only what the current formal vocabulary supports: epsilon is the
tau complement, the flip is exactly the half-cycle position, and the associated
edge weight is the Kepler-derived `sqrt(phi)`.
-/
theorem epsilon_at_flip_position :
    epsilonResidual = tau_complement ∧
      UFRF.DoublingFlip.fp = (13 : ℝ) / 2 ∧
      UFRF.DoublingFlip.fp / 13 = 1 / 2 ∧
      flipAbsorptionWeight = Real.sqrt phi := by
  refine ⟨?_, UFRF.DoublingFlip.fp_eq_core_midpoint,
    UFRF.DoublingFlip.fp_normalized_eq_half, ?_⟩
  · unfold epsilonResidual tau tau_complement
    norm_num
  · unfold flipAbsorptionWeight
    exact rest_is_sqrt_phi

/-! ## Closure at 13 -/

/-- Adding the full 13-cycle returns every nested-octave position to itself. -/
theorem mobius_closure_at_13 (p : BreathingCycle.CyclePos) :
    p + (13 : BreathingCycle.CyclePos) = p := by
  rw [BreathingCycle.full_cycle_identity]
  simp

end UFRF.NestedLearning
