import Mathlib.Tactic
import UFRF.BreathingCycle
import UFRF.Constants

/-!
# UFRF.DoublingFlip

Frequency doubling crosses the 13-cycle flip point exactly when a position
starts below the midpoint and its double lands above it.

This module keeps the physical input separate from the structural statement:
the flip point is anchored to existing UFRF Core theorems
`BreathingCycle.flip_at_half` and `UFRF.Constants.flip_is_midpoint`, while the
chirality map and doubling map are local definitions for continuous phonon
positions in the open cycle.
-/

noncomputable section

namespace UFRF.DoublingFlip

/-- The continuous flip point: the midpoint of the 13-position cycle. -/
def fp : ℝ := 6.5

/-- Core provenance: the local flip point is the UFRF midpoint theorem. -/
theorem fp_eq_core_midpoint : fp = (13 : ℝ) / 2 := by
  unfold fp
  exact UFRF.Constants.flip_is_midpoint

/-- Core provenance: normalized by cycle length, the flip point is one half. -/
theorem fp_normalized_eq_half : fp / 13 = 1 / 2 := by
  unfold fp
  exact BreathingCycle.flip_at_half

/--
Chirality on continuous positions.

Positions below the flip point are assigned `-1`, positions above it are
assigned `1`, and the exact flip boundary is assigned `0`.
-/
def chirality (p : ℝ) : ℤ :=
  if p < fp then -1 else if p > fp then 1 else 0

/-- Frequency doubling in one continuous 13-cycle chart. -/
def double (p : ℝ) : ℝ := 2 * p

theorem chirality_of_lt_fp {p : ℝ} (h : p < fp) : chirality p = -1 := by
  unfold chirality
  simp [h]

theorem chirality_of_gt_fp {p : ℝ} (h : fp < p) : chirality p = 1 := by
  unfold chirality
  have h_not_lt : ¬ p < fp := not_lt.mpr (le_of_lt h)
  simp [h_not_lt, h]

theorem chirality_of_eq_fp {p : ℝ} (h : p = fp) : chirality p = 0 := by
  rw [h]
  unfold chirality
  simp

theorem chirality_eq_neg_one_iff (p : ℝ) :
    chirality p = -1 ↔ p < fp := by
  unfold chirality
  by_cases h_lt : p < fp
  · simp [h_lt]
  · by_cases h_gt : p > fp
    · simp [h_lt, h_gt]
    · simp [h_lt, h_gt]

theorem chirality_eq_one_iff (p : ℝ) :
    chirality p = 1 ↔ fp < p := by
  unfold chirality
  by_cases h_lt : p < fp
  · have h_not_gt : ¬ fp < p := not_lt.mpr (le_of_lt h_lt)
    simp [h_lt, h_not_gt]
  · by_cases h_gt : p > fp
    · simp [h_lt, h_gt]
    · simp [h_lt, h_gt]

/--
If a position is below the flip point, and its double is above the flip point
while remaining inside the 13-cycle chart, the two chiralities are opposite.
-/
theorem chirality_flips_under_doubling
    (p : ℝ)
    (_h_pos : 0 < p)
    (h_below_flip : p < fp)
    (h_double_above_flip : fp < 2 * p)
    (_h_in_cycle : 2 * p < 13) :
    chirality p = -1 ∧ chirality (double p) = 1 := by
  refine ⟨chirality_of_lt_fp h_below_flip, ?_⟩
  apply chirality_of_gt_fp
  simpa [double] using h_double_above_flip

/-- Strict flip-crossing forces a genuine chirality change. -/
theorem chirality_reversal
    (p : ℝ)
    (h_pos : 0 < p)
    (h_below_flip : p < fp)
    (h_double_above_flip : fp < 2 * p)
    (h_in_cycle : 2 * p < 13) :
    chirality p ≠ chirality (double p) := by
  obtain ⟨h1, h2⟩ :=
    chirality_flips_under_doubling p h_pos h_below_flip
      h_double_above_flip h_in_cycle
  rw [h1, h2]
  norm_num

/--
The strict sign-reversal window for doubling is exactly `(fp / 2, fp)`.

This avoids the boundary ambiguity at `p = fp / 2`: there, the doubled position
lands exactly on the flip point and has chirality `0`, not `1`.
-/
theorem flip_window_characterization (p : ℝ) :
    chirality p = -1 ∧ chirality (double p) = 1 ↔ fp / 2 < p ∧ p < fp := by
  constructor
  · rintro ⟨h_p, h_double⟩
    have h_p_lt : p < fp := (chirality_eq_neg_one_iff p).mp h_p
    have h_double_gt : fp < double p := (chirality_eq_one_iff (double p)).mp h_double
    constructor
    · unfold double at h_double_gt
      linarith
    · exact h_p_lt
  · rintro ⟨h_lo, h_hi⟩
    constructor
    · exact (chirality_eq_neg_one_iff p).mpr h_hi
    · apply (chirality_eq_one_iff (double p)).mpr
      unfold double
      linarith

/--
The Bi2Se3 experimental numbers: the 2 THz mode at position `5.56` doubles to
the 4 THz mode at position `11.12`, crossing the 6.5 flip point.
-/
example :
    let p_Eu : ℝ := 5.56
    let p_Eg : ℝ := 11.12
    p_Eg = double p_Eu ∧ chirality p_Eu ≠ chirality p_Eg := by
  refine ⟨by norm_num [double], ?_⟩
  norm_num [chirality, fp]

end UFRF.DoublingFlip
