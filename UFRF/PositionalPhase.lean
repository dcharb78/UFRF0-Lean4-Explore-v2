import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import UFRF.Constants

set_option linter.unnecessarySeqFocus false

/-!
# UFRF.PositionalPhase

**Position vs Accounting: Phase from Prime Values**

From the Ideas folder (conversation.txt, lines ~836–976):
The fundamental error in conventional analysis is using array
indices (accounting) instead of prime values (position) for phase offsets.

The phase for prime p on the 13-cycle is `p/13 × 2π`.
This is POSITIONAL — it comes from where the prime IS, not
which slot it occupies in a list.

**The Golden Angle Discovery:**
Position 5 gives phase 5/13 of the full circle.
5/13 ≈ 0.38462... ≈ 1/φ² ≈ 0.38197...

The golden angle (137.508°) is 1/φ² of the full circle (360°).
So 5/13 ≈ 1/φ² — the golden angle EMERGES from position 5's
geometric phase. It was never imposed. It was always there.

## Status
- All theorems: ✅ PROVEN
-/

namespace UFRF.PositionalPhase

open UFRF.Constants
open Real

/-! ## Position-Based Phase -/

/--
**Positional phase of prime p on the 13-cycle.**

The phase is p/13 of the full circle. This is the prime's
GEOMETRIC position, not its index in a list.
-/
noncomputable def positional_phase (p : ℕ) : ℝ := (p : ℝ) / 13

/--
**Positional phases of the five cycle-prime naturals.**

Each prime has a distinct phase. Note how they span the circle
non-uniformly — the spacing IS the geometry.

✅ PROVEN
-/
theorem phase_values :
    positional_phase 3 = 3 / 13 ∧
    positional_phase 5 = 5 / 13 ∧
    positional_phase 7 = 7 / 13 ∧
    positional_phase 11 = 11 / 13 ∧
    positional_phase 13 = 1 := by
  unfold positional_phase
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

/-! ## Golden Angle Emergence -/

/--
**The golden ratio reciprocal squared.**

1/φ² = (3 - √5) / 2. This is the fraction of the circle
corresponding to the golden angle (≈ 137.508°).
-/
noncomputable def inv_phi_sq : ℝ := 1 / (phi ^ 2)

/--
**Position 5 approximates 1/φ² with error < 0.003.**

|5/13 - 1/φ²| < 0.003

This is the key emergence result: the golden angle isn't imposed
on the 13-cycle. It appears BECAUSE prime 5 sits at position 5,
and 5/13 happens to be within 0.27% of 1/φ².

The golden angle was always encoded in the cycle geometry.
We just couldn't see it because we were using accounting (index 2
in the prime list) instead of position (value 5 in the cycle).

✅ PROVEN
-/
theorem golden_angle_emergence :
    |positional_phase 5 - inv_phi_sq| < 3 / 1000 := by
  unfold positional_phase inv_phi_sq phi
  -- Bounds on √5 (same pattern as GoldenAngle.lean)
  have h_sqrt5_lo : 2.236 < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)] <;> norm_num
  have h_sqrt5_hi : Real.sqrt 5 < 2.237 := by
    rw [Real.sqrt_lt (by norm_num)] <;> norm_num
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  have h_pos : 0 < 3 + Real.sqrt 5 := add_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))
  -- φ² = (3+√5)/2, so 1/φ² = 2/(3+√5)
  have h_phi_sq : ((1 + Real.sqrt 5) / 2) ^ 2 = (3 + Real.sqrt 5) / 2 := by
    ring_nf; linarith
  rw [h_phi_sq]
  -- Now goal: |↑5 / 13 - 1 / ((3 + √5) / 2)| < 3 / 1000
  -- Simplify 1/((3+√5)/2) = 2/(3+√5)
  have h_half_pos : (0:ℝ) < (3 + Real.sqrt 5) / 2 := by positivity
  rw [one_div, inv_div]
  -- Now goal: |↑5 / 13 - 2 / (3 + √5)| < 3 / 1000
  rw [abs_sub_lt_iff]
  constructor
  · -- 5/13 - 3/1000 < 2/(3+√5)
    field_simp [ne_of_gt h_pos]
    push_cast
    nlinarith
  · -- 2/(3+√5) < 5/13 + 3/1000
    field_simp [ne_of_gt h_pos]
    push_cast
    nlinarith

/-! ## Phase Independence -/

/--
**The five cycle-prime naturals have distinct positional phases.**

No two primes share the same position in the cycle.
This is trivially true since distinct primes have distinct
values, but stating it explicitly connects position to phase.

✅ PROVEN
-/
theorem phases_are_distinct :
    positional_phase 3 ≠ positional_phase 5 ∧
    positional_phase 3 ≠ positional_phase 7 ∧
    positional_phase 3 ≠ positional_phase 11 ∧
    positional_phase 5 ≠ positional_phase 7 ∧
    positional_phase 5 ≠ positional_phase 11 ∧
    positional_phase 7 ≠ positional_phase 11 := by
  unfold positional_phase
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ## Observer Phase: 13 = 0 -/

/--
**The observer's positional phase is exactly 1 (= 0, full circle).**

Prime 13 at position 13 has phase 13/13 = 1 ≡ 0.
The observer completes the full circle and returns to the origin.
This is the algebraic counterpart of `observer_is_void` in PRISMAlgebra:
(13 : ZMod 13) = 0.

✅ PROVEN
-/
theorem observer_phase_is_unity :
    positional_phase 13 = 1 := by
  unfold positional_phase
  norm_num

end UFRF.PositionalPhase
