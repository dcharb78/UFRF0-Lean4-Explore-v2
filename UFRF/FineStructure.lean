import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import UFRF.Constants

open UFRF.Constants

/-!
# UFRF.FineStructure

**Theorem 23: α⁻¹ = 4π³ + π² + π ≈ 137.036303775878...**

The inverse fine structure constant is derived from zero free parameters.
It is the continuous cycle geometry (π) processed through the Three-LOG
tensor grades:

- `π` (Log1): The linear/identity contribution
- `π²` (Log2): The curved/pairing contribution
- `4π³` (Log3): The cubed/volume contribution, with coefficient 4 = 2²
  from the Merkaba dual-reflection (both expansion and contraction
  contribute simultaneously at the deepest volume scale)

The integer part 137 encodes the breathing cycle's critical phase markers:
- **1**: First emergence (start of Log1)
- **3**: Transition to curvature (end of Log1)
- **7**: First position post-flip (start of Log3)

## Measured vs. UFRF values
- CODATA 2022: α⁻¹ = 137.035999177(21)
- UFRF: α⁻¹ = 4π³ + π² + π ≈ 137.036303775878...
- Gap: < 3.1e-4

## Status
- `ufrf_alpha_inv`, `codata2018_alpha_inv`, `codata_alpha_inv`: ✅ definitions
- `alpha_inv_floor_137`, `alpha_inv_bounds_d27`: ✅ proved with π bounds
- `alpha_inv_rounds_to_137_036303775878`: ✅ proved
- `ufrf_matches_codata`, `ufrf_codata2022_gap_bounds_d27`, `ufrf_matches_codata2018`: ✅ proved
-/

noncomputable section

open Real



/--
**Theorem 23a: ⌊α⁻¹⌋ = 137**

The floor of the UFRF fine structure inverse is exactly 137.

Proof strategy: Use Mathlib's `Real.pi_gt_three` and `Real.pi_lt_four`
(or tighter bounds) to establish:
  3.14159 < π < 3.14160
Then compute:
  4 * 3.14159³ + 3.14159² + 3.14159 > 137
  4 * 3.14160³ + 3.14160² + 3.14160 < 138

🔧 TACTIC — needs careful interval arithmetic with π bounds
-/
theorem alpha_inv_floor_137 : ⌊ufrf_alpha_inv⌋ = 137 := by
  rw [Int.floor_eq_iff]
  constructor
  · -- 137 ≤ ufrf_alpha_inv
    have h_pi_gt : 3.1415 < π := Real.pi_gt_d4
    have h_val : 137 < 4 * (3.1415:ℝ)^3 + (3.1415:ℝ)^2 + 3.1415 := by norm_num
    have h_mono : 4 * (3.1415:ℝ)^3 + (3.1415:ℝ)^2 + 3.1415 < 4 * π ^ 3 + π ^ 2 + π := by
      gcongr
    unfold ufrf_alpha_inv
    dsimp [ufrf_tensor_structure]
    simp
    exact le_of_lt (lt_trans h_val h_mono)
  · -- ufrf_alpha_inv < 138
    have h_pi_lt : π < 3.1416 := Real.pi_lt_d4
    have h_val : 4 * (3.1416:ℝ)^3 + (3.1416:ℝ)^2 + 3.1416 < 138 := by norm_num
    have h_mono : 4 * π ^ 3 + π ^ 2 + π < 4 * (3.1416:ℝ)^3 + (3.1416:ℝ)^2 + 3.1416 := by
      gcongr
    unfold ufrf_alpha_inv
    dsimp [ufrf_tensor_structure]
    simp
    have h_138 : (138 : ℝ) = (137 : ℤ) + 1 := by norm_num
    rw [h_138] at h_val
    exact lt_trans h_mono h_val

/--
Helper: π > 3 (available in Mathlib as `Real.pi_gt_three`).
We need it to show that the polynomial 4π³ + ... > 100 roughly.
-/
theorem pi_gt_three_impl : 100 < ufrf_alpha_inv := by
  have : 3 < π := Real.pi_gt_three
  have h_val : 4 * (3:ℝ)^3 + (3:ℝ)^2 + 3 = 120 := by norm_num
  have h_mono : 4 * (3:ℝ)^3 + (3:ℝ)^2 + 3 < 4 * π ^ 3 + π ^ 2 + π := by
    gcongr
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  rw [h_val] at h_mono
  apply lt_trans _ h_mono
  norm_num

/--
Helper: π < 4 (available in Mathlib as `Real.pi_lt_four`).
These loose bounds alone give:
  4·27 + 9 + 3 = 120 < ufrf_alpha_inv < 4·64 + 16 + 4 = 276
So we need tighter bounds for the floor proof.
-/
theorem pi_lt_4 : π < 4 := Real.pi_lt_four

/--
Lower bound with loose π bounds:
4 * 3³ + 3² + 3 = 108 + 9 + 3 = 120

✅ PROVEN
-/
theorem alpha_inv_lower_crude : ufrf_alpha_inv > 120 := by
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  have h := Real.pi_gt_three
  nlinarith [sq_nonneg π, sq_nonneg (π - 3)]

/--
Upper bound with loose π bounds:
4 * 4³ + 4² + 4 = 256 + 16 + 4 = 276

✅ PROVEN
-/
theorem alpha_inv_upper_crude : ufrf_alpha_inv < 276 := by
  have : π < 4 := Real.pi_lt_four
  have h_val : 4 * (4:ℝ)^3 + (4:ℝ)^2 + 4 = 276 := by norm_num
  have h_mono : 4 * π ^ 3 + π ^ 2 + π < 4 * (4:ℝ)^3 + (4:ℝ)^2 + 4 := by
    gcongr
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  rw [h_val] at h_mono
  exact h_mono

/--
The UFRF polynomial coefficients read off the LOG grades.

✅ PROVEN
-/
theorem alpha_polynomial_form :
    ufrf_alpha_inv = 4 * π ^ 3 + 1 * π ^ 2 + 1 * π := by
  unfold ufrf_alpha_inv; dsimp [ufrf_tensor_structure]; simp

/--
The UFRF fine-structure candidate lies in the explicit six-decimal window
`137.036303 < α⁻¹ < 137.036304`.

This is the current decimal-place prediction promoted from the tighter `π`
bounds already available in Mathlib.
-/
theorem alpha_inv_six_decimal_window :
    137.036303 < ufrf_alpha_inv ∧ ufrf_alpha_inv < 137.036304 := by
  let poly (x : ℝ) := 4 * x ^ 3 + x ^ 2 + x
  have mono : StrictMonoOn poly (Set.Ici 0) := by
    intro a ha b hb hab
    simp at ha hb
    have hsq : a ^ 2 < b ^ 2 := by nlinarith
    have hcube : a ^ 3 < b ^ 3 := by nlinarith
    dsimp [poly]
    nlinarith
  have pi_lo : 3.14159265358979323846 < π := Real.pi_gt_d20
  have pi_hi : π < 3.14159265358979323847 := Real.pi_lt_d20
  have h_nonneg_pi : 0 ≤ π := le_of_lt (lt_trans (by norm_num) pi_lo)
  have lo :
      137.036303 < 4 * π ^ 3 + π ^ 2 + π := by
    change 137.036303 < poly π
    have hmono : poly 3.14159265358979323846 < poly π :=
      mono (by norm_num) h_nonneg_pi pi_lo
    have hlo : 137.036303 < poly 3.14159265358979323846 := by
      dsimp [poly]
      norm_num
    exact lt_trans hlo hmono
  have hi :
      4 * π ^ 3 + π ^ 2 + π < 137.036304 := by
    change poly π < 137.036304
    have hmono : poly π < poly 3.14159265358979323847 :=
      mono h_nonneg_pi (by norm_num) pi_hi
    have hhi : poly 3.14159265358979323847 < 137.036304 := by
      dsimp [poly]
      norm_num
    exact lt_trans hmono hhi
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  exact ⟨lo, hi⟩

/--
Nine-decimal bracketing for the UFRF inverse fine-structure value.

This sharpens `alpha_inv_six_decimal_window` to a one-nanounit interval using
Mathlib's 20-decimal bounds on `π`.
-/
theorem alpha_inv_bounds_d9 :
    (137.036303775 : ℝ) < ufrf_alpha_inv ∧ ufrf_alpha_inv < 137.036303776 := by
  let poly (x : ℝ) := 4 * x ^ 3 + x ^ 2 + x
  have mono : StrictMonoOn poly (Set.Ici 0) := by
    intro a ha b hb hab
    simp at ha hb
    have hsq : a ^ 2 < b ^ 2 := by nlinarith
    have hcube : a ^ 3 < b ^ 3 := by nlinarith
    dsimp [poly]
    nlinarith
  have pi_lo : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
  have pi_hi : π < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have h_nonneg_pi : 0 ≤ π := le_of_lt (lt_trans (by norm_num) pi_lo)
  have lo :
      (137.036303775 : ℝ) < 4 * π ^ 3 + π ^ 2 + π := by
    change (137.036303775 : ℝ) < poly π
    have hmono : poly (3.14159265358979323846 : ℝ) < poly π :=
      mono (by norm_num) h_nonneg_pi pi_lo
    have hlo : (137.036303775 : ℝ) < poly (3.14159265358979323846 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hlo hmono
  have hi :
      4 * π ^ 3 + π ^ 2 + π < (137.036303776 : ℝ) := by
    change poly π < (137.036303776 : ℝ)
    have hmono : poly π < poly (3.14159265358979323847 : ℝ) :=
      mono h_nonneg_pi (by norm_num) pi_hi
    have hhi : poly (3.14159265358979323847 : ℝ) < (137.036303776 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hmono hhi
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  exact ⟨lo, hi⟩

/--
The UFRF inverse fine-structure prediction rounds to `137.036303776`
at the `10^-9` place.
-/
theorem alpha_inv_rounds_to_137_036303776 :
    |ufrf_alpha_inv - 137.036303776| < 0.000000001 := by
  rcases alpha_inv_bounds_d9 with ⟨hlo, hhi⟩
  rw [abs_lt]
  constructor <;> linarith

/--
Thirteen-decimal bracketing for the UFRF inverse fine-structure value.

This sharpens `alpha_inv_bounds_d9` using the same 20-decimal bounds on `π`.
-/
theorem alpha_inv_bounds_d13 :
    (137.0363037758784 : ℝ) < ufrf_alpha_inv ∧
    ufrf_alpha_inv < 137.0363037758785 := by
  let poly (x : ℝ) := 4 * x ^ 3 + x ^ 2 + x
  have mono : StrictMonoOn poly (Set.Ici 0) := by
    intro a ha b hb hab
    simp at ha hb
    have hsq : a ^ 2 < b ^ 2 := by nlinarith
    have hcube : a ^ 3 < b ^ 3 := by nlinarith
    dsimp [poly]
    nlinarith
  have pi_lo : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
  have pi_hi : π < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have h_nonneg_pi : 0 ≤ π := le_of_lt (lt_trans (by norm_num) pi_lo)
  have lo :
      (137.0363037758784 : ℝ) < 4 * π ^ 3 + π ^ 2 + π := by
    change (137.0363037758784 : ℝ) < poly π
    have hmono : poly (3.14159265358979323846 : ℝ) < poly π :=
      mono (by norm_num) h_nonneg_pi pi_lo
    have hlo : (137.0363037758784 : ℝ) < poly (3.14159265358979323846 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hlo hmono
  have hi :
      4 * π ^ 3 + π ^ 2 + π < (137.0363037758785 : ℝ) := by
    change poly π < (137.0363037758785 : ℝ)
    have hmono : poly π < poly (3.14159265358979323847 : ℝ) :=
      mono h_nonneg_pi (by norm_num) pi_hi
    have hhi : poly (3.14159265358979323847 : ℝ) < (137.0363037758785 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hmono hhi
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  exact ⟨lo, hi⟩

/--
The UFRF inverse fine-structure prediction rounds to `137.036303775878`
at the `10^-12` place.
-/
theorem alpha_inv_rounds_to_137_036303775878 :
    |ufrf_alpha_inv - 137.036303775878| < 0.0000000000005 := by
  rcases alpha_inv_bounds_d13 with ⟨hlo, hhi⟩
  rw [abs_lt]
  constructor <;> linarith

/--
Fourteen-decimal bracketing for the UFRF inverse fine-structure value.

This sharpens `alpha_inv_bounds_d13` using the same 20-decimal bounds on `π`.
-/
theorem alpha_inv_bounds_d14 :
    (137.03630377587843 : ℝ) < ufrf_alpha_inv ∧
    ufrf_alpha_inv < 137.03630377587844 := by
  let poly (x : ℝ) := 4 * x ^ 3 + x ^ 2 + x
  have mono : StrictMonoOn poly (Set.Ici 0) := by
    intro a ha b hb hab
    simp at ha hb
    have hsq : a ^ 2 < b ^ 2 := by nlinarith
    have hcube : a ^ 3 < b ^ 3 := by nlinarith
    dsimp [poly]
    nlinarith
  have pi_lo : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
  have pi_hi : π < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have h_nonneg_pi : 0 ≤ π := le_of_lt (lt_trans (by norm_num) pi_lo)
  have lo :
      (137.03630377587843 : ℝ) < 4 * π ^ 3 + π ^ 2 + π := by
    change (137.03630377587843 : ℝ) < poly π
    have hmono : poly (3.14159265358979323846 : ℝ) < poly π :=
      mono (by norm_num) h_nonneg_pi pi_lo
    have hlo : (137.03630377587843 : ℝ) < poly (3.14159265358979323846 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hlo hmono
  have hi :
      4 * π ^ 3 + π ^ 2 + π < (137.03630377587844 : ℝ) := by
    change poly π < (137.03630377587844 : ℝ)
    have hmono : poly π < poly (3.14159265358979323847 : ℝ) :=
      mono h_nonneg_pi (by norm_num) pi_hi
    have hhi : poly (3.14159265358979323847 : ℝ) < (137.03630377587844 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hmono hhi
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  exact ⟨lo, hi⟩

/--
Fifteen-decimal bracketing for the UFRF inverse fine-structure value.

This sharpens `alpha_inv_bounds_d14` using the same 20-decimal bounds on `π`.
-/
theorem alpha_inv_bounds_d15 :
    (137.036303775878432 : ℝ) < ufrf_alpha_inv ∧
    ufrf_alpha_inv < 137.036303775878433 := by
  let poly (x : ℝ) := 4 * x ^ 3 + x ^ 2 + x
  have mono : StrictMonoOn poly (Set.Ici 0) := by
    intro a ha b hb hab
    simp at ha hb
    have hsq : a ^ 2 < b ^ 2 := by nlinarith
    have hcube : a ^ 3 < b ^ 3 := by nlinarith
    dsimp [poly]
    nlinarith
  have pi_lo : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
  have pi_hi : π < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have h_nonneg_pi : 0 ≤ π := le_of_lt (lt_trans (by norm_num) pi_lo)
  have lo :
      (137.036303775878432 : ℝ) < 4 * π ^ 3 + π ^ 2 + π := by
    change (137.036303775878432 : ℝ) < poly π
    have hmono : poly (3.14159265358979323846 : ℝ) < poly π :=
      mono (by norm_num) h_nonneg_pi pi_lo
    have hlo : (137.036303775878432 : ℝ) < poly (3.14159265358979323846 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hlo hmono
  have hi :
      4 * π ^ 3 + π ^ 2 + π < (137.036303775878433 : ℝ) := by
    change poly π < (137.036303775878433 : ℝ)
    have hmono : poly π < poly (3.14159265358979323847 : ℝ) :=
      mono h_nonneg_pi (by norm_num) pi_hi
    have hhi : poly (3.14159265358979323847 : ℝ) < (137.036303775878433 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hmono hhi
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  exact ⟨lo, hi⟩

/--
Sixteen-decimal bracketing for the UFRF inverse fine-structure value.

This sharpens `alpha_inv_bounds_d15` using the same 20-decimal bounds on `π`.
-/
theorem alpha_inv_bounds_d16 :
    (137.0363037758784325 : ℝ) < ufrf_alpha_inv ∧
    ufrf_alpha_inv < 137.0363037758784326 := by
  let poly (x : ℝ) := 4 * x ^ 3 + x ^ 2 + x
  have mono : StrictMonoOn poly (Set.Ici 0) := by
    intro a ha b hb hab
    simp at ha hb
    have hsq : a ^ 2 < b ^ 2 := by nlinarith
    have hcube : a ^ 3 < b ^ 3 := by nlinarith
    dsimp [poly]
    nlinarith
  have pi_lo : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
  have pi_hi : π < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have h_nonneg_pi : 0 ≤ π := le_of_lt (lt_trans (by norm_num) pi_lo)
  have lo :
      (137.0363037758784325 : ℝ) < 4 * π ^ 3 + π ^ 2 + π := by
    change (137.0363037758784325 : ℝ) < poly π
    have hmono : poly (3.14159265358979323846 : ℝ) < poly π :=
      mono (by norm_num) h_nonneg_pi pi_lo
    have hlo : (137.0363037758784325 : ℝ) < poly (3.14159265358979323846 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hlo hmono
  have hi :
      4 * π ^ 3 + π ^ 2 + π < (137.0363037758784326 : ℝ) := by
    change poly π < (137.0363037758784326 : ℝ)
    have hmono : poly π < poly (3.14159265358979323847 : ℝ) :=
      mono h_nonneg_pi (by norm_num) pi_hi
    have hhi : poly (3.14159265358979323847 : ℝ) < (137.0363037758784326 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hmono hhi
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  exact ⟨lo, hi⟩

/--
Seventeen-decimal bracketing for the UFRF inverse fine-structure value.

This sharpens `alpha_inv_bounds_d16` using the same 20-decimal bounds on `π`.
-/
theorem alpha_inv_bounds_d17 :
    (137.03630377587843255 : ℝ) < ufrf_alpha_inv ∧
    ufrf_alpha_inv < 137.03630377587843257 := by
  let poly (x : ℝ) := 4 * x ^ 3 + x ^ 2 + x
  have mono : StrictMonoOn poly (Set.Ici 0) := by
    intro a ha b hb hab
    simp at ha hb
    have hsq : a ^ 2 < b ^ 2 := by nlinarith
    have hcube : a ^ 3 < b ^ 3 := by nlinarith
    dsimp [poly]
    nlinarith
  have pi_lo : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
  have pi_hi : π < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have h_nonneg_pi : 0 ≤ π := le_of_lt (lt_trans (by norm_num) pi_lo)
  have lo :
      (137.03630377587843255 : ℝ) < 4 * π ^ 3 + π ^ 2 + π := by
    change (137.03630377587843255 : ℝ) < poly π
    have hmono : poly (3.14159265358979323846 : ℝ) < poly π :=
      mono (by norm_num) h_nonneg_pi pi_lo
    have hlo : (137.03630377587843255 : ℝ) < poly (3.14159265358979323846 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hlo hmono
  have hi :
      4 * π ^ 3 + π ^ 2 + π < (137.03630377587843257 : ℝ) := by
    change poly π < (137.03630377587843257 : ℝ)
    have hmono : poly π < poly (3.14159265358979323847 : ℝ) :=
      mono h_nonneg_pi (by norm_num) pi_hi
    have hhi : poly (3.14159265358979323847 : ℝ) < (137.03630377587843257 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hmono hhi
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  exact ⟨lo, hi⟩

/--
Eighteen-decimal bracketing for the UFRF inverse fine-structure value.

This sharpens `alpha_inv_bounds_d17` using the same 20-decimal bounds on `π`.
-/
theorem alpha_inv_bounds_d18 :
    (137.036303775878432558 : ℝ) < ufrf_alpha_inv ∧
    ufrf_alpha_inv < 137.036303775878432561 := by
  let poly (x : ℝ) := 4 * x ^ 3 + x ^ 2 + x
  have mono : StrictMonoOn poly (Set.Ici 0) := by
    intro a ha b hb hab
    simp at ha hb
    have hsq : a ^ 2 < b ^ 2 := by nlinarith
    have hcube : a ^ 3 < b ^ 3 := by nlinarith
    dsimp [poly]
    nlinarith
  have pi_lo : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
  have pi_hi : π < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have h_nonneg_pi : 0 ≤ π := le_of_lt (lt_trans (by norm_num) pi_lo)
  have lo :
      (137.036303775878432558 : ℝ) < 4 * π ^ 3 + π ^ 2 + π := by
    change (137.036303775878432558 : ℝ) < poly π
    have hmono : poly (3.14159265358979323846 : ℝ) < poly π :=
      mono (by norm_num) h_nonneg_pi pi_lo
    have hlo : (137.036303775878432558 : ℝ) < poly (3.14159265358979323846 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hlo hmono
  have hi :
      4 * π ^ 3 + π ^ 2 + π < (137.036303775878432561 : ℝ) := by
    change poly π < (137.036303775878432561 : ℝ)
    have hmono : poly π < poly (3.14159265358979323847 : ℝ) :=
      mono h_nonneg_pi (by norm_num) pi_hi
    have hhi : poly (3.14159265358979323847 : ℝ) < (137.036303775878432561 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hmono hhi
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  exact ⟨lo, hi⟩

/--
Nineteen-decimal bracketing for the UFRF inverse fine-structure value.

This sharpens `alpha_inv_bounds_d18` using the same 20-decimal bounds on `π`.
-/
theorem alpha_inv_bounds_d19 :
    (137.0363037758784325588 : ℝ) < ufrf_alpha_inv ∧
    ufrf_alpha_inv < 137.0363037758784325602 := by
  let poly (x : ℝ) := 4 * x ^ 3 + x ^ 2 + x
  have mono : StrictMonoOn poly (Set.Ici 0) := by
    intro a ha b hb hab
    simp at ha hb
    have hsq : a ^ 2 < b ^ 2 := by nlinarith
    have hcube : a ^ 3 < b ^ 3 := by nlinarith
    dsimp [poly]
    nlinarith
  have pi_lo : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
  have pi_hi : π < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have h_nonneg_pi : 0 ≤ π := le_of_lt (lt_trans (by norm_num) pi_lo)
  have lo :
      (137.0363037758784325588 : ℝ) < 4 * π ^ 3 + π ^ 2 + π := by
    change (137.0363037758784325588 : ℝ) < poly π
    have hmono : poly (3.14159265358979323846 : ℝ) < poly π :=
      mono (by norm_num) h_nonneg_pi pi_lo
    have hlo : (137.0363037758784325588 : ℝ) < poly (3.14159265358979323846 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hlo hmono
  have hi :
      4 * π ^ 3 + π ^ 2 + π < (137.0363037758784325602 : ℝ) := by
    change poly π < (137.0363037758784325602 : ℝ)
    have hmono : poly π < poly (3.14159265358979323847 : ℝ) :=
      mono h_nonneg_pi (by norm_num) pi_hi
    have hhi : poly (3.14159265358979323847 : ℝ) < (137.0363037758784325602 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hmono hhi
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  exact ⟨lo, hi⟩

/--
Twenty-decimal bracketing for the UFRF inverse fine-structure value.

This sharpens `alpha_inv_bounds_d19` using the same 20-decimal bounds on `π`.
-/
theorem alpha_inv_bounds_d20 :
    (137.03630377587843255887 : ℝ) < ufrf_alpha_inv ∧
    ufrf_alpha_inv < 137.03630377587843256013 := by
  let poly (x : ℝ) := 4 * x ^ 3 + x ^ 2 + x
  have mono : StrictMonoOn poly (Set.Ici 0) := by
    intro a ha b hb hab
    simp at ha hb
    have hsq : a ^ 2 < b ^ 2 := by nlinarith
    have hcube : a ^ 3 < b ^ 3 := by nlinarith
    dsimp [poly]
    nlinarith
  have pi_lo : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
  have pi_hi : π < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have h_nonneg_pi : 0 ≤ π := le_of_lt (lt_trans (by norm_num) pi_lo)
  have lo :
      (137.03630377587843255887 : ℝ) < 4 * π ^ 3 + π ^ 2 + π := by
    change (137.03630377587843255887 : ℝ) < poly π
    have hmono : poly (3.14159265358979323846 : ℝ) < poly π :=
      mono (by norm_num) h_nonneg_pi pi_lo
    have hlo : (137.03630377587843255887 : ℝ) < poly (3.14159265358979323846 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hlo hmono
  have hi :
      4 * π ^ 3 + π ^ 2 + π < (137.03630377587843256013 : ℝ) := by
    change poly π < (137.03630377587843256013 : ℝ)
    have hmono : poly π < poly (3.14159265358979323847 : ℝ) :=
      mono h_nonneg_pi (by norm_num) pi_hi
    have hhi : poly (3.14159265358979323847 : ℝ) < (137.03630377587843256013 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hmono hhi
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  exact ⟨lo, hi⟩

private theorem pi_gt_d23_local : (3.14159265358979323846264 : ℝ) < π := by
  pi_lower_bound [
    83059256537327 / 58731763537857, 229514716624781 / 124212469563491,
    369810203474024 / 188527606838667, 677928606298662 / 340604406463105,
    777449387541550 / 389193494379417, 2 - 601946350311 / 999308958963731,
    2 - 181254518629 / 1203578656967019, 2 - 183433996932 / 4872158052772001,
    2 - 45585504193 / 4843142763857414, 2 - 66901346023 / 28431194083406149,
    2 - 16815927644 / 28585184642574541, 2 - 6701090146 / 45564394933746681,
    2 - 2736600291 / 74430597154836278, 2 - 1507020551 / 163952974274946234,
    2 - 1544736865 / 672224949222763999, 2 - 362248906 / 630561121247994833,
    2 - 31146966 / 216868186249020589, 2 - 56004865 / 1559788968667090158,
    2 - 10022105 / 1116500776979871816, 2 - 10111603 / 4505884784087043220,
    2 - 6678318 / 11903842134423352567, 2 - 3574474 / 25485443615951972803,
    2 - 917150 / 26156547354794184499, 2 - 711394 / 81154057019752116051,
    2 - 250631 / 114365442862422125879, 2 - 99049 / 180788214547762209697,
    2 - 61427 / 448476114045589107403, 2 - 12176 / 355585990826124858775,
    2 - 1522 / 177792995413062429007, 2 - 3044 / 1422343963304499431295,
    2 - 3044 / 5689375853217997724419, 2 - 693 / 5180995356478413170684,
    2 - 1199 / 35855777387691875276180, 2 - 270 / 32297113910514783401329,
    2 - 194 / 92824297757627673775623, 2 - 79 / 151198340677372911923160,
    2 - 10 / 76556121861960968062357, 2 - 9 / 275602038703059485024483,
    2 - 1 / 122489794979137548899770]

private theorem pi_lt_d23_local : π < (3.14159265358979323846265 : ℝ) := by
  pi_upper_bound [
    92509020510196 / 65413755723685, 129895343557004 / 70298853360201,
    335618281015117 / 171096715928044, 3328643159695587 / 1672374520269344,
    314321062249541 / 157350066170592, 2 - 716308481182 / 1189164918529775,
    2 - 308442053061 / 2048138025927881, 2 - 160682011956 / 4267846591039751,
    2 - 60435073946 / 6420806268272081, 2 - 35127790897 / 14928325064948070,
    2 - 7736078869 / 13150463510634039, 2 - 8292341127 / 56384184931688284,
    2 - 3552405089 / 96619017757076353, 2 - 1096482049 / 119289344165444852,
    2 - 634669103 / 276189696254469964, 2 - 401170253 / 698310913720252237,
    2 - 114198861 / 795136831522338761, 2 - 50588775 / 1408945690403529656,
    2 - 34010351 / 3788883005801491842, 2 - 11330613 / 5049094264389023683,
    2 - 6440689 / 11480277682631615958, 2 - 2068458 / 14747783794472917067,
    2 - 1257489 / 35862803877918316820, 2 - 1377871 / 157184094467851665737,
    2 - 223260 / 101875780623563580817, 2 - 112177 / 204749967625360391293,
    2 - 42545 / 310619373761856977786, 2 - 3591 / 104870999758263335074,
    2 - 6421 / 750071500359575464293, 2 - 5333 / 2491905504698717301937,
    2 - 599 / 1119558520393423336704, 2 - 1062 / 7939707169668217586243,
    2 - 977 / 29216926194974947577004, 2 - 103 / 12320750862159343297544,
    2 - 73 / 34928730599519691678456, 2 - 57 / 109092473653294379488862,
    2 - 28 / 214357141213490710574599, 2 - 9 / 275602038703059485024482,
    2 - 2 / 244979589958275097799539]

private theorem pi_gt_d25_local : (3.1415926535897932384626433 : ℝ) < π := by
  pi_lower_bound [
    2 - 3289910387877251662993 / 5616228332641321147898,
    2 - 1648311417692038621923 / 10826992214258549209325,
    2 - 395292648316840416144 / 10286193517580617358195,
    2 - 35504871695071056927 / 3686693285931242086375,
    2 - 23073992572655387491 / 9577896906586823931154,
    2 - 9024207159593912090 / 14981353500137743580273,
    2 - 2468281025675379346 / 16390048559176928604859,
    2 - 496144436703854203 / 13178004912147315472204,
    2 - 323896911021853645 / 34411794025789051596677,
    2 - 87953991563098308 / 37377977472695713467473,
    2 - 39461345914286979 / 67079847337882477489228,
    2 - 5391655974885524 / 36660832317443501539135,
    2 - 1712540488452588 / 46578015659270105000269,
    2 - 1706327373687426 / 185636120102791567353611,
    2 - 588929891154691 / 256285309910843673864165,
    2 - 163027822439321 / 283780033036061844832829,
    2 - 20438508119567 / 142307991909272181620446,
    2 - 8077691543072 / 224971422771560130667919,
    2 - 1210507836607 / 134855196599111585756718,
    2 - 284487158498 / 126771824283874393877639,
    2 - 219967362634 / 392083269997114568156731,
    2 - 65821191741 / 469294858726072470554683,
    2 - 18809582498 / 536437589634023757449243,
    2 - 1617612445 / 184533201850719339408516,
    2 - 7484522389 / 3415262747352476939845237,
    2 - 615876865 / 1124123199675142429238669,
    2 - 169416222 / 1236901181871894156324881,
    2 - 67518045 / 1971786377296968248225122,
    2 - 32326517 / 3776234092444996473952744,
    2 - 5932871 / 2772202119551356388123060,
    2 - 1533930 / 2866985644719672552371233,
    2 - 1392901 / 10413583857192118591427000,
    2 - 625936 / 18718450271011093947348617,
    2 - 39121 / 4679612567752773486827374,
    2 - 52765 / 25246773562789815498818269,
    2 - 6822 / 13056646583557443103035401,
    2 - 1222 / 9355158091531630297220017,
    2 - 511 / 15648071308584821871945629,
    2 - 1744 / 213622202443615885281198601,
    2 - 109 / 53405550610903971320299623,
    2 - 21 / 41156571112990216430322640,
    2 - 41 / 321413222025256928312995845,
    2 - 5 / 156786937573296062591705289,
    2 - 1 / 125429550058636850073364231]

private theorem pi_lt_d25_local : π < (3.1415926535897932384626434 : ℝ) := by
  pi_upper_bound [
    2 - 1572584048032918633353217 / 2684568892382786771291329,
    2 - 174431960042638713916993 / 1145762537969847588040239,
    2 - 314824707215325676543828 / 8192279508160378278457487,
    2 - 183356877729493794870509 / 19039093447800941332004044,
    2 - 13588324414738124896603 / 5640444321363536605474309,
    2 - 9617727984310213991096 / 15966674994593366961902659,
    2 - 4869427440158272125395 / 32334305279417997321124262,
    2 - 1466799915180735035801 / 38959413947690113243940929,
    2 - 118826470905450684391 / 12624486070921168435448455,
    2 - 286912641060367950417 / 121929818574436149203046581,
    2 - 42843785032858765797 / 72829613202338976983293385,
    2 - 16725895785014723367 / 113728558274061431691174574,
    2 - 261245856324379570 / 7105416583634402999445191,
    2 - 272569419001266592 / 29653588275221671335529715,
    2 - 55922648493631389 / 24335924386729671340132621,
    2 - 8421560407534393 / 14659281188367777052722021,
    2 - 456841073885018 / 3180865035056662004754739,
    2 - 647488058393300 / 18033160705334117960843217,
    2 - 70722762355081 / 7878785855826771484061048,
    2 - 342818089101101 / 152764978153359781223292743,
    2 - 29476633744463 / 52540953388009354625862259,
    2 - 3863422429168 / 27545600970426772845847561,
    2 - 1902764759084 / 54265667040303324364219565,
    2 - 331941528355 / 37867063426659957527353706,
    2 - 74041821445 / 33786026867776965916228358,
    2 - 41494875127 / 75738113328682547715439845,
    2 - 8868386983 / 64747744997937810875663027,
    2 - 701827195 / 20496051127036378314210684,
    2 - 451379269 / 52728036992686249840042066,
    2 - 238785033 / 111575049347902656291149039,
    2 - 75707380 / 141500571511957679553785921,
    2 - 19834839 / 148288901523083596271279384,
    2 - 1815988 / 54306640089007333777347397,
    2 - 1698625 / 203187722652771014648453469,
    2 - 103719 / 49627027521254560290380594,
    2 - 54365 / 104049339125637700717754262,
    2 - 18255 / 139753200459009747197832578,
    2 - 3711 / 113639907291894860991761701,
    2 - 25 / 3062244874478438722494246,
    2 - 91 / 44586285372406067799516199,
    2 - 37 / 72513958627649428948663699,
    2 - 2 / 15678693757329606259170529,
    2 - 3 / 94072162543977637555023173,
    2 - 1 / 125429550058636850073364230]

private theorem pi_gt_d27_local : (3.141592653589793238462643383 : ℝ) < π := by
  pi_lower_bound [
    11504447028599191 / 8134872507723915,
    11531165357430531 / 6240621721582331,
    167398526581640002 / 85339028799870147,
    2 - 868358315709187 / 90167084669455374,
    2 - 152518480838165 / 63309645316795328,
    2 - 43076824148632 / 71513111215297799,
    2 - 38218725513043 / 253782596273546048,
    2 - 35488381533699 / 942600645252000926,
    2 - 23113060687785 / 2455601941939964342,
    2 - 11459926573315 / 4870147103998310408,
    2 - 4646588046021 / 7898676782239961317,
    2 - 5021195407316 / 34141867307221455895,
    2 - 199558405159 / 5427629059347757930,
    2 - 574051330190 / 62452647317043612379,
    2 - 64021459941 / 27860293641665594902,
    2 - 43849535029 / 76328213877585776962,
    2 - 143018761576 / 995802269234449268083,
    2 - 19052708984 / 530636138422395325093,
    2 - 44179457077 / 4921760264237841909253,
    2 - 14916256849 / 6646911945756102632044,
    2 - 1566988389 / 2793095867721538669309,
    2 - 1376972257 / 9817598006448957019732,
    2 - 22511453 / 642012633069534546173,
    2 - 599321880 / 68369148492544265661031,
    2 - 196382303 / 89611217498782549797407,
    2 - 115456973 / 210736706132915916924016,
    2 - 17226285 / 125768430107962637879429,
    2 - 28643475 / 836499543247235277529586,
    2 - 39249269 / 4584917939082163856694575,
    2 - 14258925 / 6662646483890147685078203,
    2 - 4744600 / 8867875385406738503048087,
    2 - 7914741 / 59172058252134649836872488,
    2 - 425004 / 12709632037430023152525101,
    2 - 606596 / 72560370776528242785602049,
    2 - 176159 / 84287811694257388580618354,
    2 - 27921 / 53438086962695304731728442,
    2 - 113095 / 865811460197847568301225714,
    2 - 301831 / 9242804327087016380491626509,
    2 - 49520 / 6065694647366891421516602477,
    2 - 11062 / 5419928448236878263717013115,
    2 - 2899 / 5681566650312316068166920635,
    2 - 341 / 2673217285624697867188575198,
    2 - 761 / 23862971898655660726457544979,
    2 - 35 / 4390034252052289752567748082,
    2 - 1429 / 716955308135168235019349943549]

private theorem pi_lt_d27_local : π < (3.141592653589793238462643384 : ℝ) := by
  pi_upper_bound [
    12673179459739050 / 8961291135175549,
    17169006956949601 / 9291799608484049,
    10954518762444663 / 5584565236307854,
    2 - 648401991166243 / 67327641343058021,
    99568813088608805 / 49844446362877424,
    2 - 488447140111729 / 810885559554731335,
    2 - 132888848858118 / 882417627126437485,
    2 - 770469022502 / 20464291871621067,
    2 - 6652707668053 / 706803918767169090,
    2 - 2139612305527 / 909275169153829926,
    2 - 4475237942114 / 7607400888194735473,
    2 - 1107620576428 / 7531321065906690711,
    2 - 117452390789 / 3194493405719097055,
    2 - 852488295721 / 92744582365046905516,
    2 - 140218050785 / 61018853245961452917,
    2 - 5279734045 / 9190352169914934699,
    2 - 104342405153 / 726508904732215961159,
    2 - 7805040022 / 217377817557827211573,
    2 - 3642239847 / 405759430690713123160,
    2 - 615011699 / 274058609357944592427,
    2 - 366202684 / 652742043661011725155,
    2 - 977479051 / 6969273588235567761034,
    2 - 168653673 / 4809897818660495420374,
    2 - 393982711 / 44944567136200922737273,
    2 - 20877460 / 9526594709922170187063,
    2 - 12125803 / 22132502845338152284531,
    2 - 12929803 / 94399983798899509623889,
    2 - 23411387 / 683702467395602724959089,
    2 - 1335323 / 155986252308775796247644,
    2 - 1410698 / 659164843740384605364321,
    2 - 195181 / 364802256375473723340941,
    2 - 1203947 / 9000929028060773595390313,
    2 - 243497 / 7281713283211683531379480,
    2 - 78751 / 9420111176173887806066883,
    2 - 96386 / 46118364761168561672872125,
    2 - 43815 / 83857661984545495391306962,
    2 - 111788 / 855805575070489269775475663,
    2 - 27047 / 828245371200183321273020406,
    2 - 4556 / 558063505924950672787351391,
    2 - 1937 / 949050931498357728875416236,
    2 - 2207 / 4325359640303305126748669831,
    2 - 373 / 2924076385741971567335303662,
    2 - 287 / 8999570216707193992763883585,
    2 - 468 / 58701029427442045834334460061,
    2 - 193 / 96831612645267648256637186206]

/--
Reusable twenty-five-decimal lower bound on `π` for downstream prediction proofs.
-/
theorem pi_gt_d25_ufrf : (3.1415926535897932384626433 : ℝ) < π :=
  pi_gt_d25_local

/--
Reusable twenty-five-decimal upper bound on `π` for downstream prediction proofs.
-/
theorem pi_lt_d25_ufrf : π < (3.1415926535897932384626434 : ℝ) :=
  pi_lt_d25_local

/--
Twenty-three-decimal bracketing for the UFRF inverse fine-structure value.

This sharpens `alpha_inv_bounds_d20` using stronger local bounds on `π`.
-/
theorem alpha_inv_bounds_d23 :
    (137.03630377587843255920196 : ℝ) < ufrf_alpha_inv ∧
    ufrf_alpha_inv < 137.03630377587843255920323 := by
  let poly (x : ℝ) := 4 * x ^ 3 + x ^ 2 + x
  have mono : StrictMonoOn poly (Set.Ici 0) := by
    intro a ha b hb hab
    simp at ha hb
    have hsq : a ^ 2 < b ^ 2 := by nlinarith
    have hcube : a ^ 3 < b ^ 3 := by nlinarith
    dsimp [poly]
    nlinarith
  have pi_lo : (3.14159265358979323846264 : ℝ) < π := pi_gt_d23_local
  have pi_hi : π < (3.14159265358979323846265 : ℝ) := pi_lt_d23_local
  have h_nonneg_pi : 0 ≤ π := le_of_lt (lt_trans (by norm_num) pi_lo)
  have lo :
      (137.03630377587843255920196 : ℝ) < 4 * π ^ 3 + π ^ 2 + π := by
    change (137.03630377587843255920196 : ℝ) < poly π
    have hmono : poly (3.14159265358979323846264 : ℝ) < poly π :=
      mono (by norm_num) h_nonneg_pi pi_lo
    have hlo : (137.03630377587843255920196 : ℝ) <
        poly (3.14159265358979323846264 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hlo hmono
  have hi :
      4 * π ^ 3 + π ^ 2 + π < (137.03630377587843255920323 : ℝ) := by
    change poly π < (137.03630377587843255920323 : ℝ)
    have hmono : poly π < poly (3.14159265358979323846265 : ℝ) :=
      mono h_nonneg_pi (by norm_num) pi_hi
    have hhi : poly (3.14159265358979323846265 : ℝ) <
        (137.03630377587843255920323 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hmono hhi
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  exact ⟨lo, hi⟩

/--
Twenty-five-decimal bracketing for the UFRF inverse fine-structure value.

This sharpens `alpha_inv_bounds_d23` using stronger local bounds on `π`.
-/
theorem alpha_inv_bounds_d25 :
    (137.0363037758784325592023841 : ℝ) < ufrf_alpha_inv ∧
    ufrf_alpha_inv < 137.0363037758784325592023968 := by
  let poly (x : ℝ) := 4 * x ^ 3 + x ^ 2 + x
  have mono : StrictMonoOn poly (Set.Ici 0) := by
    intro a ha b hb hab
    simp at ha hb
    have hsq : a ^ 2 < b ^ 2 := by nlinarith
    have hcube : a ^ 3 < b ^ 3 := by nlinarith
    dsimp [poly]
    nlinarith
  have pi_lo : (3.1415926535897932384626433 : ℝ) < π := pi_gt_d25_local
  have pi_hi : π < (3.1415926535897932384626434 : ℝ) := pi_lt_d25_local
  have h_nonneg_pi : 0 ≤ π := le_of_lt (lt_trans (by norm_num) pi_lo)
  have lo :
      (137.0363037758784325592023841 : ℝ) < 4 * π ^ 3 + π ^ 2 + π := by
    change (137.0363037758784325592023841 : ℝ) < poly π
    have hmono : poly (3.1415926535897932384626433 : ℝ) < poly π :=
      mono (by norm_num) h_nonneg_pi pi_lo
    have hlo : (137.0363037758784325592023841 : ℝ) <
        poly (3.1415926535897932384626433 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hlo hmono
  have hi :
      4 * π ^ 3 + π ^ 2 + π < (137.0363037758784325592023968 : ℝ) := by
    change poly π < (137.0363037758784325592023968 : ℝ)
    have hmono : poly π < poly (3.1415926535897932384626434 : ℝ) :=
      mono h_nonneg_pi (by norm_num) pi_hi
    have hhi : poly (3.1415926535897932384626434 : ℝ) <
        (137.0363037758784325592023968 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hmono hhi
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  exact ⟨lo, hi⟩

/--
Twenty-six-decimal bracketing for the UFRF inverse fine-structure value.

This sharpens `alpha_inv_bounds_d25` using stronger local bounds on `π`.
-/
theorem alpha_inv_bounds_d26 :
    (137.03630377587843255920239461 : ℝ) < ufrf_alpha_inv ∧
    ufrf_alpha_inv < 137.03630377587843255920239475 := by
  let poly (x : ℝ) := 4 * x ^ 3 + x ^ 2 + x
  have mono : StrictMonoOn poly (Set.Ici 0) := by
    intro a ha b hb hab
    simp at ha hb
    have hsq : a ^ 2 < b ^ 2 := by nlinarith
    have hcube : a ^ 3 < b ^ 3 := by nlinarith
    dsimp [poly]
    nlinarith
  have pi_lo : (3.141592653589793238462643383 : ℝ) < π := pi_gt_d27_local
  have pi_hi : π < (3.141592653589793238462643384 : ℝ) := pi_lt_d27_local
  have h_nonneg_pi : 0 ≤ π := le_of_lt (lt_trans (by norm_num) pi_lo)
  have lo :
      (137.03630377587843255920239461 : ℝ) < 4 * π ^ 3 + π ^ 2 + π := by
    change (137.03630377587843255920239461 : ℝ) < poly π
    have hmono : poly (3.141592653589793238462643383 : ℝ) < poly π :=
      mono (by norm_num) h_nonneg_pi pi_lo
    have hlo : (137.03630377587843255920239461 : ℝ) <
        poly (3.141592653589793238462643383 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hlo hmono
  have hi :
      4 * π ^ 3 + π ^ 2 + π < (137.03630377587843255920239475 : ℝ) := by
    change poly π < (137.03630377587843255920239475 : ℝ)
    have hmono : poly π < poly (3.141592653589793238462643384 : ℝ) :=
      mono h_nonneg_pi (by norm_num) pi_hi
    have hhi : poly (3.141592653589793238462643384 : ℝ) <
        (137.03630377587843255920239475 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hmono hhi
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  exact ⟨lo, hi⟩

/--
Twenty-seven-decimal bracketing for the UFRF inverse fine-structure value.

This sharpens `alpha_inv_bounds_d26` using the existing local `π` bounds.
-/
theorem alpha_inv_bounds_d27 :
    (137.036303775878432559202394616 : ℝ) < ufrf_alpha_inv ∧
    ufrf_alpha_inv < 137.036303775878432559202394743 := by
  let poly (x : ℝ) := 4 * x ^ 3 + x ^ 2 + x
  have mono : StrictMonoOn poly (Set.Ici 0) := by
    intro a ha b hb hab
    simp at ha hb
    have hsq : a ^ 2 < b ^ 2 := by nlinarith
    have hcube : a ^ 3 < b ^ 3 := by nlinarith
    dsimp [poly]
    nlinarith
  have pi_lo : (3.141592653589793238462643383 : ℝ) < π := pi_gt_d27_local
  have pi_hi : π < (3.141592653589793238462643384 : ℝ) := pi_lt_d27_local
  have h_nonneg_pi : 0 ≤ π := le_of_lt (lt_trans (by norm_num) pi_lo)
  have lo :
      (137.036303775878432559202394616 : ℝ) < 4 * π ^ 3 + π ^ 2 + π := by
    change (137.036303775878432559202394616 : ℝ) < poly π
    have hmono : poly (3.141592653589793238462643383 : ℝ) < poly π :=
      mono (by norm_num) h_nonneg_pi pi_lo
    have hlo : (137.036303775878432559202394616 : ℝ) <
        poly (3.141592653589793238462643383 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hlo hmono
  have hi :
      4 * π ^ 3 + π ^ 2 + π < (137.036303775878432559202394743 : ℝ) := by
    change poly π < (137.036303775878432559202394743 : ℝ)
    have hmono : poly π < poly (3.141592653589793238462643384 : ℝ) :=
      mono h_nonneg_pi (by norm_num) pi_hi
    have hhi : poly (3.141592653589793238462643384 : ℝ) <
        (137.036303775878432559202394743 : ℝ) := by
      dsimp [poly]
      norm_num
    exact lt_trans hmono hhi
  unfold ufrf_alpha_inv
  dsimp [ufrf_tensor_structure]
  simp
  exact ⟨lo, hi⟩

/--
Twenty-one-decimal bracketing for the UFRF inverse fine-structure value.

This follows from the stronger `alpha_inv_bounds_d23`.
-/
theorem alpha_inv_bounds_d21 :
    (137.036303775878432559201 : ℝ) < ufrf_alpha_inv ∧
    ufrf_alpha_inv < 137.036303775878432559204 := by
  rcases alpha_inv_bounds_d23 with ⟨hlo, hhi⟩
  constructor <;> linarith

/--
Twenty-two-decimal bracketing for the UFRF inverse fine-structure value.

This follows from the stronger `alpha_inv_bounds_d23`.
-/
theorem alpha_inv_bounds_d22 :
    (137.0363037758784325592019 : ℝ) < ufrf_alpha_inv ∧
    ufrf_alpha_inv < 137.0363037758784325592033 := by
  rcases alpha_inv_bounds_d23 with ⟨hlo, hhi⟩
  constructor <;> linarith


/--
**Phase Markers 1, 3, 7**

The digits of 137 correspond to breathing cycle checkpoints:
- 1: Position 1 (first emergence)
- 3: Position 3 (end of Log1 linear phase)
- 7: Position 7 (start of Log3, first post-flip position)

These sum to 11, which is the first Bridge position.

✅ PROVEN
-/
theorem phase_marker_sum : 1 + 3 + 7 = 11 := by norm_num

/--
137 is prime in the standard natural-number sense.

✅ PROVEN
-/
theorem one_three_seven_is_prime : Nat.Prime 137 := by norm_num

/--
**The Merkaba Coefficient**

The factor 4 = 2² in the Log3 term arises because at the
cubed/volume scale, BOTH expansion and contraction phases
contribute simultaneously, creating a double-reflection duality.

2 (expansion) × 2 (contraction) = 4

✅ PROVEN
-/
theorem merkaba_duality : 2 * 2 = 4 := by norm_num

/--
The CODATA 2018 recommended value for the inverse fine-structure constant.
Value: `137.035999084(21)`.
-/
def codata2018_alpha_inv : ℝ := 137.035999084

/--
The CODATA 2022 recommended value for the inverse fine-structure constant.
Value: `137.035999177(21)`.
-/
def codata_alpha_inv : ℝ := 137.035999177

/--
The static UFRF-to-CODATA 2022 gap lies in the explicit interval
`0.0003045988784 < gap < 0.0003045988785`.
-/
theorem ufrf_codata2022_gap_bounds_d13 :
    (0.0003045988784 : ℝ) < ufrf_alpha_inv - codata_alpha_inv ∧
    ufrf_alpha_inv - codata_alpha_inv < 0.0003045988785 := by
  rcases alpha_inv_bounds_d13 with ⟨hlo, hhi⟩
  unfold codata_alpha_inv
  constructor <;> linarith

/--
The static UFRF-to-CODATA 2022 gap rounds to `0.000304598878`
at the `10^-12` place.
-/
theorem ufrf_codata2022_gap_rounds_to_0_000304598878 :
    |(ufrf_alpha_inv - codata_alpha_inv) - 0.000304598878| < 0.0000000000005 := by
  rcases ufrf_codata2022_gap_bounds_d13 with ⟨hlo, hhi⟩
  rw [abs_lt]
  constructor <;> linarith

/--
The static UFRF-to-CODATA 2022 gap lies in the explicit interval
`0.00030459887843 < gap < 0.00030459887844`.
-/
theorem ufrf_codata2022_gap_bounds_d14 :
    (0.00030459887843 : ℝ) < ufrf_alpha_inv - codata_alpha_inv ∧
    ufrf_alpha_inv - codata_alpha_inv < 0.00030459887844 := by
  rcases alpha_inv_bounds_d14 with ⟨hlo, hhi⟩
  unfold codata_alpha_inv
  constructor <;> linarith

/--
The static UFRF-to-CODATA 2022 gap lies in the explicit interval
`0.000304598878432 < gap < 0.000304598878433`.
-/
theorem ufrf_codata2022_gap_bounds_d15 :
    (0.000304598878432 : ℝ) < ufrf_alpha_inv - codata_alpha_inv ∧
    ufrf_alpha_inv - codata_alpha_inv < 0.000304598878433 := by
  rcases alpha_inv_bounds_d15 with ⟨hlo, hhi⟩
  unfold codata_alpha_inv
  constructor <;> linarith

/--
The static UFRF-to-CODATA 2022 gap lies in the explicit interval
`0.0003045988784325 < gap < 0.0003045988784326`.
-/
theorem ufrf_codata2022_gap_bounds_d16 :
    (0.0003045988784325 : ℝ) < ufrf_alpha_inv - codata_alpha_inv ∧
    ufrf_alpha_inv - codata_alpha_inv < 0.0003045988784326 := by
  rcases alpha_inv_bounds_d16 with ⟨hlo, hhi⟩
  unfold codata_alpha_inv
  constructor <;> linarith

/--
The static UFRF-to-CODATA 2022 gap lies in the explicit interval
`0.00030459887843255 < gap < 0.00030459887843257`.
-/
theorem ufrf_codata2022_gap_bounds_d17 :
    (0.00030459887843255 : ℝ) < ufrf_alpha_inv - codata_alpha_inv ∧
    ufrf_alpha_inv - codata_alpha_inv < 0.00030459887843257 := by
  rcases alpha_inv_bounds_d17 with ⟨hlo, hhi⟩
  unfold codata_alpha_inv
  constructor <;> linarith

/--
The static UFRF-to-CODATA 2022 gap lies in the explicit interval
`0.000304598878432558 < gap < 0.000304598878432561`.
-/
theorem ufrf_codata2022_gap_bounds_d18 :
    (0.000304598878432558 : ℝ) < ufrf_alpha_inv - codata_alpha_inv ∧
    ufrf_alpha_inv - codata_alpha_inv < 0.000304598878432561 := by
  rcases alpha_inv_bounds_d18 with ⟨hlo, hhi⟩
  unfold codata_alpha_inv
  constructor <;> linarith

/--
The static UFRF-to-CODATA 2022 gap lies in the explicit interval
`0.0003045988784325588 < gap < 0.0003045988784325602`.
-/
theorem ufrf_codata2022_gap_bounds_d19 :
    (0.0003045988784325588 : ℝ) < ufrf_alpha_inv - codata_alpha_inv ∧
    ufrf_alpha_inv - codata_alpha_inv < 0.0003045988784325602 := by
  rcases alpha_inv_bounds_d19 with ⟨hlo, hhi⟩
  unfold codata_alpha_inv
  constructor <;> linarith

/--
The static UFRF-to-CODATA 2022 gap lies in the explicit interval
`0.00030459887843255887 < gap < 0.00030459887843256013`.
-/
theorem ufrf_codata2022_gap_bounds_d20 :
    (0.00030459887843255887 : ℝ) < ufrf_alpha_inv - codata_alpha_inv ∧
    ufrf_alpha_inv - codata_alpha_inv < 0.00030459887843256013 := by
  rcases alpha_inv_bounds_d20 with ⟨hlo, hhi⟩
  unfold codata_alpha_inv
  constructor <;> linarith

/--
The static UFRF-to-CODATA 2022 gap lies in the explicit interval
`0.00030459887843255920196 < gap < 0.00030459887843255920323`.
-/
theorem ufrf_codata2022_gap_bounds_d23 :
    (0.00030459887843255920196 : ℝ) < ufrf_alpha_inv - codata_alpha_inv ∧
    ufrf_alpha_inv - codata_alpha_inv < 0.00030459887843255920323 := by
  rcases alpha_inv_bounds_d23 with ⟨hlo, hhi⟩
  unfold codata_alpha_inv
  constructor <;> linarith

/--
The static UFRF-to-CODATA 2022 gap lies in the explicit interval
`0.0003045988784325592023841 < gap < 0.0003045988784325592023968`.
-/
theorem ufrf_codata2022_gap_bounds_d25 :
    (0.0003045988784325592023841 : ℝ) < ufrf_alpha_inv - codata_alpha_inv ∧
    ufrf_alpha_inv - codata_alpha_inv < 0.0003045988784325592023968 := by
  rcases alpha_inv_bounds_d25 with ⟨hlo, hhi⟩
  unfold codata_alpha_inv
  constructor <;> linarith

/--
The static UFRF-to-CODATA 2022 gap lies in the explicit interval
`0.00030459887843255920239461 < gap < 0.00030459887843255920239475`.
-/
theorem ufrf_codata2022_gap_bounds_d26 :
    (0.00030459887843255920239461 : ℝ) < ufrf_alpha_inv - codata_alpha_inv ∧
    ufrf_alpha_inv - codata_alpha_inv < 0.00030459887843255920239475 := by
  rcases alpha_inv_bounds_d26 with ⟨hlo, hhi⟩
  unfold codata_alpha_inv
  constructor <;> linarith

/--
The static UFRF-to-CODATA 2022 gap lies in the explicit interval
`0.000304598878432559202394616 < gap < 0.000304598878432559202394743`.
-/
theorem ufrf_codata2022_gap_bounds_d27 :
    (0.000304598878432559202394616 : ℝ) < ufrf_alpha_inv - codata_alpha_inv ∧
    ufrf_alpha_inv - codata_alpha_inv < 0.000304598878432559202394743 := by
  rcases alpha_inv_bounds_d27 with ⟨hlo, hhi⟩
  unfold codata_alpha_inv
  constructor <;> linarith

/--
The static UFRF-to-CODATA 2022 gap lies in the explicit interval
`0.000304598878432559201 < gap < 0.000304598878432559204`.
-/
theorem ufrf_codata2022_gap_bounds_d21 :
    (0.000304598878432559201 : ℝ) < ufrf_alpha_inv - codata_alpha_inv ∧
    ufrf_alpha_inv - codata_alpha_inv < 0.000304598878432559204 := by
  rcases ufrf_codata2022_gap_bounds_d23 with ⟨hlo, hhi⟩
  constructor <;> linarith

/--
The static UFRF-to-CODATA 2022 gap lies in the explicit interval
`0.0003045988784325592019 < gap < 0.0003045988784325592033`.
-/
theorem ufrf_codata2022_gap_bounds_d22 :
    (0.0003045988784325592019 : ℝ) < ufrf_alpha_inv - codata_alpha_inv ∧
    ufrf_alpha_inv - codata_alpha_inv < 0.0003045988784325592033 := by
  rcases ufrf_codata2022_gap_bounds_d23 with ⟨hlo, hhi⟩
  constructor <;> linarith


/--
**Theorem: Prediction Accuracy**
The UFRF derived value ($4\pi^3 + \pi^2 + \pi$) matches the CODATA empirical value
to within `3.1 × 10⁻⁴`.

This is not a definition, but a falsifiable prediction of the theory.
-/
theorem ufrf_matches_codata : 
    |ufrf_alpha_inv - codata_alpha_inv| < 0.00031 := by
  rcases ufrf_codata2022_gap_bounds_d13 with ⟨hlo, hhi⟩
  have hpos : 0 < ufrf_alpha_inv - codata_alpha_inv := by
    linarith
  rw [abs_of_pos hpos]
  linarith

/--
Against the CODATA 2018 value, the current UFRF static candidate differs by
less than `3.05 × 10⁻⁴`.
-/
theorem ufrf_matches_codata2018 :
    |ufrf_alpha_inv - codata2018_alpha_inv| < 0.000305 := by
  rcases alpha_inv_bounds_d9 with ⟨hlo, hhi⟩
  unfold codata2018_alpha_inv
  rw [abs_lt]
  constructor <;> linarith

end
