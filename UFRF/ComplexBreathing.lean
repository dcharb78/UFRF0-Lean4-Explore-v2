import UFRF.Fourier

/-!
# UFRF.ComplexBreathing

This module exposes the breathing cycle as a configuration of 13th roots of
unity in the complex plane. It is intentionally thin: the underlying character
theory is already formalized in `UFRF.Fourier`, and this file provides the
complex-analysis-facing interface without duplicating that construction.
-/

noncomputable section

open Complex ZMod
open scoped BigOperators Real

namespace UFRF.ComplexBreathing

/-- The cycle length used for the complex breathing interface. -/
abbrev CycleLen : ℕ := FourierCycleLen

instance : NeZero CycleLen := inferInstance

/-- The complex breathing position corresponding to a cycle index. -/
def breathingRoot (k : ZMod CycleLen) : ℂ :=
  breathingCharacter k

/--
The breathing root at position `k` is the standard `13`th-root-of-unity point
`exp(2πik / 13)` in the complex plane.

✅ PROVEN
-/
theorem breathingRoot_eq_exp (k : ZMod CycleLen) :
    breathingRoot k = Complex.exp (2 * Real.pi * Complex.I * (k.val : ℂ) / CycleLen) := by
  simpa [breathingRoot, breathingCharacter] using ZMod.stdAddChar_coe (N := CycleLen) (k.val : ℤ)

/-- The entry position maps to `1` on the unit circle. -/
@[simp] theorem breathingRoot_zero :
    breathingRoot 0 = 1 := by
  simp [breathingRoot]

/-- Addition in the cycle becomes multiplication in the complex picture. -/
theorem breathingRoot_add (a b : ZMod CycleLen) :
    breathingRoot (a + b) = breathingRoot a * breathingRoot b := by
  simpa [breathingRoot] using breathingCharacter.map_add_eq_mul a b

/-- The complex breathing map is injective. Distinct cycle positions stay distinct. -/
theorem breathingRoot_injective :
    Function.Injective breathingRoot :=
  character_injective

/-- The generator `ω` is the breathing position at cycle index `1`. -/
def omega : ℂ := breathingRoot 1

/-- Explicit exponential form of the primitive generator. -/
theorem omega_eq_exp :
    omega = Complex.exp (2 * Real.pi * Complex.I * ((1 : ZMod CycleLen).val : ℂ) / CycleLen) := by
  simpa [omega] using breathingRoot_eq_exp (1 : ZMod CycleLen)

/-- The underlying additive character is primitive. -/
theorem breathingCharacter_is_primitive :
    breathingCharacter.IsPrimitive :=
  standard_character_is_primitive

/-- The breathing positions can be packaged as actual `CycleLen`-th roots of unity. -/
def breathingRootOfUnity (k : ZMod CycleLen) : rootsOfUnity CycleLen ℂ :=
  rootsOfUnityCircleEquiv CycleLen (ZMod.rootsOfUnityAddChar CycleLen k)

/-- The packaged root-of-unity element has the expected complex value. -/
@[simp] theorem breathingRootOfUnity_val (k : ZMod CycleLen) :
    (breathingRootOfUnity k).val = breathingRoot k := by
  rw [breathingRoot_eq_exp]
  simpa [breathingRootOfUnity] using
    (rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val (n := CycleLen) k)

/-- Every breathing position closes after one full cycle: `ζ^13 = 1`. -/
theorem breathingRoot_pow_cycleLen_eq_one (k : ZMod CycleLen) :
    breathingRoot k ^ CycleLen = 1 := by
  have hk : (((breathingRootOfUnity k).1 : ℂˣ) : ℂ) ^ CycleLen = 1 := by
    exact (mem_rootsOfUnity' CycleLen (breathingRootOfUnity k).1).mp (breathingRootOfUnity k).2
  simpa using hk

/-- The breathing character is not the trivial character. -/
theorem breathingCharacter_ne_one :
    breathingCharacter ≠ 1 := by
  rw [AddChar.zmod_char_ne_one_iff (n := CycleLen) breathingCharacter]
  intro h
  have hzero : (1 : ZMod CycleLen) = 0 :=
    (AddChar.IsPrimitive.zmod_char_eq_one_iff (n := CycleLen)
      breathingCharacter_is_primitive (1 : ZMod CycleLen)).mp h
  have hone : (1 : ZMod CycleLen) ≠ 0 := by
    change (1 : ZMod 13) ≠ 0
    decide
  exact hone hzero

/--
A complete traversal of the breathing cycle cancels to zero in the complex plane.

This is the roots-of-unity closure theorem for the UFRF breathing cycle.

✅ PROVEN
-/
theorem complete_breath_sums_to_zero :
    ∑ k : ZMod CycleLen, breathingRoot k = 0 := by
  simpa [breathingRoot] using
    (AddChar.sum_eq_zero_of_ne_one (ψ := breathingCharacter) breathingCharacter_ne_one)

end UFRF.ComplexBreathing
