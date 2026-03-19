import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import UFRF.ComplexBreathing

/-!
# UFRF.ResidueDefinition

This module begins the complex-residue layer for the specific rational function
`z ↦ 1 / (z^13 - 1)`.

The emphasis here is deliberate: we do **not** claim a general residue theorem
yet. Instead, we formalize the concrete root and derivative data, together with
the punctured simple-pole limit, for this one explicitly controlled function.
-/

noncomputable section

open Complex Filter
open scoped BigOperators Topology
open UFRF.ComplexBreathing

namespace UFRF.ResidueDefinition

/-- The cycle length inherited from the complex breathing interface. -/
abbrev CycleLen : ℕ := UFRF.ComplexBreathing.CycleLen

/-- The breathing denominator `z^13 - 1`. -/
def breathingDenominator (z : ℂ) : ℂ := z ^ CycleLen - 1

/-- The specific rational function whose poles sit at the breathing roots. -/
def breathingFunction (z : ℂ) : ℂ := 1 / breathingDenominator z

/--
The finite geometric factor appearing when `z^13 - 1` is expanded around a
chosen breathing root.
-/
def localFactorAt (k : ZMod CycleLen) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range CycleLen, z ^ i * breathingRoot k ^ (CycleLen - 1 - i)

/-- The inherited cycle length is exactly `13`. -/
theorem cycleLen_eq_thirteen : CycleLen = 13 := by
  simp [CycleLen, UFRF.ComplexBreathing.CycleLen, FourierCycleLen,
    BreathingCycle.cycle_len, UFRF.Foundation.derived_cycle_length,
    UFRF.Foundation.trinity_dimension, UFRF.Structure13.projective_order]

/-- The cycle length is positive. -/
theorem cycleLen_pos : 0 < CycleLen := by
  rw [cycleLen_eq_thirteen]
  norm_num

/-- Breathing roots are nonzero because they are roots of unity. -/
theorem breathingRoot_ne_zero (k : ZMod CycleLen) : breathingRoot k ≠ 0 := by
  intro hk
  have hpow := breathingRoot_pow_cycleLen_eq_one k
  rw [hk] at hpow
  norm_num [CycleLen, UFRF.ComplexBreathing.CycleLen, FourierCycleLen,
    BreathingCycle.cycle_len, UFRF.Foundation.derived_cycle_length,
    UFRF.Foundation.trinity_dimension, UFRF.Structure13.projective_order] at hpow

/-- Every breathing root is a zero of the denominator `z^13 - 1`. -/
theorem breathingDenominator_vanishes_at_root (k : ZMod CycleLen) :
    breathingDenominator (breathingRoot k) = 0 := by
  simp [breathingDenominator, breathingRoot_pow_cycleLen_eq_one]

/--
Exact local factorization of `z^13 - 1` around a chosen breathing root.

This is the finite geometric-series identity specialized to the breathing cycle.
-/
theorem localFactorAt_mul_root_diff (k : ZMod CycleLen) (z : ℂ) :
    localFactorAt k z * (z - breathingRoot k) = breathingDenominator z := by
  calc
    localFactorAt k z * (z - breathingRoot k)
        = z ^ CycleLen - breathingRoot k ^ CycleLen := by
            simpa [localFactorAt] using geom_sum₂_mul z (breathingRoot k) CycleLen
    _ = z ^ CycleLen - 1 := by rw [breathingRoot_pow_cycleLen_eq_one]
    _ = breathingDenominator z := by simp [breathingDenominator]

/-- Derivative formula for the denominator. -/
theorem breathingDenominator_deriv (z : ℂ) :
    deriv breathingDenominator z = (CycleLen : ℂ) * z ^ (CycleLen - 1) := by
  change deriv (fun w : ℂ => w ^ CycleLen - 1) z = (CycleLen : ℂ) * z ^ (CycleLen - 1)
  simp

/--
At a breathing root, the predecessor power collapses to the multiplicative inverse.

This is the algebraic core of the simple-pole formula for `z^13 - 1`.
-/
theorem breathingRoot_pow_pred_eq_inv (k : ZMod CycleLen) :
    breathingRoot k ^ (CycleLen - 1) = (breathingRoot k)⁻¹ := by
  have hmul : breathingRoot k ^ (CycleLen - 1) * breathingRoot k = 1 := by
    calc
      breathingRoot k ^ (CycleLen - 1) * breathingRoot k
          = breathingRoot k ^ (CycleLen - 1) * breathingRoot k ^ 1 := by simp
      _ = breathingRoot k ^ ((CycleLen - 1) + 1) := by rw [← pow_add]
      _ = breathingRoot k ^ CycleLen := by
          rw [Nat.sub_add_cancel (Nat.succ_le_of_lt cycleLen_pos)]
      _ = 1 := breathingRoot_pow_cycleLen_eq_one k
  field_simp [breathingRoot_ne_zero k]
  simpa [mul_comm] using hmul

/-- The derivative of `z^13 - 1` at a breathing root has the expected reciprocal form. -/
theorem breathingDenominator_deriv_at_root_eq_div (k : ZMod CycleLen) :
    deriv breathingDenominator (breathingRoot k) = (CycleLen : ℂ) / breathingRoot k := by
  calc
    deriv breathingDenominator (breathingRoot k)
        = (CycleLen : ℂ) * breathingRoot k ^ (CycleLen - 1) := by
            simpa using breathingDenominator_deriv (breathingRoot k)
    _ = (CycleLen : ℂ) * (breathingRoot k)⁻¹ := by
          rw [breathingRoot_pow_pred_eq_inv]
    _ = (CycleLen : ℂ) / breathingRoot k := by
          simp [div_eq_mul_inv]

/-- The derivative at a breathing root is nonzero, so the poles are simple at the denominator level. -/
theorem breathingDenominator_deriv_at_root_ne_zero (k : ZMod CycleLen) :
    deriv breathingDenominator (breathingRoot k) ≠ 0 := by
  rw [breathingDenominator_deriv_at_root_eq_div]
  exact div_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne CycleLen)) (breathingRoot_ne_zero k)

/--
Evaluating the local factor at the breathing root recovers the denominator derivative.

This is the exact algebraic bridge between the geometric-factor expansion and
the simple-pole derivative formula.
-/
theorem localFactorAt_root_eq_deriv (k : ZMod CycleLen) :
    localFactorAt k (breathingRoot k) = deriv breathingDenominator (breathingRoot k) := by
  rw [breathingDenominator_deriv]
  unfold localFactorAt
  have hconst :
      ∑ i ∈ Finset.range CycleLen,
        breathingRoot k ^ i * breathingRoot k ^ (CycleLen - 1 - i)
        = ∑ i ∈ Finset.range CycleLen, breathingRoot k ^ (CycleLen - 1) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← pow_add]
    congr 1
    rw [Finset.mem_range] at hi
    omega
  rw [hconst]
  simp

/-- The local factor at the root also has the reciprocal form `13 / ω_k`. -/
theorem localFactorAt_root_eq_div (k : ZMod CycleLen) :
    localFactorAt k (breathingRoot k) = (CycleLen : ℂ) / breathingRoot k := by
  rw [localFactorAt_root_eq_deriv, breathingDenominator_deriv_at_root_eq_div]

/-- The local factor is continuous as a finite polynomial expression. -/
theorem continuousAt_localFactorAt (k : ZMod CycleLen) (z : ℂ) :
    ContinuousAt (localFactorAt k) z := by
  simpa [localFactorAt] using
    (by fun_prop : ContinuousAt
      (fun w : ℂ => ∑ i ∈ Finset.range CycleLen,
        w ^ i * breathingRoot k ^ (CycleLen - 1 - i)) z)

/-- The local factor does not vanish at the chosen breathing root. -/
theorem localFactorAt_root_ne_zero (k : ZMod CycleLen) :
    localFactorAt k (breathingRoot k) ≠ 0 := by
  rw [localFactorAt_root_eq_div]
  exact div_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne CycleLen)) (breathingRoot_ne_zero k)

/--
The explicit residue candidate attached to a breathing root.

This is the explicit residue value for the simple pole of
`1 / (z^13 - 1)` at a breathing root. The conservative name is retained while
the API remains specific to this one function.
-/
def residueCandidateAt (k : ZMod CycleLen) : ℂ := ((CycleLen : ℂ)⁻¹) * breathingRoot k

/-- The candidate takes the familiar form `ω_k / 13`. -/
theorem residueCandidateAt_eq_div (k : ZMod CycleLen) :
    residueCandidateAt k = breathingRoot k / CycleLen := by
  simp [residueCandidateAt, div_eq_mul_inv, mul_comm]

/-- The candidate is the inverse of the denominator derivative at the root. -/
theorem residueCandidateAt_eq_inverse_deriv (k : ZMod CycleLen) :
    residueCandidateAt k = (deriv breathingDenominator (breathingRoot k))⁻¹ := by
  rw [residueCandidateAt_eq_div, breathingDenominator_deriv_at_root_eq_div]
  field_simp [breathingRoot_ne_zero k, Nat.cast_ne_zero.mpr (NeZero.ne CycleLen)]

/-- The residue candidate is also the inverse of the local factor at the breathing root. -/
theorem residueCandidateAt_eq_inverse_localFactorAt_root (k : ZMod CycleLen) :
    residueCandidateAt k = (localFactorAt k (breathingRoot k))⁻¹ := by
  rw [localFactorAt_root_eq_deriv]
  exact residueCandidateAt_eq_inverse_deriv k

/--
The explicit residue candidates still cancel over a full breathing cycle.

This is the global algebraic cancellation statement that the later contour
integral layer will inherit.
-/
theorem total_residue_candidate_zero :
    ∑ k : ZMod CycleLen, residueCandidateAt k = 0 := by
  rw [show (∑ k : ZMod CycleLen, residueCandidateAt k) =
      ((CycleLen : ℂ)⁻¹) * ∑ k : ZMod CycleLen, breathingRoot k by
        simp [residueCandidateAt, Finset.mul_sum]]
  simp [complete_breath_sums_to_zero]

/--
Away from denominator zeros, the punctured function desingularizes to the
inverse local factor.

This is the exact algebraic identity used to prove the local simple-pole limit.
-/
theorem punctured_breathingFunction_eq_inverse_localFactor (k : ZMod CycleLen) {z : ℂ}
    (hz : breathingDenominator z ≠ 0) :
    (z - breathingRoot k) * breathingFunction z = (localFactorAt k z)⁻¹ := by
  have hfac : localFactorAt k z * (z - breathingRoot k) = breathingDenominator z :=
    localFactorAt_mul_root_diff k z
  have hlocal : localFactorAt k z ≠ 0 := by
    intro h0
    apply hz
    rw [← hfac, h0, zero_mul]
  have hdiff : z - breathingRoot k ≠ 0 := by
    intro h0
    apply hz
    rw [← hfac, h0, mul_zero]
  rw [breathingFunction, ← hfac]
  field_simp [hlocal, hdiff]

/--
Near a breathing root, the local factor stays nonzero on punctured neighborhoods.

This is the continuity input that lets the simple-pole limit reduce to the
inverse local factor.
-/
theorem eventually_localFactorAt_ne_zero_punctured (k : ZMod CycleLen) :
    ∀ᶠ z : ℂ in 𝓝[≠] (breathingRoot k), localFactorAt k z ≠ 0 := by
  exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
    (ContinuousAt.preimage_mem_nhds (continuousAt_localFactorAt k (breathingRoot k))
      (compl_singleton_mem_nhds (localFactorAt_root_ne_zero k)))

/--
Near a breathing root, the denominator `z^13 - 1` vanishes only at the root itself.

This is the punctured-neighborhood nonvanishing statement needed for the local
simple-pole limit.
-/
theorem eventually_breathingDenominator_ne_zero_punctured (k : ZMod CycleLen) :
    ∀ᶠ z : ℂ in 𝓝[≠] (breathingRoot k), breathingDenominator z ≠ 0 := by
  filter_upwards [eventually_localFactorAt_ne_zero_punctured k,
    (eventually_mem_nhdsWithin :
      ∀ᶠ z : ℂ in 𝓝[≠] (breathingRoot k), z ∈ ({breathingRoot k}ᶜ : Set ℂ))] with z
      hlocal hz
  intro hzero
  have hmul : localFactorAt k z * (z - breathingRoot k) = 0 := by
    simpa [hzero] using localFactorAt_mul_root_diff k z
  rcases mul_eq_zero.mp hmul with hfac | hdiff
  · exact hlocal hfac
  · exact hz (sub_eq_zero.mp hdiff)

/--
The punctured simple-pole limit for the specific breathing function `1 / (z^13 - 1)`.

This is the first honest analytic residue-style statement in the pipeline: the
desingularized function tends to the explicit residue candidate `ω_k / 13`.
-/
theorem breathingFunction_simplePole_limit (k : ZMod CycleLen) :
    Tendsto (fun z : ℂ => (z - breathingRoot k) * breathingFunction z)
      (𝓝[≠] (breathingRoot k)) (𝓝 (residueCandidateAt k)) := by
  have h_inverse_limit :
      Tendsto (fun z : ℂ => (localFactorAt k z)⁻¹)
        (𝓝[≠] (breathingRoot k)) (𝓝 (residueCandidateAt k)) := by
    have hcont :
        ContinuousAt (fun z : ℂ => (localFactorAt k z)⁻¹) (breathingRoot k) :=
      (continuousAt_localFactorAt k (breathingRoot k)).inv₀ (localFactorAt_root_ne_zero k)
    have ht :
        Tendsto (fun z : ℂ => (localFactorAt k z)⁻¹)
          (𝓝[≠] (breathingRoot k)) (𝓝 ((localFactorAt k (breathingRoot k))⁻¹)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    convert ht using 1
    rw [← residueCandidateAt_eq_inverse_localFactorAt_root]
  have h_eventually_eq :
      (fun z : ℂ => (localFactorAt k z)⁻¹) =ᶠ[𝓝[≠] (breathingRoot k)]
        (fun z : ℂ => (z - breathingRoot k) * breathingFunction z) := by
    filter_upwards [eventually_breathingDenominator_ne_zero_punctured k] with z hz
    symm
    exact punctured_breathingFunction_eq_inverse_localFactor k hz
  exact Tendsto.congr' h_eventually_eq h_inverse_limit

end UFRF.ResidueDefinition
