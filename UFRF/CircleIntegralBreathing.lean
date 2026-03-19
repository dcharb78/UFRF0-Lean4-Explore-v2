import Mathlib.Analysis.Complex.CauchyIntegral
import UFRF.ResidueDefinition

/-!
# UFRF.CircleIntegralBreathing

This module provides the first honest circle-integral bridge for the specific
breathing function `z ↦ 1 / (z^13 - 1)`.

The scope is intentionally narrow. We do not introduce a general residue API or
claim a general residue theorem. Instead, we prove a concrete contour statement
around a single breathing root on a sufficiently small circle.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology
open UFRF.ComplexBreathing

namespace UFRF.CircleIntegralBreathing

/-- The cycle length inherited from the complex breathing interface. -/
abbrev CycleLen : ℕ := UFRF.ComplexBreathing.CycleLen

/--
The standard circle kernel integrates to `2πi` around any breathing root on a
positive-radius circle centered at that root.
-/
theorem circleIntegral_kernel_around_breathingRoot (k : ZMod CycleLen) {R : ℝ} (hR : 0 < R) :
    (∮ z in C(breathingRoot k, R), (z - breathingRoot k)⁻¹) = 2 * Real.pi * Complex.I := by
  exact circleIntegral.integral_sub_inv_of_mem_ball (by
    exact Metric.mem_ball_self hR)

/--
Because the local factor is continuous and nonzero at the chosen breathing
root, it stays nonzero on some sufficiently small closed ball around that root.
-/
theorem exists_pos_radius_localFactorAt_nonzero_closedBall (k : ZMod CycleLen) :
    ∃ R > 0, ∀ z : ℂ, z ∈ Metric.closedBall (breathingRoot k) R →
      UFRF.ResidueDefinition.localFactorAt k z ≠ 0 := by
  have hmem : {z : ℂ | UFRF.ResidueDefinition.localFactorAt k z ≠ 0} ∈ 𝓝 (breathingRoot k) := by
    exact (UFRF.ResidueDefinition.continuousAt_localFactorAt k (breathingRoot k)).preimage_mem_nhds
      (compl_singleton_mem_nhds (UFRF.ResidueDefinition.localFactorAt_root_ne_zero k))
  rcases Metric.mem_nhds_iff.mp hmem with ⟨R, hR, hsub⟩
  refine ⟨R / 2, by positivity, ?_⟩
  intro z hz
  apply hsub
  exact Metric.closedBall_subset_ball (by linarith) hz

/--
The desingularized breathing function attached to a chosen breathing root.

This is the punctured function from `ResidueDefinition`, now named so it can be
fed directly into Mathlib's punctured-center Cauchy formula.
-/
def desingularizedBreathingFunctionAt (k : ZMod CycleLen) (z : ℂ) : ℂ :=
  (z - breathingRoot k) * UFRF.ResidueDefinition.breathingFunction z

/--
Away from the chosen breathing root, the desingularized breathing function
agrees with the inverse local factor whenever the local factor is nonzero.
-/
theorem desingularizedBreathingFunctionAt_eq_inverse_localFactorAt
    (k : ZMod CycleLen) {z : ℂ} (hz : z ≠ breathingRoot k)
    (hlocal : UFRF.ResidueDefinition.localFactorAt k z ≠ 0) :
    desingularizedBreathingFunctionAt k z = (UFRF.ResidueDefinition.localFactorAt k z)⁻¹ := by
  have hden_ne : UFRF.ResidueDefinition.breathingDenominator z ≠ 0 := by
    intro hzero
    have hmul : UFRF.ResidueDefinition.localFactorAt k z * (z - breathingRoot k) = 0 := by
      simpa [hzero] using UFRF.ResidueDefinition.localFactorAt_mul_root_diff k z
    rcases mul_eq_zero.mp hmul with hfac | hdiff
    · exact hlocal hfac
    · exact hz (sub_eq_zero.mp hdiff)
  simpa [desingularizedBreathingFunctionAt] using
    UFRF.ResidueDefinition.punctured_breathingFunction_eq_inverse_localFactor k hden_ne

/--
On any closed ball where the local factor stays nonzero, the desingularized
breathing function is continuous away from the chosen breathing root.
-/
theorem continuousOn_desingularizedBreathingFunctionAt_punctured_closedBall
    (k : ZMod CycleLen) {R : ℝ}
    (hlocal : ∀ z : ℂ, z ∈ Metric.closedBall (breathingRoot k) R →
      UFRF.ResidueDefinition.localFactorAt k z ≠ 0) :
    ContinuousOn (desingularizedBreathingFunctionAt k)
      (Metric.closedBall (breathingRoot k) R \ {breathingRoot k}) := by
  let s : Set ℂ := Metric.closedBall (breathingRoot k) R \ {breathingRoot k}
  have hcontLocal : ContinuousOn (fun z : ℂ => UFRF.ResidueDefinition.localFactorAt k z) s := by
    intro z hz
    exact (UFRF.ResidueDefinition.continuousAt_localFactorAt k z).continuousWithinAt
  have hcontInv : ContinuousOn (fun z : ℂ => (UFRF.ResidueDefinition.localFactorAt k z)⁻¹) s :=
    hcontLocal.inv₀ (by intro z hz; exact hlocal z hz.1)
  refine hcontInv.congr ?_
  intro z hz
  exact desingularizedBreathingFunctionAt_eq_inverse_localFactorAt k hz.2 (hlocal z hz.1)

/--
On any closed ball where the local factor stays nonzero, the desingularized
breathing function is holomorphic on the corresponding punctured open ball.
-/
theorem differentiableOn_desingularizedBreathingFunctionAt_punctured_ball
    (k : ZMod CycleLen) {R : ℝ}
    (hlocal : ∀ z : ℂ, z ∈ Metric.closedBall (breathingRoot k) R →
      UFRF.ResidueDefinition.localFactorAt k z ≠ 0) :
    DifferentiableOn ℂ (desingularizedBreathingFunctionAt k)
      (Metric.ball (breathingRoot k) R \ {breathingRoot k}) := by
  let s : Set ℂ := Metric.ball (breathingRoot k) R \ {breathingRoot k}
  have hdiffLocal : DifferentiableOn ℂ (fun z : ℂ => UFRF.ResidueDefinition.localFactorAt k z) s := by
    intro z hz
    have hlf : DifferentiableAt ℂ (UFRF.ResidueDefinition.localFactorAt k) z := by
      simpa [UFRF.ResidueDefinition.localFactorAt] using
        (by fun_prop : DifferentiableAt ℂ (fun w : ℂ =>
          ∑ i ∈ Finset.range CycleLen,
            w ^ i * breathingRoot k ^ (CycleLen - 1 - i)) z)
    exact hlf.differentiableWithinAt
  have hdiffInv : DifferentiableOn ℂ (fun z : ℂ => (UFRF.ResidueDefinition.localFactorAt k z)⁻¹) s :=
    hdiffLocal.inv (by intro z hz; exact hlocal z (Metric.ball_subset_closedBall hz.1))
  refine hdiffInv.congr ?_
  intro z hz
  exact desingularizedBreathingFunctionAt_eq_inverse_localFactorAt k hz.2
    (hlocal z (Metric.ball_subset_closedBall hz.1))

/--
On any positive-radius closed ball where the local factor stays nonzero, the
circle integral of the specific breathing function equals `2πi` times the
explicit residue candidate at the enclosed breathing root.
-/
theorem circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate
    (k : ZMod CycleLen) {R : ℝ} (hR : 0 < R)
    (hlocal : ∀ z : ℂ, z ∈ Metric.closedBall (breathingRoot k) R →
      UFRF.ResidueDefinition.localFactorAt k z ≠ 0) :
    (∮ z in C(breathingRoot k, R), UFRF.ResidueDefinition.breathingFunction z) =
      (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt k := by
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => (UFRF.ResidueDefinition.localFactorAt k z)⁻¹)
      (Metric.closedBall (breathingRoot k) R) := by
    intro z hz
    have hlf : DifferentiableAt ℂ (UFRF.ResidueDefinition.localFactorAt k) z := by
      simpa [UFRF.ResidueDefinition.localFactorAt] using
        (by fun_prop : DifferentiableAt ℂ (fun w : ℂ =>
          ∑ i ∈ Finset.range CycleLen,
            w ^ i * breathingRoot k ^ (CycleLen - 1 - i)) z)
    exact (hlf.inv (hlocal z hz)).differentiableWithinAt
  have hroot_mem : breathingRoot k ∈ Metric.ball (breathingRoot k) R := by
    exact Metric.mem_ball_self hR
  have hCauchy :
      (∮ z in C(breathingRoot k, R),
        (z - breathingRoot k)⁻¹ * (UFRF.ResidueDefinition.localFactorAt k z)⁻¹) =
        (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt k := by
    simpa [smul_eq_mul,
      UFRF.ResidueDefinition.residueCandidateAt_eq_inverse_localFactorAt_root] using
      hdiff.circleIntegral_sub_inv_smul hroot_mem
  have hEqOn : EqOn
      (fun z : ℂ => (z - breathingRoot k)⁻¹ * (UFRF.ResidueDefinition.localFactorAt k z)⁻¹)
      UFRF.ResidueDefinition.breathingFunction
      (Metric.sphere (breathingRoot k) R) := by
    intro z hz
    have hz_ne : z ≠ breathingRoot k := by
      intro hz_eq
      rw [hz_eq, Metric.mem_sphere, dist_self] at hz
      exact hR.ne' hz.symm
    have hz_closed : z ∈ Metric.closedBall (breathingRoot k) R := Metric.sphere_subset_closedBall hz
    have hlocal_ne : UFRF.ResidueDefinition.localFactorAt k z ≠ 0 := hlocal z hz_closed
    rw [UFRF.ResidueDefinition.breathingFunction,
      ← UFRF.ResidueDefinition.localFactorAt_mul_root_diff k z]
    field_simp [hlocal_ne, hz_ne]
  calc
    (∮ z in C(breathingRoot k, R), UFRF.ResidueDefinition.breathingFunction z)
        = ∮ z in C(breathingRoot k, R),
            (z - breathingRoot k)⁻¹ * (UFRF.ResidueDefinition.localFactorAt k z)⁻¹ := by
              refine circleIntegral.integral_congr hR.le ?_
              intro z hz
              symm
              exact hEqOn hz
    _ = (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt k := hCauchy

/--
The same contour formula can also be derived directly from the punctured
simple-pole limit in `ResidueDefinition`.

This theorem makes the Phase 2 → Phase 3 bridge explicit: the local limit
theorem, together with punctured-disk regularity of the desingularized
function, feeds directly into Mathlib's punctured-center Cauchy formula.
-/
theorem circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_via_simplePole_limit
    (k : ZMod CycleLen) {R : ℝ} (hR : 0 < R)
    (hlocal : ∀ z : ℂ, z ∈ Metric.closedBall (breathingRoot k) R →
      UFRF.ResidueDefinition.localFactorAt k z ≠ 0) :
    (∮ z in C(breathingRoot k, R), UFRF.ResidueDefinition.breathingFunction z) =
      (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt k := by
  have hcont := continuousOn_desingularizedBreathingFunctionAt_punctured_closedBall k hlocal
  have hdiff := differentiableOn_desingularizedBreathingFunctionAt_punctured_ball k hlocal
  have hopen : IsOpen (Metric.ball (breathingRoot k) R \ {breathingRoot k}) := by
    simpa [Set.diff_eq, inter_comm] using Metric.isOpen_ball.inter isOpen_compl_singleton
  have hlim : Tendsto (desingularizedBreathingFunctionAt k)
      (𝓝[≠] (breathingRoot k)) (𝓝 (UFRF.ResidueDefinition.residueCandidateAt k)) := by
    simpa [desingularizedBreathingFunctionAt] using
      (UFRF.ResidueDefinition.breathingFunction_simplePole_limit k)
  have hcenter :
      (∮ z in C(breathingRoot k, R),
        (z - breathingRoot k)⁻¹ * desingularizedBreathingFunctionAt k z) =
        (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt k := by
    simpa [smul_eq_mul] using
      Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
        (c := breathingRoot k) (R := R) hR countable_empty hcont
        (by
          intro z hz
          have hz' : z ∈ Metric.ball (breathingRoot k) R \ {breathingRoot k} := by
            simpa [diff_empty] using hz
          exact (hdiff z hz').differentiableAt (hopen.mem_nhds hz'))
        hlim
  have hEqOn : EqOn
      (fun z : ℂ => (z - breathingRoot k)⁻¹ * desingularizedBreathingFunctionAt k z)
      UFRF.ResidueDefinition.breathingFunction
      (Metric.sphere (breathingRoot k) R) := by
    intro z hz
    have hz_ne : z ≠ breathingRoot k := by
      intro hz_eq
      rw [hz_eq, Metric.mem_sphere, dist_self] at hz
      exact hR.ne' hz.symm
    change (z - breathingRoot k)⁻¹ * ((z - breathingRoot k) * UFRF.ResidueDefinition.breathingFunction z) =
      UFRF.ResidueDefinition.breathingFunction z
    rw [← mul_assoc]
    have hmul : (z - breathingRoot k)⁻¹ * (z - breathingRoot k) = 1 := by
      rw [inv_mul_cancel₀]
      exact sub_ne_zero.mpr hz_ne
    rw [hmul, one_mul]
  calc
    (∮ z in C(breathingRoot k, R), UFRF.ResidueDefinition.breathingFunction z)
        = ∮ z in C(breathingRoot k, R),
            (z - breathingRoot k)⁻¹ * desingularizedBreathingFunctionAt k z := by
              refine circleIntegral.integral_congr hR.le ?_
              intro z hz
              symm
              exact hEqOn hz
    _ = (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt k := hcenter

/--
Every breathing root admits some sufficiently small positive-radius circle on
which the breathing function integrates to `2πi` times the explicit residue
candidate at that root.
-/
theorem exists_pos_radius_circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate
    (k : ZMod CycleLen) :
    ∃ R > 0,
      (∮ z in C(breathingRoot k, R), UFRF.ResidueDefinition.breathingFunction z) =
        (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt k := by
  rcases exists_pos_radius_localFactorAt_nonzero_closedBall k with ⟨R, hR, hlocal⟩
  exact ⟨R, hR, circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate k hR hlocal⟩

end UFRF.CircleIntegralBreathing
