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
