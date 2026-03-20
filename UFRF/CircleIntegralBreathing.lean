import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Infsep
import UFRF.ResidueDefinition

/-!
# UFRF.CircleIntegralBreathing

This module provides the first honest circle-integral bridge for the specific
breathing function `z ↦ 1 / (z^13 - 1)`.

The scope is intentionally narrow. We do not introduce a general residue API or
claim a general residue theorem. Instead, we prove concrete contour statements
for the specific breathing function, first on small circles around individual
breathing roots and then on explicit origin-centered enclosing circles.
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
For a fixed pole label `k`, the local factor vanishes at every other breathing
root `breathingRoot j` with `j ≠ k`.
-/
theorem localFactorAt_vanishes_at_other_breathingRoot
    (k j : ZMod CycleLen) (hjk : j ≠ k) :
    UFRF.ResidueDefinition.localFactorAt k (breathingRoot j) = 0 := by
  have hmul :=
    UFRF.ResidueDefinition.localFactorAt_mul_root_diff k (breathingRoot j)
  rw [UFRF.ResidueDefinition.breathingDenominator_vanishes_at_root j] at hmul
  have hroot_ne : breathingRoot j - breathingRoot k ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hroot
    exact hjk (UFRF.ComplexBreathing.breathingRoot_injective hroot)
  exact (mul_eq_zero.mp hmul).resolve_right hroot_ne

/--
On a sufficiently small closed ball around a chosen breathing root, the
denominator `z^13 - 1` vanishes only at that root.
-/
theorem exists_pos_radius_closedBall_zero_unique_for_breathingDenominator
    (k : ZMod CycleLen) :
    ∃ R > 0, ∀ z : ℂ, z ∈ Metric.closedBall (breathingRoot k) R →
      UFRF.ResidueDefinition.breathingDenominator z = 0 → z = breathingRoot k := by
  rcases exists_pos_radius_localFactorAt_nonzero_closedBall k with ⟨R, hR, hlocal⟩
  refine ⟨R, hR, ?_⟩
  intro z hz hzero
  have hmul : UFRF.ResidueDefinition.localFactorAt k z * (z - breathingRoot k) = 0 := by
    simpa [hzero] using UFRF.ResidueDefinition.localFactorAt_mul_root_diff k z
  have hlocal_ne : UFRF.ResidueDefinition.localFactorAt k z ≠ 0 := hlocal z hz
  rcases mul_eq_zero.mp hmul with hfac | hdiff
  · exact False.elim (hlocal_ne hfac)
  · exact sub_eq_zero.mp hdiff

/--
Every chosen breathing root admits a sufficiently small closed ball that
contains no other breathing root.
-/
theorem exists_pos_radius_closedBall_excludes_other_breathingRoots
    (k : ZMod CycleLen) :
    ∃ R > 0, ∀ j : ZMod CycleLen, j ≠ k →
      breathingRoot j ∉ Metric.closedBall (breathingRoot k) R := by
  rcases exists_pos_radius_closedBall_zero_unique_for_breathingDenominator k with
    ⟨R, hR, hunique⟩
  refine ⟨R, hR, ?_⟩
  intro j hj hjmem
  have heq : breathingRoot j = breathingRoot k :=
    hunique (breathingRoot j) hjmem
      (UFRF.ResidueDefinition.breathingDenominator_vanishes_at_root j)
  exact hj (UFRF.ComplexBreathing.breathingRoot_injective heq)

/--
Every chosen breathing root admits a strictly positive distance buffer to every
other breathing root.
-/
theorem exists_pos_radius_lt_dist_other_breathingRoots
    (k : ZMod CycleLen) :
    ∃ R > 0, ∀ j : ZMod CycleLen, j ≠ k →
      R < dist (breathingRoot k) (breathingRoot j) := by
  rcases exists_pos_radius_closedBall_excludes_other_breathingRoots k with
    ⟨R, hR, hexcl⟩
  refine ⟨R, hR, ?_⟩
  intro j hj
  have hnot : breathingRoot j ∉ Metric.closedBall (breathingRoot k) R := hexcl j hj
  rw [Metric.mem_closedBall, not_le] at hnot
  simpa [dist_comm] using hnot

/--
The full breathing-root configuration has a strictly positive global infimum
separation in the complex plane.
-/
theorem breathingRootSet_infsep_pos :
    0 < (Set.range breathingRoot : Set ℂ).infsep := by
  have hfinite : (Set.range breathingRoot : Set ℂ).Finite := Set.finite_range breathingRoot
  have hnontrivial : (Set.range breathingRoot : Set ℂ).Nontrivial := by
    refine ⟨breathingRoot 0, ⟨0, rfl⟩, breathingRoot 1, ⟨1, rfl⟩, ?_⟩
    intro hroot
    have h01 : (0 : ZMod CycleLen) = 1 :=
      UFRF.ComplexBreathing.breathingRoot_injective hroot
    exact zero_ne_one h01
  exact (hfinite.infsep_pos_iff_nontrivial).2 hnontrivial

/--
Half of the global breathing-root infimum separation is still strictly smaller
than the distance between any two distinct breathing roots.
-/
theorem half_infsep_lt_dist_breathingRoots {j k : ZMod CycleLen} (hjk : j ≠ k) :
    ((Set.range breathingRoot : Set ℂ).infsep) / 2 <
      dist (breathingRoot j) (breathingRoot k) := by
  have hpos : 0 < (Set.range breathingRoot : Set ℂ).infsep := breathingRootSet_infsep_pos
  have hjmem : breathingRoot j ∈ (Set.range breathingRoot : Set ℂ) := ⟨j, rfl⟩
  have hkmem : breathingRoot k ∈ (Set.range breathingRoot : Set ℂ) := ⟨k, rfl⟩
  have hroot_ne : breathingRoot j ≠ breathingRoot k := by
    intro hroot
    have hjk_eq : j = k := UFRF.ComplexBreathing.breathingRoot_injective hroot
    exact hjk hjk_eq
  have hle :
      (Set.range breathingRoot : Set ℂ).infsep ≤
        dist (breathingRoot j) (breathingRoot k) :=
    Set.infsep_le_dist_of_mem hjmem hkmem hroot_ne
  exact (half_lt_self hpos).trans_le hle

/--
The canonical radius `infsep(range breathingRoot) / 2` excludes every other
breathing root from the closed ball around a chosen breathing root.
-/
theorem half_infsep_closedBall_excludes_other_breathingRoots
    (k : ZMod CycleLen) :
    ∀ j : ZMod CycleLen, j ≠ k →
      breathingRoot j ∉ Metric.closedBall (breathingRoot k)
        (((Set.range breathingRoot : Set ℂ).infsep) / 2) := by
  intro j hj
  rw [Metric.mem_closedBall, not_le]
  simpa [dist_comm] using half_infsep_lt_dist_breathingRoots (j := k) (k := j) hj.symm

/--
Every zero of the denominator `z^13 - 1` is one of the breathing roots.

This packages the full zero set of the specific denominator into the existing
`breathingRoot` interface without introducing any general residue API.
-/
theorem exists_breathingRoot_of_breathingDenominator_eq_zero {z : ℂ}
    (hz : UFRF.ResidueDefinition.breathingDenominator z = 0) :
    ∃ j : ZMod CycleLen, z = breathingRoot j := by
  have hzpow : z ^ CycleLen = 1 := by
    rw [UFRF.ResidueDefinition.breathingDenominator] at hz
    exact sub_eq_zero.mp hz
  let ζ : rootsOfUnity CycleLen ℂ := rootsOfUnity.mkOfPowEq z hzpow
  obtain ⟨j, hj⟩ :=
    surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar CycleLen ζ
  refine ⟨j, ?_⟩
  have hval := congrArg (fun w : rootsOfUnity CycleLen ℂ => ((w : ℂˣ) : ℂ)) hj
  simpa [ζ, breathingRootOfUnity, breathingRootOfUnity_val] using hval.symm

/--
On the canonical half-`infsep` closed ball around `breathingRoot k`, the local
factor `localFactorAt k` never vanishes.

This is the quantitative bridge that upgrades the earlier existential
nonvanishing radius into a canonical radius derived from the full breathing-root
configuration.
-/
theorem localFactorAt_nonzero_closedBall_half_infsep
    (k : ZMod CycleLen) :
    ∀ z : ℂ,
      z ∈ Metric.closedBall (breathingRoot k)
        (((Set.range breathingRoot : Set ℂ).infsep) / 2) →
      UFRF.ResidueDefinition.localFactorAt k z ≠ 0 := by
  intro z hzball hzero
  have hden_zero : UFRF.ResidueDefinition.breathingDenominator z = 0 := by
    rw [← UFRF.ResidueDefinition.localFactorAt_mul_root_diff k z, hzero, zero_mul]
  obtain ⟨j, hjz⟩ := exists_breathingRoot_of_breathingDenominator_eq_zero hden_zero
  subst hjz
  by_cases hj : j = k
  · subst hj
    exact UFRF.ResidueDefinition.localFactorAt_root_ne_zero j hzero
  · exact (half_infsep_closedBall_excludes_other_breathingRoots k j hj) hzball

/--
The canonical open balls of radius `infsep(range breathingRoot) / 2` around
distinct breathing roots are disjoint.
-/
theorem disjoint_ball_half_infsep_breathingRoots {j k : ZMod CycleLen} (hjk : j ≠ k) :
    Disjoint
      (Metric.ball (breathingRoot j) (((Set.range breathingRoot : Set ℂ).infsep) / 2))
      (Metric.ball (breathingRoot k) (((Set.range breathingRoot : Set ℂ).infsep) / 2)) := by
  refine Set.disjoint_left.2 ?_
  intro z hzj hzk
  have hdist_le :
      (Set.range breathingRoot : Set ℂ).infsep ≤ dist (breathingRoot j) (breathingRoot k) :=
    Set.infsep_le_dist_of_mem ⟨j, rfl⟩ ⟨k, rfl⟩ (by
      intro hroot
      exact hjk (UFRF.ComplexBreathing.breathingRoot_injective hroot))
  have hdist_lt :
      dist (breathingRoot j) (breathingRoot k) < (Set.range breathingRoot : Set ℂ).infsep := by
    calc
      dist (breathingRoot j) (breathingRoot k)
          ≤ dist (breathingRoot j) z + dist (breathingRoot k) z := dist_triangle_right _ _ _
      _ = dist (breathingRoot j) z + dist z (breathingRoot k) := by
          rw [dist_comm (breathingRoot k) z]
      _ < (((Set.range breathingRoot : Set ℂ).infsep) / 2) +
            (((Set.range breathingRoot : Set ℂ).infsep) / 2) := by
            exact add_lt_add
              (by simpa [Metric.mem_ball, dist_comm] using hzj)
              (by simpa [Metric.mem_ball] using hzk)
      _ = (Set.range breathingRoot : Set ℂ).infsep := by ring
  exact not_lt_of_ge hdist_le hdist_lt

/--
Any common radius strictly smaller than `infsep(range breathingRoot) / 2`
produces pairwise disjoint closed balls around distinct breathing roots.
-/
theorem disjoint_closedBall_of_lt_half_infsep_breathingRoots
    {R : ℝ}
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep) / 2)
    {j k : ZMod CycleLen} (hjk : j ≠ k) :
    Disjoint
      (Metric.closedBall (breathingRoot j) R)
      (Metric.closedBall (breathingRoot k) R) := by
  refine Set.disjoint_left.2 ?_
  intro z hzj hzk
  have hdist_le :
      (Set.range breathingRoot : Set ℂ).infsep ≤ dist (breathingRoot j) (breathingRoot k) :=
    Set.infsep_le_dist_of_mem ⟨j, rfl⟩ ⟨k, rfl⟩ (by
      intro hroot
      exact hjk (UFRF.ComplexBreathing.breathingRoot_injective hroot))
  have hdist_lt :
      dist (breathingRoot j) (breathingRoot k) < (Set.range breathingRoot : Set ℂ).infsep := by
    calc
      dist (breathingRoot j) (breathingRoot k)
          ≤ dist (breathingRoot j) z + dist (breathingRoot k) z := dist_triangle_right _ _ _
      _ = dist (breathingRoot j) z + dist z (breathingRoot k) := by
          rw [dist_comm (breathingRoot k) z]
      _ ≤ R + R := by
            exact add_le_add
              (by simpa [Metric.mem_closedBall, dist_comm] using hzj)
              (by simpa [Metric.mem_closedBall] using hzk)
      _ < (Set.range breathingRoot : Set ℂ).infsep := by
          linarith
  exact not_lt_of_ge hdist_le hdist_lt

/--
Any common radius strictly smaller than `infsep(range breathingRoot) / 2`
also produces pairwise disjoint circles around distinct breathing roots.
-/
theorem disjoint_sphere_of_lt_half_infsep_breathingRoots
    {R : ℝ} (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep) / 2)
    {j k : ZMod CycleLen} (hjk : j ≠ k) :
    Disjoint
      (Metric.sphere (breathingRoot j) R)
      (Metric.sphere (breathingRoot k) R) := by
  exact (disjoint_closedBall_of_lt_half_infsep_breathingRoots (R := R) hRlt hjk).mono
    Metric.sphere_subset_closedBall Metric.sphere_subset_closedBall

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

/--
The breathing function integrates to `2πi` times the explicit residue
candidate on the canonical circle of radius `infsep(range breathingRoot) / 2`
around any chosen breathing root.
-/
theorem circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_half_infsep
    (k : ZMod CycleLen) :
    (∮ z in C(breathingRoot k, ((Set.range breathingRoot : Set ℂ).infsep / 2)),
      UFRF.ResidueDefinition.breathingFunction z) =
        (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt k := by
  have hR : 0 < ((Set.range breathingRoot : Set ℂ).infsep / 2) := by
    exact half_pos breathingRootSet_infsep_pos
  apply circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate k hR
  exact localFactorAt_nonzero_closedBall_half_infsep k

/--
On any circle around `breathingRoot k` with radius strictly less than
`infsep(range breathingRoot) / 2`, the breathing function integrates to
`2πi` times the explicit residue candidate at that root.

This packages the single-root contour formula at any common separated radius,
not only at the canonical half-`infsep` or quarter-`infsep` scales.
-/
theorem circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_of_lt_half_infsep
    (k : ZMod CycleLen) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (∮ z in C(breathingRoot k, R), UFRF.ResidueDefinition.breathingFunction z) =
      (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt k := by
  apply circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate k hR
  intro z hz
  apply localFactorAt_nonzero_closedBall_half_infsep k z
  exact Metric.closedBall_subset_closedBall hRlt.le hz

/--
On any closed annulus centered at `breathingRoot k` whose outer radius is
strictly smaller than `infsep(range breathingRoot) / 2`, the denominator
`z^13 - 1` does not vanish.
-/
theorem breathingDenominator_ne_zero_of_mem_closedBall_lt_half_infsep
    (k : ZMod CycleLen) {R : ℝ}
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep) / 2)
    {z : ℂ} (hz : z ∈ Metric.closedBall (breathingRoot k) R)
    (hzroot : z ≠ breathingRoot k) :
    UFRF.ResidueDefinition.breathingDenominator z ≠ 0 := by
  intro hzero
  have hlocal : UFRF.ResidueDefinition.localFactorAt k z ≠ 0 :=
    localFactorAt_nonzero_closedBall_half_infsep k z
      (Metric.closedBall_subset_closedBall hRlt.le hz)
  have hmul : UFRF.ResidueDefinition.localFactorAt k z * (z - breathingRoot k) = 0 := by
    simpa [hzero] using UFRF.ResidueDefinition.localFactorAt_mul_root_diff k z
  rcases mul_eq_zero.mp hmul with hfac | hdiff
  · exact hlocal hfac
  · exact hzroot (sub_eq_zero.mp hdiff)

/--
The breathing function is continuous on any closed annulus centered at
`breathingRoot k` whose outer radius is strictly smaller than
`infsep(range breathingRoot) / 2`.
-/
theorem continuousOn_breathingFunction_closedAnnulus_lt_half_infsep
    (k : ZMod CycleLen) {r R : ℝ} (hr : 0 < r)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep) / 2) :
    ContinuousOn UFRF.ResidueDefinition.breathingFunction
      (Metric.closedBall (breathingRoot k) R \ Metric.ball (breathingRoot k) r) := by
  let s : Set ℂ := Metric.closedBall (breathingRoot k) R \ Metric.ball (breathingRoot k) r
  have hcontDen : ContinuousOn UFRF.ResidueDefinition.breathingDenominator s := by
    intro z hz
    change ContinuousWithinAt (fun w : ℂ => w ^ UFRF.ResidueDefinition.CycleLen - (1 : ℂ)) s z
    fun_prop
  have hnonzero : ∀ z ∈ s, UFRF.ResidueDefinition.breathingDenominator z ≠ 0 := by
    intro z hz
    apply breathingDenominator_ne_zero_of_mem_closedBall_lt_half_infsep k hRlt hz.1
    intro hzroot
    exact hz.2 (by
      simpa [hzroot] using
        (Metric.mem_ball_self hr : breathingRoot k ∈ Metric.ball (breathingRoot k) r))
  simpa [UFRF.ResidueDefinition.breathingFunction] using
    (continuousOn_const.div hcontDen hnonzero)

/--
The breathing function is holomorphic on any open annulus centered at
`breathingRoot k` whose outer radius is strictly smaller than
`infsep(range breathingRoot) / 2`.
-/
theorem differentiableOn_breathingFunction_openAnnulus_lt_half_infsep
    (k : ZMod CycleLen) {r R : ℝ} (hr : 0 < r)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep) / 2) :
    DifferentiableOn ℂ UFRF.ResidueDefinition.breathingFunction
      (Metric.ball (breathingRoot k) R \ Metric.closedBall (breathingRoot k) r) := by
  let s : Set ℂ := Metric.ball (breathingRoot k) R \ Metric.closedBall (breathingRoot k) r
  have hdiffDen : DifferentiableOn ℂ UFRF.ResidueDefinition.breathingDenominator s := by
    intro z hz
    change DifferentiableWithinAt ℂ
      (fun w : ℂ => w ^ UFRF.ResidueDefinition.CycleLen - (1 : ℂ)) s z
    fun_prop
  have hnonzero : ∀ z ∈ s, UFRF.ResidueDefinition.breathingDenominator z ≠ 0 := by
    intro z hz
    apply breathingDenominator_ne_zero_of_mem_closedBall_lt_half_infsep k hRlt
      (Metric.ball_subset_closedBall hz.1)
    intro hzroot
    exact hz.2 (by
      simpa [Metric.mem_closedBall, hzroot, dist_self] using le_of_lt hr)
  have hconst : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s := by
    intro z hz
    exact (differentiableAt_const (c := (1 : ℂ))).differentiableWithinAt
  simpa [UFRF.ResidueDefinition.breathingFunction] using hconst.div hdiffDen hnonzero

/--
For any `0 < r ≤ R < infsep(range breathingRoot) / 2`, the circle integrals of
the breathing function over the two concentric circles centered at
`breathingRoot k` are equal.

This is a genuine same-center annulus comparison theorem. It does not yet
compare a family of disjoint inner circles to a single outer contour.
-/
theorem circleIntegral_breathingFunction_eq_of_le_lt_half_infsep
    (k : ZMod CycleLen) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep) / 2) :
    (∮ z in C(breathingRoot k, R), UFRF.ResidueDefinition.breathingFunction z) =
      ∮ z in C(breathingRoot k, r), UFRF.ResidueDefinition.breathingFunction z := by
  have hopen : IsOpen (Metric.ball (breathingRoot k) R \ Metric.closedBall (breathingRoot k) r) := by
    simpa [Set.diff_eq, inter_comm] using
      Metric.isOpen_ball.inter Metric.isClosed_closedBall.isOpen_compl
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    (c := breathingRoot k) (r := r) (R := R) hr hrR (s := ∅)
  · exact countable_empty
  · simpa using continuousOn_breathingFunction_closedAnnulus_lt_half_infsep k hr hRlt
  · intro z hz
    have hz' : z ∈ Metric.ball (breathingRoot k) R \ Metric.closedBall (breathingRoot k) r := by
      simpa [diff_empty] using hz
    have hdiff :=
      differentiableOn_breathingFunction_openAnnulus_lt_half_infsep k hr hRlt
    exact (hdiff z hz').differentiableAt (hopen.mem_nhds hz')

/--
For any finite family of breathing roots and any common radius
`0 < R < infsep(range breathingRoot) / 2`, the sum of the corresponding circle
integrals equals `2πi` times the sum of the explicit residue candidates.

This is the generic-radius finite multi-circle formula inside the separated
regime.
-/
theorem sum_circleIntegral_breathingFunction_of_lt_half_infsep_eq_two_pi_I_mul_sum_residueCandidate
    (S : Finset (ZMod CycleLen)) {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    Finset.sum S (fun k =>
      (∮ z in C(breathingRoot k, R), UFRF.ResidueDefinition.breathingFunction z)) =
      (2 * Real.pi * Complex.I) * Finset.sum S UFRF.ResidueDefinition.residueCandidateAt := by
  simp_rw [circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_of_lt_half_infsep
    (R := R) (hR := hR) (hRlt := hRlt)]
  rw [← Finset.mul_sum]

/--
For any finite family of breathing roots, the total separated-radius circle
integral is independent of the common radius as long as
`0 < r ≤ R < infsep(range breathingRoot) / 2`.

This is the finite-family same-center annular comparison theorem inside the
local separated regime.
-/
theorem sum_circleIntegral_breathingFunction_eq_of_le_lt_half_infsep
    (S : Finset (ZMod CycleLen)) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    Finset.sum S (fun k =>
      (∮ z in C(breathingRoot k, R), UFRF.ResidueDefinition.breathingFunction z)) =
      Finset.sum S (fun k =>
        (∮ z in C(breathingRoot k, r), UFRF.ResidueDefinition.breathingFunction z)) := by
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  rw [sum_circleIntegral_breathingFunction_of_lt_half_infsep_eq_two_pi_I_mul_sum_residueCandidate
    (S := S) (R := R) hR hRlt]
  rw [sum_circleIntegral_breathingFunction_of_lt_half_infsep_eq_two_pi_I_mul_sum_residueCandidate
    (S := S) (R := r) hr (lt_of_le_of_lt hrR hRlt)]

/--
For any common radius `0 < R < infsep(range breathingRoot) / 2`, the sum of the
breathing-function circle integrals over the full breathing-root family is zero.

This is the generic-radius all-roots cancellation theorem in the separated
regime.
-/
theorem sum_circleIntegral_breathingFunction_of_lt_half_infsep_allRoots_eq_zero
    {R : ℝ} (hR : 0 < R)
    (hRlt : R < ((Set.range breathingRoot : Set ℂ).infsep / 2)) :
    (∑ k : ZMod CycleLen,
      (∮ z in C(breathingRoot k, R), UFRF.ResidueDefinition.breathingFunction z)) = 0 := by
  rw [show (∑ k : ZMod CycleLen,
      (∮ z in C(breathingRoot k, R), UFRF.ResidueDefinition.breathingFunction z)) =
      Finset.sum Finset.univ (fun k : ZMod CycleLen =>
        (∮ z in C(breathingRoot k, R), UFRF.ResidueDefinition.breathingFunction z)) by rfl]
  rw [sum_circleIntegral_breathingFunction_of_lt_half_infsep_eq_two_pi_I_mul_sum_residueCandidate
    (S := Finset.univ) (R := R) hR hRlt]
  rw [UFRF.ResidueDefinition.total_residue_candidate_zero, mul_zero]

/-- Every breathing root lies on the unit circle in the complex plane. -/
theorem norm_breathingRoot_eq_one (k : ZMod CycleLen) :
    ‖breathingRoot k‖ = 1 := by
  change ‖((breathingRootOfUnity k).1 : ℂ)‖ = 1
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (breathingRootOfUnity k).2

/--
Outside the unit circle, the denominator `z^13 - 1` does not vanish.

This is the concrete outer-region nonvanishing theorem for the specific
breathing denominator.
-/
theorem breathingDenominator_ne_zero_of_one_lt_norm {z : ℂ}
    (hz : 1 < ‖z‖) :
    UFRF.ResidueDefinition.breathingDenominator z ≠ 0 := by
  intro hzero
  obtain ⟨j, rfl⟩ := exists_breathingRoot_of_breathingDenominator_eq_zero hzero
  rw [norm_breathingRoot_eq_one] at hz
  linarith

/--
The breathing function is continuous on every closed annulus centered at the
origin whose inner radius is strictly larger than `1`.
-/
theorem continuousOn_breathingFunction_closedAnnulus_of_one_lt
    {r R : ℝ} (hr : 1 < r) :
    ContinuousOn UFRF.ResidueDefinition.breathingFunction
      (Metric.closedBall (0 : ℂ) R \ Metric.ball (0 : ℂ) r) := by
  let s : Set ℂ := Metric.closedBall (0 : ℂ) R \ Metric.ball (0 : ℂ) r
  have hcontDen : ContinuousOn UFRF.ResidueDefinition.breathingDenominator s := by
    intro z hz
    change ContinuousWithinAt (fun w : ℂ => w ^ UFRF.ResidueDefinition.CycleLen - (1 : ℂ)) s z
    fun_prop
  have hnonzero : ∀ z ∈ s, UFRF.ResidueDefinition.breathingDenominator z ≠ 0 := by
    intro z hz
    have hzball : z ∉ Metric.ball (0 : ℂ) r := by
      simpa [s] using hz.2
    have hznorm : r ≤ ‖z‖ := by
      rw [Metric.mem_ball, not_lt, dist_eq_norm] at hzball
      simpa using hzball
    exact breathingDenominator_ne_zero_of_one_lt_norm (lt_of_lt_of_le hr hznorm)
  simpa [UFRF.ResidueDefinition.breathingFunction] using
    (continuousOn_const.div hcontDen hnonzero)

/--
The breathing function is holomorphic on every open annulus centered at the
origin whose inner radius is strictly larger than `1`.
-/
theorem differentiableOn_breathingFunction_openAnnulus_of_one_lt
    {r R : ℝ} (hr : 1 < r) :
    DifferentiableOn ℂ UFRF.ResidueDefinition.breathingFunction
      (Metric.ball (0 : ℂ) R \ Metric.closedBall (0 : ℂ) r) := by
  let s : Set ℂ := Metric.ball (0 : ℂ) R \ Metric.closedBall (0 : ℂ) r
  have hdiffDen : DifferentiableOn ℂ UFRF.ResidueDefinition.breathingDenominator s := by
    intro z hz
    change DifferentiableWithinAt ℂ
      (fun w : ℂ => w ^ UFRF.ResidueDefinition.CycleLen - (1 : ℂ)) s z
    fun_prop
  have hnonzero : ∀ z ∈ s, UFRF.ResidueDefinition.breathingDenominator z ≠ 0 := by
    intro z hz
    have hzclosed : z ∉ Metric.closedBall (0 : ℂ) r := by
      simpa [s] using hz.2
    have hznorm : r < ‖z‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hzclosed
      simpa using hzclosed
    exact breathingDenominator_ne_zero_of_one_lt_norm (lt_trans hr hznorm)
  have hconst : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) s := by
    intro z hz
    exact (differentiableAt_const (c := (1 : ℂ))).differentiableWithinAt
  simpa [UFRF.ResidueDefinition.breathingFunction] using hconst.div hdiffDen hnonzero

/--
For any `1 < r ≤ R`, the origin-centered circle integrals of the breathing
function over radii `r` and `R` agree.

This is the outer-annulus comparison theorem centered at the origin, outside
the unit circle that contains all breathing poles.
-/
theorem circleIntegral_breathingFunction_eq_of_one_lt_le
    {r R : ℝ} (hr : 1 < r) (hrR : r ≤ R) :
    (∮ z in C((0 : ℂ), R), UFRF.ResidueDefinition.breathingFunction z) =
      ∮ z in C((0 : ℂ), r), UFRF.ResidueDefinition.breathingFunction z := by
  have h0r : 0 < r := lt_trans zero_lt_one hr
  have hopen : IsOpen (Metric.ball (0 : ℂ) R \ Metric.closedBall (0 : ℂ) r) := by
    simpa [Set.diff_eq, inter_comm] using
      Metric.isOpen_ball.inter Metric.isClosed_closedBall.isOpen_compl
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    (c := (0 : ℂ)) (r := r) (R := R) h0r hrR (s := ∅)
  · exact countable_empty
  · simpa using continuousOn_breathingFunction_closedAnnulus_of_one_lt hr
  · intro z hz
    have hz' : z ∈ Metric.ball (0 : ℂ) R \ Metric.closedBall (0 : ℂ) r := by
      simpa [diff_empty] using hz
    have hdiff := differentiableOn_breathingFunction_openAnnulus_of_one_lt (r := r) (R := R) hr
    exact (hdiff z hz').differentiableAt (hopen.mem_nhds hz')

/--
On a circle centered at the origin with radius at least `2`, the breathing
function is uniformly bounded by `2 / R^13`.

This is the quantitative decay input used to force the outer contour integral
to vanish.
-/
theorem norm_breathingFunction_le_two_div_radius_pow_of_mem_sphere_of_two_le
    {R : ℝ} (hR2 : 2 ≤ R) {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) R) :
    ‖UFRF.ResidueDefinition.breathingFunction z‖ ≤ 2 / R ^ CycleLen := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hR2
  have hznorm : ‖z‖ = R := by
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    simpa using hz
  have hden_ne : UFRF.ResidueDefinition.breathingDenominator z ≠ 0 :=
    breathingDenominator_ne_zero_of_one_lt_norm (by linarith [hznorm])
  have hpow_nonneg : 0 ≤ R ^ CycleLen - 1 := by
    have hpow_one : (1 : ℝ) ≤ R ^ CycleLen := by
      have hpow_two : (2 : ℝ) ≤ R ^ CycleLen := by
        have htwo_le_two_pow : (2 : ℝ) ≤ 2 ^ CycleLen := by
          simpa using
            (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num)
              (Nat.succ_le_of_lt UFRF.ResidueDefinition.cycleLen_pos))
        have htwo_pow_le : (2 : ℝ) ^ CycleLen ≤ R ^ CycleLen := by
          exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hR2 CycleLen
        exact htwo_le_two_pow.trans htwo_pow_le
      linarith
    linarith
  have hden_lower : R ^ CycleLen - 1 ≤ ‖UFRF.ResidueDefinition.breathingDenominator z‖ := by
    calc
      R ^ CycleLen - 1 = ‖z ^ CycleLen‖ - ‖(1 : ℂ)‖ := by rw [norm_pow, hznorm, norm_one]
      _ ≤ ‖z ^ CycleLen - 1‖ := norm_sub_norm_le _ _
      _ = ‖UFRF.ResidueDefinition.breathingDenominator z‖ := by
        simp [UFRF.ResidueDefinition.breathingDenominator]
  have hpow_two : (2 : ℝ) ≤ R ^ CycleLen := by
    have htwo_le_two_pow : (2 : ℝ) ≤ 2 ^ CycleLen := by
      simpa using
        (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num)
          (Nat.succ_le_of_lt UFRF.ResidueDefinition.cycleLen_pos))
    have htwo_pow_le : (2 : ℝ) ^ CycleLen ≤ R ^ CycleLen := by
      exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hR2 CycleLen
    exact htwo_le_two_pow.trans htwo_pow_le
  have hhalf_lower : R ^ CycleLen / 2 ≤ ‖UFRF.ResidueDefinition.breathingDenominator z‖ := by
    have : R ^ CycleLen / 2 ≤ R ^ CycleLen - 1 := by
      linarith
    exact this.trans hden_lower
  have hhalf_pos : 0 < R ^ CycleLen / 2 := by positivity
  calc
    ‖UFRF.ResidueDefinition.breathingFunction z‖
        = 1 / ‖UFRF.ResidueDefinition.breathingDenominator z‖ := by
            simp [UFRF.ResidueDefinition.breathingFunction, norm_inv]
    _ ≤ 1 / (R ^ CycleLen / 2) := one_div_le_one_div_of_le hhalf_pos hhalf_lower
    _ = 2 / R ^ CycleLen := by
        field_simp [pow_ne_zero CycleLen hRpos.ne']

/--
Any origin-centered circle of radius strictly greater than `1` has zero
breathing-function integral.

This is the first honest enclosing-contour theorem in the pipeline for
`1 / (z^13 - 1)`.
-/
theorem circleIntegral_breathingFunction_eq_zero_of_one_lt
    {R : ℝ} (hR : 1 < R) :
    (∮ z in C((0 : ℂ), R), UFRF.ResidueDefinition.breathingFunction z) = 0 := by
  let I : ℂ := ∮ z in C((0 : ℂ), R), UFRF.ResidueDefinition.breathingFunction z
  let N : ℕ := Nat.ceil R + 1
  let g : ℕ → ℂ := fun n =>
    ∮ z in C((0 : ℂ), (((n + N : ℕ) : ℝ))), UFRF.ResidueDefinition.breathingFunction z
  let b : ℕ → ℝ := fun n => 4 * Real.pi / ((((n + N : ℕ) : ℝ)) ^ 12)
  have hRN : ∀ n : ℕ, R ≤ (((n + N : ℕ) : ℝ)) := by
    intro n
    have hnat : (Nat.ceil R : ℕ) ≤ n + N := by
      dsimp [N]
      omega
    exact (Nat.le_ceil R).trans (by exact_mod_cast hnat)
  have hconst : (fun _ : ℕ => I) =ᶠ[atTop] g := by
    filter_upwards [] with n
    dsimp [I, g]
    symm
    exact circleIntegral_breathingFunction_eq_of_one_lt_le hR (hRN n)
  have hbound : ∀ n : ℕ, ‖g n‖ ≤ b n := by
    intro n
    have hceil_one_nat : 1 ≤ Nat.ceil R := by
      exact_mod_cast (le_trans (le_of_lt hR) (Nat.le_ceil R))
    have hN_two_nat : 2 ≤ N := by
      dsimp [N]
      omega
    have hrad_two_nat : 2 ≤ n + N := by
      omega
    have hrad_two : (2 : ℝ) ≤ (((n + N : ℕ) : ℝ)) := by
      exact_mod_cast hrad_two_nat
    have hrad_nonneg : 0 ≤ (((n + N : ℕ) : ℝ)) := by positivity
    have hrad_pos : 0 < (((n + N : ℕ) : ℝ)) := by positivity
    calc
      ‖g n‖
          ≤ 2 * Real.pi * (((n + N : ℕ) : ℝ)) *
              (2 / (((n + N : ℕ) : ℝ)) ^ CycleLen) := by
                dsimp [g]
                refine circleIntegral.norm_integral_le_of_norm_le_const hrad_nonneg ?_
                intro z hz
                exact norm_breathingFunction_le_two_div_radius_pow_of_mem_sphere_of_two_le
                  hrad_two hz
      _ = b n := by
          change 2 * Real.pi * (((n + N : ℕ) : ℝ)) *
              (2 / (((n + N : ℕ) : ℝ)) ^ 13) = b n
          dsimp [b]
          field_simp [pow_ne_zero 12 hrad_pos.ne', pow_ne_zero 13 hrad_pos.ne']
          ring
  have hb_tendsto : Tendsto b atTop (𝓝 0) := by
    have hpow :
        Tendsto (fun n : ℕ => ((((n + N : ℕ) : ℝ)) ^ 12)) atTop atTop := by
      exact (tendsto_pow_atTop (n := 12) (by norm_num)).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat N))
    have hinv :
        Tendsto (fun n : ℕ => ((((n + N : ℕ) : ℝ)) ^ 12)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hpow
    simpa [b, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (tendsto_const_nhds.mul hinv :
        Tendsto (fun n : ℕ => (4 * Real.pi : ℝ) * ((((n + N : ℕ) : ℝ)) ^ 12)⁻¹)
          atTop (𝓝 ((4 * Real.pi : ℝ) * 0)))
  have hg_norm_tendsto_zero : Tendsto (fun n : ℕ => ‖g n‖) atTop (𝓝 0) := by
    exact squeeze_zero (fun n => norm_nonneg _) hbound hb_tendsto
  have hg_tendsto_zero : Tendsto g atTop (𝓝 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hg_norm_tendsto_zero
  have hconst_tendsto_zero : Tendsto (fun _ : ℕ => I) atTop (𝓝 0) :=
    Tendsto.congr' hconst.symm hg_tendsto_zero
  have hI : I = 0 := tendsto_nhds_unique tendsto_const_nhds hconst_tendsto_zero
  simpa [I] using hI

/--
For any separated inner-circle radius and any origin-centered outer radius
strictly larger than `1`, the full family of breathing-root circle integrals
equals that explicit outer-circle integral.

This is the first honest inner-to-outer contour comparison in the repo. The
proof stays precise: both sides are shown to be zero by specific theorems, not
by a general residue theorem or a multi-boundary decomposition claim.
-/
theorem sum_circleIntegral_breathingFunction_of_lt_half_infsep_allRoots_eq_outerCircle_of_one_lt
    {r R : ℝ} (hr : 0 < r)
    (hrlt : r < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (hR : 1 < R) :
    (∑ k : ZMod CycleLen,
      (∮ z in C(breathingRoot k, r), UFRF.ResidueDefinition.breathingFunction z)) =
      ∮ z in C((0 : ℂ), R), UFRF.ResidueDefinition.breathingFunction z := by
  rw [sum_circleIntegral_breathingFunction_of_lt_half_infsep_allRoots_eq_zero hr hrlt,
    circleIntegral_breathingFunction_eq_zero_of_one_lt hR]

/--
For distinct breathing roots, the canonical open balls of radius
`infsep(range breathingRoot) / 2` are disjoint.

This is the sharp open-ball separation statement extracted from the global
finite breathing-root configuration.
-/
theorem half_infsep_ball_disjoint_ball_breathingRoots
    {j k : ZMod CycleLen} (hjk : j ≠ k) :
    Disjoint
      (Metric.ball (breathingRoot j) (((Set.range breathingRoot : Set ℂ).infsep) / 2))
      (Metric.ball (breathingRoot k) (((Set.range breathingRoot : Set ℂ).infsep) / 2)) := by
  apply Metric.ball_disjoint_ball
  have hjmem : breathingRoot j ∈ (Set.range breathingRoot : Set ℂ) := ⟨j, rfl⟩
  have hkmem : breathingRoot k ∈ (Set.range breathingRoot : Set ℂ) := ⟨k, rfl⟩
  have hroot_ne : breathingRoot j ≠ breathingRoot k := by
    intro hroot
    exact hjk (UFRF.ComplexBreathing.breathingRoot_injective hroot)
  have hle :
      (Set.range breathingRoot : Set ℂ).infsep ≤
        dist (breathingRoot j) (breathingRoot k) :=
    Set.infsep_le_dist_of_mem hjmem hkmem hroot_ne
  linarith

/--
For distinct breathing roots, the closed balls of radius
`infsep(range breathingRoot) / 4` are disjoint.

This is the canonical closed-neighborhood separation package that avoids the
touching issue at radius `infsep / 2`.
-/
theorem quarter_infsep_closedBall_disjoint_closedBall_breathingRoots
    {j k : ZMod CycleLen} (hjk : j ≠ k) :
    Disjoint
      (Metric.closedBall (breathingRoot j) (((Set.range breathingRoot : Set ℂ).infsep) / 4))
      (Metric.closedBall (breathingRoot k) (((Set.range breathingRoot : Set ℂ).infsep) / 4)) := by
  apply Metric.closedBall_disjoint_closedBall
  have hlt := half_infsep_lt_dist_breathingRoots (j := j) (k := k) hjk
  linarith

/--
For distinct breathing roots, the quarter-`infsep` contour circles are
disjoint.

This provides the clean geometric input for any later finite multi-circle
decomposition theorem.
-/
theorem quarter_infsep_sphere_disjoint_sphere_breathingRoots
    {j k : ZMod CycleLen} (hjk : j ≠ k) :
    Disjoint
      (Metric.sphere (breathingRoot j) (((Set.range breathingRoot : Set ℂ).infsep) / 4))
      (Metric.sphere (breathingRoot k) (((Set.range breathingRoot : Set ℂ).infsep) / 4)) := by
  refine (quarter_infsep_closedBall_disjoint_closedBall_breathingRoots (j := j) (k := k) hjk).mono
    Metric.sphere_subset_closedBall Metric.sphere_subset_closedBall

/--
The local factor also stays nonzero on the smaller canonical closed ball of
radius `infsep(range breathingRoot) / 4`.

This is the nonvanishing form suited to the pairwise-disjoint closed-ball
package.
-/
theorem localFactorAt_nonzero_closedBall_quarter_infsep (k : ZMod CycleLen) :
    ∀ z : ℂ,
      z ∈ Metric.closedBall (breathingRoot k)
        (((Set.range breathingRoot : Set ℂ).infsep) / 4) →
      UFRF.ResidueDefinition.localFactorAt k z ≠ 0 := by
  intro z hz
  have hpos : 0 < (Set.range breathingRoot : Set ℂ).infsep := breathingRootSet_infsep_pos
  apply localFactorAt_nonzero_closedBall_half_infsep k z
  exact Metric.closedBall_subset_closedBall (by linarith) hz

/--
The breathing function integrates to `2πi` times the explicit residue
candidate on the quarter-`infsep` circle around any chosen breathing root.

This is the separated-circle version of the single-root contour theorem, ready
for later finite multi-circle assembly.
-/
theorem circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_quarter_infsep
    (k : ZMod CycleLen) :
    (∮ z in C(breathingRoot k, ((Set.range breathingRoot : Set ℂ).infsep / 4)),
      UFRF.ResidueDefinition.breathingFunction z) =
        (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt k := by
  have hpos : 0 < (Set.range breathingRoot : Set ℂ).infsep := breathingRootSet_infsep_pos
  have hR : 0 < ((Set.range breathingRoot : Set ℂ).infsep / 4) := by
    positivity
  exact circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate k hR
    (localFactorAt_nonzero_closedBall_quarter_infsep k)

/--
For any finite family of breathing roots, the sum of the quarter-`infsep`
circle integrals equals `2πi` times the sum of the explicit residue
candidates.

This is the finite-subset multi-circle formula at the separated quarter-`infsep`
scale. It remains specific to the breathing function and does not compare the
inner-circle sum to any enclosing contour.
-/
theorem sum_circleIntegral_breathingFunction_quarter_infsep_eq_two_pi_I_mul_sum_residueCandidate
    (S : Finset (ZMod CycleLen)) :
    Finset.sum S (fun k =>
      (∮ z in C(breathingRoot k, ((Set.range breathingRoot : Set ℂ).infsep / 4)),
        UFRF.ResidueDefinition.breathingFunction z)) =
      (2 * Real.pi * Complex.I) * Finset.sum S UFRF.ResidueDefinition.residueCandidateAt := by
  simp_rw [circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_quarter_infsep]
  rw [← Finset.mul_sum]

/--
The separated quarter-`infsep` circles around all breathing roots have total
circle integral zero.

This is a genuine finite multi-circle contour statement: it sums the already
proved single-root formulas over the full breathing configuration without
promoting that sum to a general residue theorem or to an enclosing-contour
statement that has not yet been formalized.
-/
theorem sum_circleIntegral_breathingFunction_quarter_infsep_allRoots_eq_zero :
    ∑ k : ZMod CycleLen,
      (∮ z in C(breathingRoot k, ((Set.range breathingRoot : Set ℂ).infsep / 4)),
        UFRF.ResidueDefinition.breathingFunction z) = 0 := by
  rw [sum_circleIntegral_breathingFunction_quarter_infsep_eq_two_pi_I_mul_sum_residueCandidate
    (S := Finset.univ)]
  rw [UFRF.ResidueDefinition.total_residue_candidate_zero, mul_zero]

/--
The finite set of breathing-root labels whose poles lie strictly inside the
circle centered at `c` with radius `R`.
-/
noncomputable def breathingRootsInBall (c : ℂ) (R : ℝ) : Finset (ZMod CycleLen) := by
  classical
  exact Finset.univ.filter (fun k : ZMod CycleLen => breathingRoot k ∈ Metric.ball c R)

@[simp] theorem mem_breathingRootsInBall {c : ℂ} {R : ℝ} {k : ZMod CycleLen} :
    k ∈ breathingRootsInBall c R ↔ breathingRoot k ∈ Metric.ball c R := by
  classical
  simp [breathingRootsInBall]

/--
If the pole `w` lies outside the closed disk bounded by `C(c, R)`, then the
standard circle kernel `(z - w)⁻¹` has zero circle integral on that contour.
-/
theorem circleIntegral_kernel_eq_zero_of_not_mem_closedBall
    {c w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hw : w ∉ Metric.closedBall c R) :
    (∮ z in C(c, R), (z - w)⁻¹) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    (c := c) (R := R) (s := ∅) hR countable_empty
  · refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    intro z hz
    exact sub_ne_zero.mpr (by
      intro hzw
      exact hw (hzw ▸ hz))
  · intro z hz
    have hzball : z ∈ Metric.ball c R := by simpa [diff_empty] using hz
    have hne : z ≠ w := by
      intro hzw
      exact hw (hzw ▸ Metric.ball_subset_closedBall hzball)
    exact (differentiableAt_id.sub_const w).inv (sub_ne_zero.mpr hne)

/--
On any positive-radius circle whose boundary contains no breathing root, the
circle integral of the specific breathing function equals `2πi` times the sum
of the explicit residue candidates for exactly the enclosed breathing roots.

This is a concrete subset-sensitive contour formula for `z ↦ 1 / (z^13 - 1)`.
It stays specific to the breathing setup and does not promote the result to a
general residue theorem or a generic residue API.
-/
theorem circleIntegral_breathingFunction_eq_two_pi_I_mul_sum_residueCandidate_of_no_boundary_roots
    (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hboundary : ∀ k : ZMod CycleLen, breathingRoot k ∉ Metric.sphere c R) :
    (∮ z in C(c, R), UFRF.ResidueDefinition.breathingFunction z) =
      (2 * Real.pi * Complex.I) *
        Finset.sum (breathingRootsInBall c R) UFRF.ResidueDefinition.residueCandidateAt := by
  classical
  let S : Finset (ZMod CycleLen) := breathingRootsInBall c R
  let f : ZMod CycleLen → ℂ → ℂ := fun k z =>
    UFRF.ResidueDefinition.residueCandidateAt k * (z - breathingRoot k)⁻¹
  have hEqOn :
      EqOn UFRF.ResidueDefinition.breathingFunction
        (fun z : ℂ => Finset.sum Finset.univ (fun k : ZMod CycleLen => f k z))
        (Metric.sphere c R) := by
    intro z hz
    simpa [f] using
      UFRF.ResidueDefinition.breathingFunction_eq_sum_residueCandidateAt_sub_inv (by
        intro hzero
        obtain ⟨k, hk⟩ := exists_breathingRoot_of_breathingDenominator_eq_zero hzero
        subst hk
        exact hboundary k hz)
  have hInt :
      (∮ z in C(c, R), UFRF.ResidueDefinition.breathingFunction z) =
        ∮ z in C(c, R), Finset.sum Finset.univ (fun k : ZMod CycleLen => f k z) := by
    refine circleIntegral.integral_congr hR.le ?_
    intro z hz
    exact hEqOn hz
  have hIntf :
      ∀ k ∈ Finset.univ, CircleIntegrable (f k) c R := by
    intro k hk
    have hcont : ContinuousOn (f k) (Metric.sphere c R) := by
      refine continuousOn_const.mul ?_
      refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
      intro z hz
      exact sub_ne_zero.mpr (by
        intro hzw
        exact hboundary k (hzw ▸ hz))
    exact hcont.circleIntegrable hR.le
  rw [hInt]
  rw [circleIntegral.integral_fun_sum (s := Finset.univ) hIntf]
  rw [← S.sum_add_sum_compl (fun k : ZMod CycleLen => ∮ z in C(c, R), f k z)]
  have hinside :
      Finset.sum S (fun k => ∮ z in C(c, R), f k z) =
        (2 * Real.pi * Complex.I) *
          Finset.sum S UFRF.ResidueDefinition.residueCandidateAt := by
    calc
      Finset.sum S (fun k => ∮ z in C(c, R), f k z)
          = Finset.sum S
              (fun k =>
                UFRF.ResidueDefinition.residueCandidateAt k * (2 * Real.pi * Complex.I)) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                have hkball : breathingRoot k ∈ Metric.ball c R := by simpa [S] using hk
                simp [f, circleIntegral.integral_const_mul,
                  circleIntegral.integral_sub_inv_of_mem_ball hkball]
      _ = Finset.sum S
            (fun k => (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt k) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              ring
      _ = (2 * Real.pi * Complex.I) *
            Finset.sum S UFRF.ResidueDefinition.residueCandidateAt := by
              rw [Finset.mul_sum]
  have houtside_zero :
      Finset.sum Sᶜ (fun k => ∮ z in C(c, R), f k z) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hknotS : k ∉ S := Finset.mem_compl.mp hk
    have hknotBall : breathingRoot k ∉ Metric.ball c R := by
      intro hkball
      have hkS : k ∈ S := by
        simpa [S] using hkball
      exact hknotS hkS
    have hknotClosed : breathingRoot k ∉ Metric.closedBall c R := by
      intro hkclosed
      have hle : dist (breathingRoot k) c ≤ R := by
        simpa [Metric.mem_closedBall, dist_comm] using hkclosed
      have hnotlt : ¬ dist (breathingRoot k) c < R := by
        intro hlt
        exact hknotBall (by simpa [Metric.mem_ball, dist_comm] using hlt)
      have heq : dist (breathingRoot k) c = R := le_antisymm hle (le_of_not_gt hnotlt)
      have hkSphere : breathingRoot k ∈ Metric.sphere c R := by
        rw [Metric.mem_sphere]
        simpa [dist_comm] using heq
      exact hboundary k hkSphere
    simp [f, circleIntegral.integral_const_mul,
      circleIntegral_kernel_eq_zero_of_not_mem_closedBall hR.le hknotClosed]
  rw [houtside_zero, add_zero, hinside]

/--
An enclosing circle that avoids the breathing roots on its boundary has the
same breathing-function integral as the sum of the separated local circles
around exactly the enclosed breathing roots.

The common local radius can be any `r` with
`0 < r < infsep(range breathingRoot) / 2`, so the inner circles stay in the
already proved separated regime.
-/
theorem circleIntegral_breathingFunction_eq_sum_localCircleIntegrals_of_lt_half_infsep_of_no_boundary_roots
    (c : ℂ) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrlt : r < ((Set.range breathingRoot : Set ℂ).infsep / 2))
    (hboundary : ∀ k : ZMod CycleLen, breathingRoot k ∉ Metric.sphere c R) :
    (∮ z in C(c, R), UFRF.ResidueDefinition.breathingFunction z) =
      Finset.sum (breathingRootsInBall c R) (fun k =>
        (∮ z in C(breathingRoot k, r), UFRF.ResidueDefinition.breathingFunction z)) := by
  rw [sum_circleIntegral_breathingFunction_of_lt_half_infsep_eq_two_pi_I_mul_sum_residueCandidate
    (S := breathingRootsInBall c R) hr hrlt]
  exact circleIntegral_breathingFunction_eq_two_pi_I_mul_sum_residueCandidate_of_no_boundary_roots
    c hR hboundary

/--
The coordinate form of the positively oriented boundary integral around the
closed rectangle with horizontal endpoints `x0`, `x1` and vertical endpoints
`y0`, `y1`.
-/
def boundaryRectIntegral (f : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) : ℂ :=
  (∫ x : ℝ in x0..x1, f (x + y0 * Complex.I)) -
    (∫ x : ℝ in x0..x1, f (x + y1 * Complex.I)) +
    Complex.I • (∫ y : ℝ in y0..y1, f (x1 + y * Complex.I)) -
    Complex.I • (∫ y : ℝ in y0..y1, f (x0 + y * Complex.I))

/-- The closed rectangle with horizontal endpoints `x0`, `x1` and vertical
endpoints `y0`, `y1`. -/
def closedRect (x0 x1 y0 y1 : ℝ) : Set ℂ :=
  uIcc x0 x1 ×ℂ uIcc y0 y1

/--
The finite set of breathing-root labels whose poles lie strictly inside the
given rectangle.
-/
noncomputable def breathingRootsInInteriorRect (x0 x1 y0 y1 : ℝ) : Finset (ZMod CycleLen) := by
  classical
  exact Finset.univ.filter (fun k : ZMod CycleLen =>
    breathingRoot k ∈ interior (closedRect x0 x1 y0 y1))

@[simp] theorem mem_breathingRootsInInteriorRect
    {x0 x1 y0 y1 : ℝ} {k : ZMod CycleLen} :
    k ∈ breathingRootsInInteriorRect x0 x1 y0 y1 ↔
      breathingRoot k ∈ interior (closedRect x0 x1 y0 y1) := by
  classical
  simp [breathingRootsInInteriorRect]

private lemma sub_mul_I_ne_zero {r x : ℝ} (hr : 0 < r) :
    ((x : ℂ) - r * Complex.I) ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  have : r = 0 := by simpa using him
  exact hr.ne' this

private lemma add_mul_I_ne_zero {r x : ℝ} (hr : 0 < r) :
    ((x : ℂ) + r * Complex.I) ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  have : r = 0 := by simpa using him
  exact hr.ne' this

private lemma re_add_im_mul_I_ne_zero {r y : ℝ} (hr : 0 < r) :
    ((r : ℂ) + y * Complex.I) ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  have : r = 0 := by simpa using hre
  exact hr.ne' this

private lemma neg_re_add_im_mul_I_ne_zero {r y : ℝ} (hr : 0 < r) :
    (((-r : ℂ) + y * Complex.I) : ℂ) ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  have : r = 0 := by simpa using hre
  exact hr.ne' this

private lemma intervalIntegrable_sub_mul_I_inv {r a b : ℝ} (hr : 0 < r) :
    IntervalIntegrable (fun x : ℝ => ((x : ℂ) - r * Complex.I)⁻¹)
      MeasureTheory.volume a b := by
  have hcont : Continuous fun x : ℝ => ((x : ℂ) - r * Complex.I : ℂ) := by
    fun_prop
  exact ContinuousOn.intervalIntegrable
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hcont.inv₀ (fun x => sub_mul_I_ne_zero (r := r) (x := x) hr)).continuousOn

private lemma intervalIntegrable_add_mul_I_inv {r a b : ℝ} (hr : 0 < r) :
    IntervalIntegrable (fun x : ℝ => ((x : ℂ) + r * Complex.I)⁻¹)
      MeasureTheory.volume a b := by
  have hcont : Continuous fun x : ℝ => ((x : ℂ) + r * Complex.I : ℂ) := by
    fun_prop
  exact ContinuousOn.intervalIntegrable
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hcont.inv₀ (fun x => add_mul_I_ne_zero (r := r) (x := x) hr)).continuousOn

private lemma intervalIntegrable_re_add_im_mul_I_inv {r a b : ℝ} (hr : 0 < r) :
    IntervalIntegrable (fun y : ℝ => ((r : ℂ) + y * Complex.I)⁻¹)
      MeasureTheory.volume a b := by
  have hcont : Continuous fun y : ℝ => ((r : ℂ) + y * Complex.I : ℂ) := by
    fun_prop
  exact ContinuousOn.intervalIntegrable
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hcont.inv₀ (fun y => re_add_im_mul_I_ne_zero (r := r) (y := y) hr)).continuousOn

private lemma intervalIntegrable_neg_re_add_im_mul_I_inv {r a b : ℝ} (hr : 0 < r) :
    IntervalIntegrable (fun y : ℝ => (((-r : ℂ) + y * Complex.I) : ℂ)⁻¹)
      MeasureTheory.volume a b := by
  have hcont : Continuous fun y : ℝ => (((-r : ℂ) + y * Complex.I) : ℂ) := by
    fun_prop
  exact ContinuousOn.intervalIntegrable
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hcont.inv₀ (fun y => neg_re_add_im_mul_I_ne_zero (r := r) (y := y) hr)).continuousOn

private lemma sub_inv_bottom_top_eq {r x : ℝ} (hr : 0 < r) :
    (((x : ℂ) - r * Complex.I)⁻¹ - ((x : ℂ) + r * Complex.I)⁻¹) =
      (2 * r * Complex.I : ℂ) * (r ^ 2 + x ^ 2)⁻¹ := by
  have hx1 : ((x : ℂ) - r * Complex.I) ≠ 0 := sub_mul_I_ne_zero (r := r) (x := x) hr
  have hx2 : ((x : ℂ) + r * Complex.I) ≠ 0 := add_mul_I_ne_zero (r := r) (x := x) hr
  have hnum : (((x : ℂ) + r * Complex.I) - ((x : ℂ) - r * Complex.I)) =
      (2 * r * Complex.I : ℂ) := by
    ring
  have hden :
      (((x : ℂ) - r * Complex.I) * ((x : ℂ) + r * Complex.I)) =
        ((r ^ 2 + x ^ 2 : ℝ) : ℂ) := by
    ring_nf
    simp [pow_two]
    ring
  calc
    (((x : ℂ) - r * Complex.I)⁻¹ - ((x : ℂ) + r * Complex.I)⁻¹)
        = ((((x : ℂ) + r * Complex.I) - ((x : ℂ) - r * Complex.I)) /
            (((x : ℂ) - r * Complex.I) * ((x : ℂ) + r * Complex.I))) := by
              simpa using inv_sub_inv hx1 hx2
    _ = (2 * r * Complex.I : ℂ) / ((r ^ 2 + x ^ 2 : ℝ) : ℂ) := by rw [hnum, hden]
    _ = (2 * r * Complex.I : ℂ) * (r ^ 2 + x ^ 2)⁻¹ := by
      simp [div_eq_mul_inv]

private lemma I_mul_sub_inv_right_left_eq {r y : ℝ} (hr : 0 < r) :
    Complex.I * ((((r : ℂ) + y * Complex.I)⁻¹) - (((-r : ℂ) + y * Complex.I)⁻¹)) =
      (2 * r * Complex.I : ℂ) * (r ^ 2 + y ^ 2)⁻¹ := by
  have ha : ((r : ℂ) + y * Complex.I) ≠ 0 := re_add_im_mul_I_ne_zero (r := r) (y := y) hr
  have hb : (((-r : ℂ) + y * Complex.I) : ℂ) ≠ 0 :=
    neg_re_add_im_mul_I_ne_zero (r := r) (y := y) hr
  have hsq : (r ^ 2 + y ^ 2 : ℝ) ≠ 0 := by
    nlinarith [sq_nonneg r, sq_nonneg y, hr]
  have hnum : (((-r : ℂ) + y * Complex.I) - ((r : ℂ) + y * Complex.I)) = (-2 * r : ℂ) := by
    ring
  have hden :
      (((r : ℂ) + y * Complex.I) * (((-r : ℂ) + y * Complex.I))) =
        (-((r ^ 2 + y ^ 2 : ℝ) : ℂ)) := by
    ring_nf
    simp [pow_two]
    ring
  have hsub :
      (((r : ℂ) + y * Complex.I)⁻¹) - (((-r : ℂ) + y * Complex.I)⁻¹) =
        ((((-r : ℂ) + y * Complex.I) - ((r : ℂ) + y * Complex.I)) /
          (((r : ℂ) + y * Complex.I) * (((-r : ℂ) + y * Complex.I)))) := by
    exact inv_sub_inv ha hb
  have hsubI :
      Complex.I * ((((r : ℂ) + y * Complex.I)⁻¹) - (((-r : ℂ) + y * Complex.I)⁻¹)) =
        Complex.I *
          (((((-r : ℂ) + y * Complex.I) - ((r : ℂ) + y * Complex.I)) /
            (((r : ℂ) + y * Complex.I) * (((-r : ℂ) + y * Complex.I))))) := by
    rw [hsub]
  calc
    Complex.I * ((((r : ℂ) + y * Complex.I)⁻¹) - (((-r : ℂ) + y * Complex.I)⁻¹))
        = Complex.I *
            (((((-r : ℂ) + y * Complex.I) - ((r : ℂ) + y * Complex.I)) /
              (((r : ℂ) + y * Complex.I) * (((-r : ℂ) + y * Complex.I))))) := by
                exact hsubI
    _ = Complex.I * (((-2 * r : ℂ)) / (-((r ^ 2 + y ^ 2 : ℝ) : ℂ))) := by rw [hnum, hden]
    _ = Complex.I * (((2 * r : ℂ)) / (((r ^ 2 + y ^ 2 : ℝ) : ℂ))) := by
      have hsqC : ((r ^ 2 + y ^ 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hsq
      field_simp [hsqC]
    _ = (2 * r * Complex.I : ℂ) * (r ^ 2 + y ^ 2)⁻¹ := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm]

/--
If the standard kernel `z ↦ z⁻¹` has no pole inside a closed rectangle, then
its boundary integral around that rectangle is zero.
-/
theorem boundaryRectIntegral_sub_inv_eq_zero_of_not_mem_closedRect
    {u : ℂ} {x0 x1 y0 y1 : ℝ}
    (hu : u ∉ closedRect x0 x1 y0 y1) :
    boundaryRectIntegral (fun z : ℂ => (z - u)⁻¹) x0 x1 y0 y1 = 0 := by
  have hcont :
      ContinuousOn (fun z : ℂ => (z - u)⁻¹) (closedRect x0 x1 y0 y1) := by
    refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    intro z hz
    exact sub_ne_zero.mpr (by
      intro hzu
      exact hu (hzu ▸ hz))
  have hdiff :
      DifferentiableOn ℂ (fun z : ℂ => (z - u)⁻¹)
        (Ioo (min x0 x1) (max x0 x1) ×ℂ Ioo (min y0 y1) (max y0 y1)) := by
    intro z hz
    have hzInterior : z ∈ interior (closedRect x0 x1 y0 y1) := by
      simpa [closedRect, interior_reProdIm, uIcc, interior_Icc] using hz
    have hzClosed : z ∈ closedRect x0 x1 y0 y1 := interior_subset hzInterior
    have hzu : z - u ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      intro hEq
      exact hu (hEq ▸ hzClosed)
    exact ((differentiableAt_id.sub_const u).inv hzu).differentiableWithinAt
  have hcont' :
      ContinuousOn (fun z : ℂ => (z - u)⁻¹)
        (uIcc (x0 + y0 * Complex.I).re (x1 + y1 * Complex.I).re ×ℂ
          uIcc (x0 + y0 * Complex.I).im (x1 + y1 * Complex.I).im) := by
    simpa [closedRect] using hcont
  have hdiff' :
      DifferentiableOn ℂ (fun z : ℂ => (z - u)⁻¹)
        (Ioo (min (x0 + y0 * Complex.I).re (x1 + y1 * Complex.I).re)
            (max (x0 + y0 * Complex.I).re (x1 + y1 * Complex.I).re) ×ℂ
          Ioo (min (x0 + y0 * Complex.I).im (x1 + y1 * Complex.I).im)
            (max (x0 + y0 * Complex.I).im (x1 + y1 * Complex.I).im)) := by
    simpa using hdiff
  simpa [boundaryRectIntegral] using
    Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      (fun z : ℂ => (z - u)⁻¹) (x0 + y0 * Complex.I) (x1 + y1 * Complex.I) hcont' hdiff'

/--
The standard kernel `z ↦ z⁻¹` has rectangle boundary integral `2πi` around the
origin-centered square `[-r, r] × [-r, r]` for every `r > 0`.
-/
theorem boundaryRectIntegral_inv_centeredSquare {r : ℝ} (hr : 0 < r) :
    boundaryRectIntegral (fun z : ℂ => z⁻¹) (-r) r (-r) r = 2 * Real.pi * Complex.I := by
  have hbottom :
      (∫ x : ℝ in -r..r, ((x : ℂ) - r * Complex.I)⁻¹) -
        (∫ x : ℝ in -r..r, ((x : ℂ) + r * Complex.I)⁻¹) =
          ∫ x : ℝ in -r..r, (2 * r * Complex.I : ℂ) * (r ^ 2 + x ^ 2)⁻¹ := by
    rw [← intervalIntegral.integral_sub
      (intervalIntegrable_sub_mul_I_inv (a := -r) (b := r) hr)
      (intervalIntegrable_add_mul_I_inv (a := -r) (b := r) hr)]
    refine intervalIntegral.integral_congr ?_
    intro x hx
    simpa using sub_inv_bottom_top_eq (r := r) (x := x) hr
  have hvertical :
      Complex.I * (∫ y : ℝ in -r..r, ((r : ℂ) + y * Complex.I)⁻¹) -
        Complex.I * (∫ y : ℝ in -r..r, (((-r : ℂ) + y * Complex.I) : ℂ)⁻¹) =
          ∫ y : ℝ in -r..r, (2 * r * Complex.I : ℂ) * (r ^ 2 + y ^ 2)⁻¹ := by
    rw [← mul_sub]
    rw [← intervalIntegral.integral_sub
      (intervalIntegrable_re_add_im_mul_I_inv (a := -r) (b := r) hr)
      (intervalIntegrable_neg_re_add_im_mul_I_inv (a := -r) (b := r) hr)]
    let f : ℝ → ℂ := fun y =>
      (((r : ℂ) + y * Complex.I)⁻¹ - (((-r : ℂ) + y * Complex.I)⁻¹))
    have hconstmul :
        Complex.I * (∫ y : ℝ in -r..r, f y) =
          ∫ y : ℝ in -r..r, Complex.I * f y := by
      exact
        (intervalIntegral.integral_const_mul (μ := MeasureTheory.volume) (a := -r) (b := r)
          Complex.I f).symm
    rw [hconstmul]
    refine intervalIntegral.integral_congr ?_
    intro y hy
    simpa [f, mul_assoc] using I_mul_sub_inv_right_left_eq (r := r) (y := y) hr
  have hpiece :
      (∫ x : ℝ in -r..r, (2 * r * Complex.I : ℂ) * (r ^ 2 + x ^ 2)⁻¹) =
        Real.pi * Complex.I := by
    change (∫ x : ℝ in -r..r, (2 * r * Complex.I : ℂ) * ((((r ^ 2 + x ^ 2)⁻¹ : ℝ) : ℂ))) =
      Real.pi * Complex.I
    let g : ℝ → ℂ := fun x => ((((r ^ 2 + x ^ 2)⁻¹ : ℝ) : ℂ))
    have hconstmul :
        (∫ x : ℝ in -r..r, (2 * r * Complex.I : ℂ) * g x) =
          (2 * r * Complex.I : ℂ) * (∫ x : ℝ in -r..r, g x) := by
      exact
        (intervalIntegral.integral_const_mul (μ := MeasureTheory.volume) (a := -r) (b := r)
          (2 * r * Complex.I : ℂ) g)
    rw [hconstmul]
    have hofreal :
        (∫ x : ℝ in -r..r, g x) = ↑(∫ x : ℝ in -r..r, (r ^ 2 + x ^ 2)⁻¹) := by
      dsimp [g]
      exact
        (intervalIntegral.integral_ofReal (μ := MeasureTheory.volume) (a := -r) (b := r)
          (f := fun x : ℝ => (r ^ 2 + x ^ 2)⁻¹))
    rw [hofreal, integral_inv_sq_add_sq (a := -r) (b := r) hr.ne']
    have harctan : Real.arctan (r / r) - Real.arctan (-r / r) = Real.pi / 2 := by
      rw [div_self hr.ne', neg_div, div_self hr.ne', Real.arctan_one, Real.arctan_neg,
        Real.arctan_one]
      ring
    rw [harctan]
    have hreal : (2 * r : ℝ) * (r⁻¹ * (Real.pi / 2)) = Real.pi := by
      field_simp [hr.ne']
    calc
      (2 * r * Complex.I : ℂ) * ((r⁻¹ * (Real.pi / 2) : ℝ) : ℂ)
          = (((2 * r : ℝ) * (r⁻¹ * (Real.pi / 2)) : ℝ) : ℂ) * Complex.I := by
              simp [mul_left_comm, mul_comm]
      _ = Real.pi * Complex.I := by rw [hreal]
  have hbottom' :
      ((∫ x : ℝ in -r..r, (fun z : ℂ => z⁻¹) (x + (-r) * Complex.I)) -
        (∫ x : ℝ in -r..r, (fun z : ℂ => z⁻¹) (x + r * Complex.I))) =
          ∫ x : ℝ in -r..r, (2 * r * Complex.I : ℂ) * (r ^ 2 + x ^ 2)⁻¹ := by
    simpa using hbottom
  have hvertical' :
      (Complex.I • (∫ y : ℝ in -r..r, (fun z : ℂ => z⁻¹) (r + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in -r..r, (fun z : ℂ => z⁻¹) (-r + y * Complex.I))) =
          ∫ y : ℝ in -r..r, (2 * r * Complex.I : ℂ) * (r ^ 2 + y ^ 2)⁻¹ := by
    simpa [smul_eq_mul] using hvertical
  calc
    boundaryRectIntegral (fun z : ℂ => z⁻¹) (-r) r (-r) r
        = ((∫ x : ℝ in -r..r, (fun z : ℂ => z⁻¹) (x + (-r) * Complex.I)) -
            (∫ x : ℝ in -r..r, (fun z : ℂ => z⁻¹) (x + r * Complex.I))) +
          (Complex.I • (∫ y : ℝ in -r..r, (fun z : ℂ => z⁻¹) (r + y * Complex.I)) -
            Complex.I • (∫ y : ℝ in -r..r, (fun z : ℂ => z⁻¹) (-r + y * Complex.I))) := by
              simp [boundaryRectIntegral, sub_eq_add_neg, add_assoc]
    _ = (∫ x : ℝ in -r..r, (2 * r * Complex.I : ℂ) * (r ^ 2 + x ^ 2)⁻¹) +
          (∫ y : ℝ in -r..r, (2 * r * Complex.I : ℂ) * (r ^ 2 + y ^ 2)⁻¹) := by
            rw [hbottom', hvertical']
    _ = Real.pi * Complex.I + Real.pi * Complex.I := by
          rw [hpiece]
    _ = 2 * Real.pi * Complex.I := by ring

/--
The translated kernel `z ↦ (z - a)⁻¹` has rectangle boundary integral `2πi`
around the square centered at `a` with side length `2r`, for every `r > 0`.
-/
theorem boundaryRectIntegral_sub_inv_arbitraryCenterSquare {a : ℂ} {r : ℝ}
    (hr : 0 < r) :
    boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹)
      (a.re - r) (a.re + r) (a.im - r) (a.im + r) = 2 * Real.pi * Complex.I := by
  have hbottom :
      (∫ x : ℝ in a.re - r..a.re + r,
          (x + (a.im - r) * Complex.I - a)⁻¹) =
        ∫ x : ℝ in -r..r, ((x : ℂ) - r * Complex.I)⁻¹ := by
    calc
      (∫ x : ℝ in a.re - r..a.re + r, (x + (a.im - r) * Complex.I - a)⁻¹)
          =
            ∫ x : ℝ in a.re - r..a.re + r, (((x - a.re : ℝ) : ℂ) - r * Complex.I)⁻¹ := by
              refine intervalIntegral.integral_congr ?_
              intro x hx
              have harg :
                  x + (a.im - r) * Complex.I - a =
                    (((x - a.re : ℝ) : ℂ) - r * Complex.I) := by
                apply Complex.ext <;> simp [sub_eq_add_neg, add_assoc, add_comm]
              simp [harg]
      _ = ∫ x : ℝ in -r..r, ((x : ℂ) - r * Complex.I)⁻¹ := by
          simpa using
            (intervalIntegral.integral_comp_sub_right
              (f := fun x : ℝ => ((x : ℂ) - r * Complex.I)⁻¹)
              (a := a.re - r) (b := a.re + r) (d := a.re))
  have htop :
      (∫ x : ℝ in a.re - r..a.re + r,
          (x + (a.im + r) * Complex.I - a)⁻¹) =
        ∫ x : ℝ in -r..r, ((x : ℂ) + r * Complex.I)⁻¹ := by
    calc
      (∫ x : ℝ in a.re - r..a.re + r, (x + (a.im + r) * Complex.I - a)⁻¹)
          =
            ∫ x : ℝ in a.re - r..a.re + r, (((x - a.re : ℝ) : ℂ) + r * Complex.I)⁻¹ := by
              refine intervalIntegral.integral_congr ?_
              intro x hx
              have harg :
                  x + (a.im + r) * Complex.I - a =
                    (((x - a.re : ℝ) : ℂ) + r * Complex.I) := by
                apply Complex.ext <;> simp [sub_eq_add_neg, add_left_comm, add_comm]
              simp [harg]
      _ = ∫ x : ℝ in -r..r, ((x : ℂ) + r * Complex.I)⁻¹ := by
          simpa using
            (intervalIntegral.integral_comp_sub_right
              (f := fun x : ℝ => ((x : ℂ) + r * Complex.I)⁻¹)
              (a := a.re - r) (b := a.re + r) (d := a.re))
  have hright :
      (∫ y : ℝ in a.im - r..a.im + r,
          (a.re + r + y * Complex.I - a)⁻¹) =
        ∫ y : ℝ in -r..r, ((r : ℂ) + y * Complex.I)⁻¹ := by
    calc
      (∫ y : ℝ in a.im - r..a.im + r, (a.re + r + y * Complex.I - a)⁻¹)
          =
            ∫ y : ℝ in a.im - r..a.im + r, ((r : ℂ) + (y - a.im) * Complex.I)⁻¹ := by
              refine intervalIntegral.integral_congr ?_
              intro y hy
              have harg :
                  a.re + r + y * Complex.I - a =
                    ((r : ℂ) + (y - a.im) * Complex.I) := by
                apply Complex.ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
              simp [harg]
      _ = ∫ y : ℝ in -r..r, ((r : ℂ) + y * Complex.I)⁻¹ := by
          simpa using
            (intervalIntegral.integral_comp_sub_right
              (f := fun y : ℝ => ((r : ℂ) + y * Complex.I)⁻¹)
              (a := a.im - r) (b := a.im + r) (d := a.im))
  have hleft :
      (∫ y : ℝ in a.im - r..a.im + r,
          (a.re - r + y * Complex.I - a)⁻¹) =
        ∫ y : ℝ in -r..r, (((-r : ℂ) + y * Complex.I) : ℂ)⁻¹ := by
    calc
      (∫ y : ℝ in a.im - r..a.im + r, (a.re - r + y * Complex.I - a)⁻¹)
          =
            ∫ y : ℝ in a.im - r..a.im + r, (((-r : ℂ) + (y - a.im) * Complex.I) : ℂ)⁻¹ := by
              refine intervalIntegral.integral_congr ?_
              intro y hy
              have harg :
                  a.re - r + y * Complex.I - a =
                    (((-r : ℂ) + (y - a.im) * Complex.I) : ℂ) := by
                apply Complex.ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
              simp [harg]
      _ = ∫ y : ℝ in -r..r, (((-r : ℂ) + y * Complex.I) : ℂ)⁻¹ := by
          simpa using
            (intervalIntegral.integral_comp_sub_right
              (f := fun y : ℝ => (((-r : ℂ) + y * Complex.I) : ℂ)⁻¹)
              (a := a.im - r) (b := a.im + r) (d := a.im))
  calc
    boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹)
        (a.re - r) (a.re + r) (a.im - r) (a.im + r)
        =
          ((∫ x : ℝ in -r..r, ((x : ℂ) - r * Complex.I)⁻¹) -
              (∫ x : ℝ in -r..r, ((x : ℂ) + r * Complex.I)⁻¹) +
            Complex.I • (∫ y : ℝ in -r..r, ((r : ℂ) + y * Complex.I)⁻¹) -
            Complex.I • (∫ y : ℝ in -r..r, (((-r : ℂ) + y * Complex.I) : ℂ)⁻¹)) := by
              simp [boundaryRectIntegral, hbottom, htop, hright, hleft]
    _ = boundaryRectIntegral (fun z : ℂ => z⁻¹) (-r) r (-r) r := by
          simp [boundaryRectIntegral, sub_eq_add_neg]
    _ = 2 * Real.pi * Complex.I := boundaryRectIntegral_inv_centeredSquare hr

private lemma intervalIntegrable_sub_inv_horizontal_off_im
    {a : ℂ} {y x0 x1 : ℝ} (hy : y ≠ a.im) :
    IntervalIntegrable (fun x : ℝ => (x + y * Complex.I - a)⁻¹)
      MeasureTheory.volume x0 x1 := by
  have hcont :
      ContinuousOn (fun x : ℝ => (x + y * Complex.I - a)⁻¹) (uIcc x0 x1) := by
    refine (by
      fun_prop : ContinuousOn (fun x : ℝ => (x + y * Complex.I - a : ℂ)) (uIcc x0 x1)).inv₀ ?_
    intro x hx hzero
    have hz : x + y * Complex.I = a := sub_eq_zero.mp hzero
    exact hy (by simpa using congrArg Complex.im hz)
  exact ContinuousOn.intervalIntegrable
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hcont

private lemma intervalIntegrable_sub_inv_vertical_off_re
    {a : ℂ} {x y0 y1 : ℝ} (hx : x ≠ a.re) :
    IntervalIntegrable (fun y : ℝ => (x + y * Complex.I - a)⁻¹)
      MeasureTheory.volume y0 y1 := by
  have hcont :
      ContinuousOn (fun y : ℝ => (x + y * Complex.I - a)⁻¹) (uIcc y0 y1) := by
    refine (by
      fun_prop : ContinuousOn (fun y : ℝ => (x + y * Complex.I - a : ℂ)) (uIcc y0 y1)).inv₀ ?_
    intro y hy hzero
    have hz : x + y * Complex.I = a := sub_eq_zero.mp hzero
    exact hx (by simpa using congrArg Complex.re hz)
  exact ContinuousOn.intervalIntegrable
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hcont

private lemma intervalIntegrable_sub_inv_horizontal_of_ne
    {a : ℂ} {y x0 x1 : ℝ}
    (h : ∀ x ∈ uIcc x0 x1, x + y * Complex.I ≠ a) :
    IntervalIntegrable (fun x : ℝ => (x + y * Complex.I - a)⁻¹)
      MeasureTheory.volume x0 x1 := by
  have hcont :
      ContinuousOn (fun x : ℝ => (x + y * Complex.I - a)⁻¹) (uIcc x0 x1) := by
    refine (by
      fun_prop : ContinuousOn (fun x : ℝ => (x + y * Complex.I - a : ℂ)) (uIcc x0 x1)).inv₀ ?_
    intro x hx hzero
    exact h x hx (sub_eq_zero.mp hzero)
  exact ContinuousOn.intervalIntegrable
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hcont

private lemma intervalIntegrable_sub_inv_vertical_of_ne
    {a : ℂ} {x y0 y1 : ℝ}
    (h : ∀ y ∈ uIcc y0 y1, x + y * Complex.I ≠ a) :
    IntervalIntegrable (fun y : ℝ => (x + y * Complex.I - a)⁻¹)
      MeasureTheory.volume y0 y1 := by
  have hcont :
      ContinuousOn (fun y : ℝ => (x + y * Complex.I - a)⁻¹) (uIcc y0 y1) := by
    refine (by
      fun_prop : ContinuousOn (fun y : ℝ => (x + y * Complex.I - a : ℂ)) (uIcc y0 y1)).inv₀ ?_
    intro y hy hzero
    exact h y hy (sub_eq_zero.mp hzero)
  exact ContinuousOn.intervalIntegrable
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hcont

private theorem boundaryRectIntegral_split_vertical
    {f : ℂ → ℂ} {x0 x1 x2 y0 y1 : ℝ}
    (hbot01 : IntervalIntegrable (fun x : ℝ => f (x + y0 * Complex.I))
      MeasureTheory.volume x0 x1)
    (hbot12 : IntervalIntegrable (fun x : ℝ => f (x + y0 * Complex.I))
      MeasureTheory.volume x1 x2)
    (htop01 : IntervalIntegrable (fun x : ℝ => f (x + y1 * Complex.I))
      MeasureTheory.volume x0 x1)
    (htop12 : IntervalIntegrable (fun x : ℝ => f (x + y1 * Complex.I))
      MeasureTheory.volume x1 x2) :
    boundaryRectIntegral f x0 x2 y0 y1 =
      boundaryRectIntegral f x0 x1 y0 y1 + boundaryRectIntegral f x1 x2 y0 y1 := by
  rw [boundaryRectIntegral, boundaryRectIntegral, boundaryRectIntegral]
  have hbot := intervalIntegral.integral_add_adjacent_intervals hbot01 hbot12
  have htop := intervalIntegral.integral_add_adjacent_intervals htop01 htop12
  rw [← hbot, ← htop]
  ring

private theorem boundaryRectIntegral_split_horizontal
    {f : ℂ → ℂ} {x0 x1 y0 y1 y2 : ℝ}
    (hright01 : IntervalIntegrable (fun y : ℝ => f (x1 + y * Complex.I))
      MeasureTheory.volume y0 y1)
    (hright12 : IntervalIntegrable (fun y : ℝ => f (x1 + y * Complex.I))
      MeasureTheory.volume y1 y2)
    (hleft01 : IntervalIntegrable (fun y : ℝ => f (x0 + y * Complex.I))
      MeasureTheory.volume y0 y1)
    (hleft12 : IntervalIntegrable (fun y : ℝ => f (x0 + y * Complex.I))
      MeasureTheory.volume y1 y2) :
    boundaryRectIntegral f x0 x1 y0 y2 =
      boundaryRectIntegral f x0 x1 y0 y1 + boundaryRectIntegral f x0 x1 y1 y2 := by
  rw [boundaryRectIntegral, boundaryRectIntegral, boundaryRectIntegral]
  have hright := intervalIntegral.integral_add_adjacent_intervals hright01 hright12
  have hleft := intervalIntegral.integral_add_adjacent_intervals hleft01 hleft12
  rw [← hright, ← hleft]
  simp [sub_eq_add_neg, smul_eq_mul, add_assoc, add_left_comm, add_comm, mul_add, mul_comm]

/--
If the pole `a` lies in the interior of a positively oriented rectangle, then
the kernel `z ↦ (z - a)⁻¹` has boundary rectangle integral `2πi`.

This is the arbitrary-rectangle nonzero kernel theorem obtained by reducing the
outer rectangle to an inner centered square and four surrounding pole-free
rectangles.
-/
theorem boundaryRectIntegral_sub_inv_eq_two_pi_I_of_mem_interior_closedRect
    {a : ℂ} {x0 x1 y0 y1 : ℝ}
    (hx : x0 < x1) (hy : y0 < y1)
    (ha : a ∈ interior (closedRect x0 x1 y0 y1)) :
    boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) x0 x1 y0 y1 =
      2 * Real.pi * Complex.I := by
  have hainter :
      a.re ∈ Set.Ioo x0 x1 ∧ a.im ∈ Set.Ioo y0 y1 := by
    simpa [closedRect, interior_reProdIm, Set.uIcc_of_le hx.le, Set.uIcc_of_le hy.le, interior_Icc]
      using ha
  have hx0a : x0 < a.re := hainter.1.1
  have hax1 : a.re < x1 := hainter.1.2
  have hy0a : y0 < a.im := hainter.2.1
  have hay1 : a.im < y1 := hainter.2.2
  let r : ℝ :=
    min ((a.re - x0) / 2)
      (min ((x1 - a.re) / 2) (min ((a.im - y0) / 2) ((y1 - a.im) / 2)))
  let xl : ℝ := a.re - r
  let xr : ℝ := a.re + r
  let yb : ℝ := a.im - r
  let yt : ℝ := a.im + r
  have hrpos0 : 0 < (a.re - x0) / 2 := by linarith
  have hrpos1 : 0 < (x1 - a.re) / 2 := by linarith
  have hrpos2 : 0 < (a.im - y0) / 2 := by linarith
  have hrpos3 : 0 < (y1 - a.im) / 2 := by linarith
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min hrpos0 (lt_min hrpos1 (lt_min hrpos2 hrpos3))
  have hrle0 : r ≤ (a.re - x0) / 2 := by
    dsimp [r]
    exact min_le_left _ _
  have hrle1 : r ≤ (x1 - a.re) / 2 := by
    dsimp [r]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hrle2 : r ≤ (a.im - y0) / 2 := by
    dsimp [r]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrle3 : r ≤ (y1 - a.im) / 2 := by
    dsimp [r]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hxl0 : x0 < xl := by
    dsimp [xl]
    linarith
  have hxlxr : xl < xr := by
    dsimp [xl, xr]
    linarith
  have hxr1 : xr < x1 := by
    dsimp [xr]
    linarith
  have hyb0 : y0 < yb := by
    dsimp [yb]
    linarith
  have hybyt : yb < yt := by
    dsimp [yb, yt]
    linarith
  have hyt1 : yt < y1 := by
    dsimp [yt]
    linarith
  have hy0_ne : y0 ≠ a.im := by linarith
  have hy1_ne : y1 ≠ a.im := by linarith
  have hxl_ne : xl ≠ a.re := by
    dsimp [xl]
    linarith
  have hxr_ne : xr ≠ a.re := by
    dsimp [xr]
    linarith
  have hsplit0 :
      boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) x0 x1 y0 y1 =
        boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) x0 xl y0 y1 +
          boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl x1 y0 y1 :=
    boundaryRectIntegral_split_vertical
      (intervalIntegrable_sub_inv_horizontal_off_im (a := a) (y := y0) hy0_ne)
      (intervalIntegrable_sub_inv_horizontal_off_im (a := a) (y := y0) hy0_ne)
      (intervalIntegrable_sub_inv_horizontal_off_im (a := a) (y := y1) hy1_ne)
      (intervalIntegrable_sub_inv_horizontal_off_im (a := a) (y := y1) hy1_ne)
  have hsplit1 :
      boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl x1 y0 y1 =
        boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr y0 y1 +
          boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xr x1 y0 y1 :=
    boundaryRectIntegral_split_vertical
      (intervalIntegrable_sub_inv_horizontal_off_im (a := a) (y := y0) hy0_ne)
      (intervalIntegrable_sub_inv_horizontal_off_im (a := a) (y := y0) hy0_ne)
      (intervalIntegrable_sub_inv_horizontal_off_im (a := a) (y := y1) hy1_ne)
      (intervalIntegrable_sub_inv_horizontal_off_im (a := a) (y := y1) hy1_ne)
  have hsplit2 :
      boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr y0 y1 =
        boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr y0 yb +
          boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr yb y1 :=
    boundaryRectIntegral_split_horizontal
      (intervalIntegrable_sub_inv_vertical_off_re (a := a) (x := xr) hxr_ne)
      (intervalIntegrable_sub_inv_vertical_off_re (a := a) (x := xr) hxr_ne)
      (intervalIntegrable_sub_inv_vertical_off_re (a := a) (x := xl) hxl_ne)
      (intervalIntegrable_sub_inv_vertical_off_re (a := a) (x := xl) hxl_ne)
  have hsplit3 :
      boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr yb y1 =
        boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr yb yt +
          boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr yt y1 :=
    boundaryRectIntegral_split_horizontal
      (intervalIntegrable_sub_inv_vertical_off_re (a := a) (x := xr) hxr_ne)
      (intervalIntegrable_sub_inv_vertical_off_re (a := a) (x := xr) hxr_ne)
      (intervalIntegrable_sub_inv_vertical_off_re (a := a) (x := xl) hxl_ne)
      (intervalIntegrable_sub_inv_vertical_off_re (a := a) (x := xl) hxl_ne)
  have hnot_left : a ∉ closedRect x0 xl y0 y1 := by
    intro hmem
    have hre : a.re ∈ Set.Icc x0 xl := by
      simpa [closedRect, Set.uIcc_of_le hxl0.le, Set.uIcc_of_le hy.le] using hmem.1
    have hlt : xl < a.re := by
      dsimp [xl]
      linarith
    exact not_le_of_gt hlt hre.2
  have hnot_right : a ∉ closedRect xr x1 y0 y1 := by
    intro hmem
    have hre : a.re ∈ Set.Icc xr x1 := by
      simpa [closedRect, Set.uIcc_of_le hxr1.le, Set.uIcc_of_le hy.le] using hmem.1
    have hlt : a.re < xr := by
      dsimp [xr]
      linarith
    exact not_le_of_gt hlt hre.1
  have hnot_bottom : a ∉ closedRect xl xr y0 yb := by
    intro hmem
    have him : a.im ∈ Set.Icc y0 yb := by
      simpa [closedRect, Set.uIcc_of_le hxlxr.le, Set.uIcc_of_le hyb0.le] using hmem.2
    have hlt : yb < a.im := by
      dsimp [yb]
      linarith
    exact not_le_of_gt hlt him.2
  have hnot_top : a ∉ closedRect xl xr yt y1 := by
    intro hmem
    have him : a.im ∈ Set.Icc yt y1 := by
      simpa [closedRect, Set.uIcc_of_le hxlxr.le, Set.uIcc_of_le hyt1.le] using hmem.2
    have hlt : a.im < yt := by
      dsimp [yt]
      linarith
    exact not_le_of_gt hlt him.1
  have hzero_left :
      boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) x0 xl y0 y1 = 0 :=
    boundaryRectIntegral_sub_inv_eq_zero_of_not_mem_closedRect hnot_left
  have hzero_right :
      boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xr x1 y0 y1 = 0 :=
    boundaryRectIntegral_sub_inv_eq_zero_of_not_mem_closedRect hnot_right
  have hzero_bottom :
      boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr y0 yb = 0 :=
    boundaryRectIntegral_sub_inv_eq_zero_of_not_mem_closedRect hnot_bottom
  have hzero_top :
      boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr yt y1 = 0 :=
    boundaryRectIntegral_sub_inv_eq_zero_of_not_mem_closedRect hnot_top
  have hsquare :
      boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr yb yt =
        2 * Real.pi * Complex.I := by
    simpa [xl, xr, yb, yt] using
      boundaryRectIntegral_sub_inv_arbitraryCenterSquare (a := a) (r := r) hr
  calc
    boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) x0 x1 y0 y1
        =
          boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) x0 xl y0 y1 +
            boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl x1 y0 y1 := hsplit0
    _ =
        boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) x0 xl y0 y1 +
          (boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr y0 y1 +
            boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xr x1 y0 y1) := by
              rw [hsplit1]
    _ =
        boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) x0 xl y0 y1 +
          (boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr y0 yb +
            boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr yb y1) +
          boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xr x1 y0 y1 := by
              rw [hsplit2]
              abel
    _ =
        boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) x0 xl y0 y1 +
          boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr y0 yb +
          boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr yb yt +
          boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xl xr yt y1 +
          boundaryRectIntegral (fun z : ℂ => (z - a)⁻¹) xr x1 y0 y1 := by
              rw [hsplit3]
              abel
    _ = 0 + 0 + (2 * Real.pi * Complex.I) + 0 + 0 := by
          rw [hzero_left, hzero_bottom, hsquare, hzero_top, hzero_right]
    _ = 2 * Real.pi * Complex.I := by simp

private lemma bottom_edge_ne_center {a : ℂ} {r x : ℝ} (hr : 0 < r) :
    x + (a.im - r) * Complex.I ≠ a := by
  intro h
  have him : a.im - r = a.im := by
    simpa using congrArg Complex.im h
  linarith

private lemma top_edge_ne_center {a : ℂ} {r x : ℝ} (hr : 0 < r) :
    x + (a.im + r) * Complex.I ≠ a := by
  intro h
  have him : a.im + r = a.im := by
    simpa using congrArg Complex.im h
  linarith

private lemma right_edge_ne_center {a : ℂ} {r y : ℝ} (hr : 0 < r) :
    a.re + r + y * Complex.I ≠ a := by
  intro h
  have hre : a.re + r = a.re := by
    simpa using congrArg Complex.re h
  linarith

private lemma left_edge_ne_center {a : ℂ} {r y : ℝ} (hr : 0 < r) :
    a.re - r + y * Complex.I ≠ a := by
  intro h
  have hre : a.re - r = a.re := by
    simpa using congrArg Complex.re h
  linarith

/--
If a square centered at `breathingRoot k` contains no other breathing roots,
then the rectangle boundary integral of `breathingFunction` around that square
is exactly `2πi` times the explicit residue candidate at `k`.

This is a noncircular local contour theorem for the specific function
`z ↦ 1 / (z^13 - 1)`. It relies only on the proved rectangle kernel theorems
and the explicit partial-fraction identity from `ResidueDefinition`.
-/
theorem boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_of_no_otherRoots_centeredSquare
    (k : ZMod CycleLen) {r : ℝ} (hr : 0 < r)
    (hother :
      ∀ j : ZMod CycleLen, j ≠ k →
        breathingRoot j ∉ closedRect
          ((breathingRoot k).re - r) ((breathingRoot k).re + r)
          ((breathingRoot k).im - r) ((breathingRoot k).im + r)) :
    boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction
      ((breathingRoot k).re - r) ((breathingRoot k).re + r)
      ((breathingRoot k).im - r) ((breathingRoot k).im + r) =
      (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt k := by
  classical
  let a : ℂ := breathingRoot k
  let x0 : ℝ := a.re - r
  let x1 : ℝ := a.re + r
  let y0 : ℝ := a.im - r
  let y1 : ℝ := a.im + r
  have hx0_mem : x0 ∈ uIcc x0 x1 := by
    simp [x0, x1, hr.le]
  have hx1_mem : x1 ∈ uIcc x0 x1 := by
    simp [x0, x1, hr.le]
  have hy0_mem : y0 ∈ uIcc y0 y1 := by
    simp [y0, y1, hr.le]
  have hy1_mem : y1 ∈ uIcc y0 y1 := by
    simp [y0, y1, hr.le]
  have hother' :
      ∀ j : ZMod CycleLen, j ≠ k → breathingRoot j ∉ closedRect x0 x1 y0 y1 := by
    intro j hj
    simpa [a, x0, x1, y0, y1] using hother j hj
  have hbottom_kernel_int :
      ∀ j : ZMod CycleLen,
        IntervalIntegrable
          (fun x : ℝ => (x + y0 * Complex.I - breathingRoot j)⁻¹)
          MeasureTheory.volume x0 x1 := by
    intro j
    have hcont :
        ContinuousOn
          (fun x : ℝ => (x + y0 * Complex.I - breathingRoot j)⁻¹)
          (uIcc x0 x1) := by
      refine (by
        fun_prop : ContinuousOn
          (fun x : ℝ => (x + y0 * Complex.I - breathingRoot j : ℂ))
          (uIcc x0 x1)).inv₀ ?_
      intro x hx hzero
      by_cases hjk : j = k
      · subst hjk
        have hneq : x + y0 * Complex.I ≠ a := by
          simpa [a, y0] using bottom_edge_ne_center (a := a) (r := r) (x := x) hr
        exact hneq (by simpa [a] using sub_eq_zero.mp hzero)
      · have hz : x + y0 * Complex.I = breathingRoot j := sub_eq_zero.mp hzero
        have hmem : breathingRoot j ∈ closedRect x0 x1 y0 y1 := by
          rw [closedRect, ← hz]
          change (x + y0 * Complex.I).re ∈ uIcc x0 x1 ∧ (x + y0 * Complex.I).im ∈ uIcc y0 y1
          constructor
          · simpa using hx
          · simpa using hy0_mem
        exact hother' j hjk hmem
    exact ContinuousOn.intervalIntegrable
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hcont
  have htop_kernel_int :
      ∀ j : ZMod CycleLen,
        IntervalIntegrable
          (fun x : ℝ => (x + y1 * Complex.I - breathingRoot j)⁻¹)
          MeasureTheory.volume x0 x1 := by
    intro j
    have hcont :
        ContinuousOn
          (fun x : ℝ => (x + y1 * Complex.I - breathingRoot j)⁻¹)
          (uIcc x0 x1) := by
      refine (by
        fun_prop : ContinuousOn
          (fun x : ℝ => (x + y1 * Complex.I - breathingRoot j : ℂ))
          (uIcc x0 x1)).inv₀ ?_
      intro x hx hzero
      by_cases hjk : j = k
      · subst hjk
        have hneq : x + y1 * Complex.I ≠ a := by
          simpa [a, y1] using top_edge_ne_center (a := a) (r := r) (x := x) hr
        exact hneq (by simpa [a] using sub_eq_zero.mp hzero)
      · have hz : x + y1 * Complex.I = breathingRoot j := sub_eq_zero.mp hzero
        have hmem : breathingRoot j ∈ closedRect x0 x1 y0 y1 := by
          rw [closedRect, ← hz]
          change (x + y1 * Complex.I).re ∈ uIcc x0 x1 ∧ (x + y1 * Complex.I).im ∈ uIcc y0 y1
          constructor
          · simpa using hx
          · simpa using hy1_mem
        exact hother' j hjk hmem
    exact ContinuousOn.intervalIntegrable
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hcont
  have hright_kernel_int :
      ∀ j : ZMod CycleLen,
        IntervalIntegrable
          (fun y : ℝ => (x1 + y * Complex.I - breathingRoot j)⁻¹)
          MeasureTheory.volume y0 y1 := by
    intro j
    have hcont :
        ContinuousOn
          (fun y : ℝ => (x1 + y * Complex.I - breathingRoot j)⁻¹)
          (uIcc y0 y1) := by
      refine (by
        fun_prop : ContinuousOn
          (fun y : ℝ => (x1 + y * Complex.I - breathingRoot j : ℂ))
          (uIcc y0 y1)).inv₀ ?_
      intro y hy hzero
      by_cases hjk : j = k
      · subst hjk
        have hneq : x1 + y * Complex.I ≠ a := by
          simpa [a, x1] using right_edge_ne_center (a := a) (r := r) (y := y) hr
        exact hneq (by simpa [a] using sub_eq_zero.mp hzero)
      · have hz : x1 + y * Complex.I = breathingRoot j := sub_eq_zero.mp hzero
        have hmem : breathingRoot j ∈ closedRect x0 x1 y0 y1 := by
          rw [closedRect, ← hz]
          change (x1 + y * Complex.I).re ∈ uIcc x0 x1 ∧ (x1 + y * Complex.I).im ∈ uIcc y0 y1
          constructor
          · simpa using hx1_mem
          · simpa using hy
        exact hother' j hjk hmem
    exact ContinuousOn.intervalIntegrable
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hcont
  have hleft_kernel_int :
      ∀ j : ZMod CycleLen,
        IntervalIntegrable
          (fun y : ℝ => (x0 + y * Complex.I - breathingRoot j)⁻¹)
          MeasureTheory.volume y0 y1 := by
    intro j
    have hcont :
        ContinuousOn
          (fun y : ℝ => (x0 + y * Complex.I - breathingRoot j)⁻¹)
          (uIcc y0 y1) := by
      refine (by
        fun_prop : ContinuousOn
          (fun y : ℝ => (x0 + y * Complex.I - breathingRoot j : ℂ))
          (uIcc y0 y1)).inv₀ ?_
      intro y hy hzero
      by_cases hjk : j = k
      · subst hjk
        have hneq : x0 + y * Complex.I ≠ a := by
          simpa [a, x0] using left_edge_ne_center (a := a) (r := r) (y := y) hr
        exact hneq (by simpa [a] using sub_eq_zero.mp hzero)
      · have hz : x0 + y * Complex.I = breathingRoot j := sub_eq_zero.mp hzero
        have hmem : breathingRoot j ∈ closedRect x0 x1 y0 y1 := by
          rw [closedRect, ← hz]
          change (x0 + y * Complex.I).re ∈ uIcc x0 x1 ∧ (x0 + y * Complex.I).im ∈ uIcc y0 y1
          constructor
          · simpa using hx0_mem
          · simpa using hy
        exact hother' j hjk hmem
    exact ContinuousOn.intervalIntegrable
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hcont
  have hbottom_den :
      ∀ x ∈ uIcc x0 x1,
        UFRF.ResidueDefinition.breathingDenominator (x + y0 * Complex.I) ≠ 0 := by
    intro x hx hzero
    obtain ⟨j, hj⟩ := exists_breathingRoot_of_breathingDenominator_eq_zero hzero
    by_cases hjk : j = k
    · subst hjk
      have hneq : x + y0 * Complex.I ≠ a := by
        simpa [a, y0] using bottom_edge_ne_center (a := a) (r := r) (x := x) hr
      exact hneq (by simpa [a] using hj)
    · have hmem : breathingRoot j ∈ closedRect x0 x1 y0 y1 := by
        rw [closedRect, ← hj]
        change (x + y0 * Complex.I).re ∈ uIcc x0 x1 ∧ (x + y0 * Complex.I).im ∈ uIcc y0 y1
        constructor
        · simpa using hx
        · simpa using hy0_mem
      exact hother' j hjk hmem
  have htop_den :
      ∀ x ∈ uIcc x0 x1,
        UFRF.ResidueDefinition.breathingDenominator (x + y1 * Complex.I) ≠ 0 := by
    intro x hx hzero
    obtain ⟨j, hj⟩ := exists_breathingRoot_of_breathingDenominator_eq_zero hzero
    by_cases hjk : j = k
    · subst hjk
      have hneq : x + y1 * Complex.I ≠ a := by
        simpa [a, y1] using top_edge_ne_center (a := a) (r := r) (x := x) hr
      exact hneq (by simpa [a] using hj)
    · have hmem : breathingRoot j ∈ closedRect x0 x1 y0 y1 := by
        rw [closedRect, ← hj]
        change (x + y1 * Complex.I).re ∈ uIcc x0 x1 ∧ (x + y1 * Complex.I).im ∈ uIcc y0 y1
        constructor
        · simpa using hx
        · simpa using hy1_mem
      exact hother' j hjk hmem
  have hright_den :
      ∀ y ∈ uIcc y0 y1,
        UFRF.ResidueDefinition.breathingDenominator (x1 + y * Complex.I) ≠ 0 := by
    intro y hy hzero
    obtain ⟨j, hj⟩ := exists_breathingRoot_of_breathingDenominator_eq_zero hzero
    by_cases hjk : j = k
    · subst hjk
      have hneq : x1 + y * Complex.I ≠ a := by
        simpa [a, x1] using right_edge_ne_center (a := a) (r := r) (y := y) hr
      exact hneq (by simpa [a] using hj)
    · have hmem : breathingRoot j ∈ closedRect x0 x1 y0 y1 := by
        rw [closedRect, ← hj]
        change (x1 + y * Complex.I).re ∈ uIcc x0 x1 ∧ (x1 + y * Complex.I).im ∈ uIcc y0 y1
        constructor
        · simpa using hx1_mem
        · simpa using hy
      exact hother' j hjk hmem
  have hleft_den :
      ∀ y ∈ uIcc y0 y1,
        UFRF.ResidueDefinition.breathingDenominator (x0 + y * Complex.I) ≠ 0 := by
    intro y hy hzero
    obtain ⟨j, hj⟩ := exists_breathingRoot_of_breathingDenominator_eq_zero hzero
    by_cases hjk : j = k
    · subst hjk
      have hneq : x0 + y * Complex.I ≠ a := by
        simpa [a, x0] using left_edge_ne_center (a := a) (r := r) (y := y) hr
      exact hneq (by simpa [a] using hj)
    · have hmem : breathingRoot j ∈ closedRect x0 x1 y0 y1 := by
        rw [closedRect, ← hj]
        change (x0 + y * Complex.I).re ∈ uIcc x0 x1 ∧ (x0 + y * Complex.I).im ∈ uIcc y0 y1
        constructor
        · simpa using hx0_mem
        · simpa using hy
      exact hother' j hjk hmem
  have hbottom_pf :
      (∫ x : ℝ in x0..x1, UFRF.ResidueDefinition.breathingFunction (x + y0 * Complex.I)) =
        ∑ j : ZMod CycleLen,
          UFRF.ResidueDefinition.residueCandidateAt j •
            (∫ x : ℝ in x0..x1, (x + y0 * Complex.I - breathingRoot j)⁻¹) := by
    calc
      (∫ x : ℝ in x0..x1, UFRF.ResidueDefinition.breathingFunction (x + y0 * Complex.I))
          =
            ∫ x : ℝ in x0..x1,
              ∑ j : ZMod CycleLen,
                UFRF.ResidueDefinition.residueCandidateAt j •
                  (x + y0 * Complex.I - breathingRoot j)⁻¹ := by
                    refine intervalIntegral.integral_congr ?_
                    intro x hx
                    simpa [smul_eq_mul] using
                      UFRF.ResidueDefinition.breathingFunction_eq_sum_residueCandidateAt_sub_inv
                        (z := x + y0 * Complex.I) (hbottom_den x hx)
      _ =
          ∑ j : ZMod CycleLen,
            ∫ x : ℝ in x0..x1,
              UFRF.ResidueDefinition.residueCandidateAt j •
                (x + y0 * Complex.I - breathingRoot j)⁻¹ := by
                  simpa using
                    (intervalIntegral.integral_finset_sum
                      (s := Finset.univ)
                      (f := fun j x =>
                        UFRF.ResidueDefinition.residueCandidateAt j •
                          (x + y0 * Complex.I - breathingRoot j)⁻¹)
                      (fun j hj => (hbottom_kernel_int j).smul
                        (UFRF.ResidueDefinition.residueCandidateAt j)))
      _ =
          ∑ j : ZMod CycleLen,
            UFRF.ResidueDefinition.residueCandidateAt j •
              (∫ x : ℝ in x0..x1, (x + y0 * Complex.I - breathingRoot j)⁻¹) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [smul_eq_mul]
                exact
                  (intervalIntegral.integral_const_mul
                    (a := x0) (b := x1)
                    (r := UFRF.ResidueDefinition.residueCandidateAt j)
                    (f := fun x : ℝ => (x + y0 * Complex.I - breathingRoot j)⁻¹))
  have htop_pf :
      (∫ x : ℝ in x0..x1, UFRF.ResidueDefinition.breathingFunction (x + y1 * Complex.I)) =
        ∑ j : ZMod CycleLen,
          UFRF.ResidueDefinition.residueCandidateAt j •
            (∫ x : ℝ in x0..x1, (x + y1 * Complex.I - breathingRoot j)⁻¹) := by
    calc
      (∫ x : ℝ in x0..x1, UFRF.ResidueDefinition.breathingFunction (x + y1 * Complex.I))
          =
            ∫ x : ℝ in x0..x1,
              ∑ j : ZMod CycleLen,
                UFRF.ResidueDefinition.residueCandidateAt j •
                  (x + y1 * Complex.I - breathingRoot j)⁻¹ := by
                    refine intervalIntegral.integral_congr ?_
                    intro x hx
                    simpa [smul_eq_mul] using
                      UFRF.ResidueDefinition.breathingFunction_eq_sum_residueCandidateAt_sub_inv
                        (z := x + y1 * Complex.I) (htop_den x hx)
      _ =
          ∑ j : ZMod CycleLen,
            ∫ x : ℝ in x0..x1,
              UFRF.ResidueDefinition.residueCandidateAt j •
                (x + y1 * Complex.I - breathingRoot j)⁻¹ := by
                  simpa using
                    (intervalIntegral.integral_finset_sum
                      (s := Finset.univ)
                      (f := fun j x =>
                        UFRF.ResidueDefinition.residueCandidateAt j •
                          (x + y1 * Complex.I - breathingRoot j)⁻¹)
                      (fun j hj => (htop_kernel_int j).smul
                        (UFRF.ResidueDefinition.residueCandidateAt j)))
      _ =
          ∑ j : ZMod CycleLen,
            UFRF.ResidueDefinition.residueCandidateAt j •
              (∫ x : ℝ in x0..x1, (x + y1 * Complex.I - breathingRoot j)⁻¹) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [smul_eq_mul]
                exact
                  (intervalIntegral.integral_const_mul
                    (a := x0) (b := x1)
                    (r := UFRF.ResidueDefinition.residueCandidateAt j)
                    (f := fun x : ℝ => (x + y1 * Complex.I - breathingRoot j)⁻¹))
  have hright_pf :
      (∫ y : ℝ in y0..y1, UFRF.ResidueDefinition.breathingFunction (x1 + y * Complex.I)) =
        ∑ j : ZMod CycleLen,
          UFRF.ResidueDefinition.residueCandidateAt j •
            (∫ y : ℝ in y0..y1, (x1 + y * Complex.I - breathingRoot j)⁻¹) := by
    calc
      (∫ y : ℝ in y0..y1, UFRF.ResidueDefinition.breathingFunction (x1 + y * Complex.I))
          =
            ∫ y : ℝ in y0..y1,
              ∑ j : ZMod CycleLen,
                UFRF.ResidueDefinition.residueCandidateAt j •
                  (x1 + y * Complex.I - breathingRoot j)⁻¹ := by
                    refine intervalIntegral.integral_congr ?_
                    intro y hy
                    simpa [smul_eq_mul] using
                      UFRF.ResidueDefinition.breathingFunction_eq_sum_residueCandidateAt_sub_inv
                        (z := x1 + y * Complex.I) (hright_den y hy)
      _ =
          ∑ j : ZMod CycleLen,
            ∫ y : ℝ in y0..y1,
              UFRF.ResidueDefinition.residueCandidateAt j •
                (x1 + y * Complex.I - breathingRoot j)⁻¹ := by
                  simpa using
                    (intervalIntegral.integral_finset_sum
                      (s := Finset.univ)
                      (f := fun j y =>
                        UFRF.ResidueDefinition.residueCandidateAt j •
                          (x1 + y * Complex.I - breathingRoot j)⁻¹)
                      (fun j hj => (hright_kernel_int j).smul
                        (UFRF.ResidueDefinition.residueCandidateAt j)))
      _ =
          ∑ j : ZMod CycleLen,
            UFRF.ResidueDefinition.residueCandidateAt j •
              (∫ y : ℝ in y0..y1, (x1 + y * Complex.I - breathingRoot j)⁻¹) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [smul_eq_mul]
                exact
                  (intervalIntegral.integral_const_mul
                    (a := y0) (b := y1)
                    (r := UFRF.ResidueDefinition.residueCandidateAt j)
                    (f := fun y : ℝ => (x1 + y * Complex.I - breathingRoot j)⁻¹))
  have hleft_pf :
      (∫ y : ℝ in y0..y1, UFRF.ResidueDefinition.breathingFunction (x0 + y * Complex.I)) =
        ∑ j : ZMod CycleLen,
          UFRF.ResidueDefinition.residueCandidateAt j •
            (∫ y : ℝ in y0..y1, (x0 + y * Complex.I - breathingRoot j)⁻¹) := by
    calc
      (∫ y : ℝ in y0..y1, UFRF.ResidueDefinition.breathingFunction (x0 + y * Complex.I))
          =
            ∫ y : ℝ in y0..y1,
              ∑ j : ZMod CycleLen,
                UFRF.ResidueDefinition.residueCandidateAt j •
                  (x0 + y * Complex.I - breathingRoot j)⁻¹ := by
                    refine intervalIntegral.integral_congr ?_
                    intro y hy
                    simpa [smul_eq_mul] using
                      UFRF.ResidueDefinition.breathingFunction_eq_sum_residueCandidateAt_sub_inv
                        (z := x0 + y * Complex.I) (hleft_den y hy)
      _ =
          ∑ j : ZMod CycleLen,
            ∫ y : ℝ in y0..y1,
              UFRF.ResidueDefinition.residueCandidateAt j •
                (x0 + y * Complex.I - breathingRoot j)⁻¹ := by
                  simpa using
                    (intervalIntegral.integral_finset_sum
                      (s := Finset.univ)
                      (f := fun j y =>
                        UFRF.ResidueDefinition.residueCandidateAt j •
                          (x0 + y * Complex.I - breathingRoot j)⁻¹)
                      (fun j hj => (hleft_kernel_int j).smul
                        (UFRF.ResidueDefinition.residueCandidateAt j)))
      _ =
          ∑ j : ZMod CycleLen,
            UFRF.ResidueDefinition.residueCandidateAt j •
              (∫ y : ℝ in y0..y1, (x0 + y * Complex.I - breathingRoot j)⁻¹) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [smul_eq_mul]
                exact
                  (intervalIntegral.integral_const_mul
                    (a := y0) (b := y1)
                    (r := UFRF.ResidueDefinition.residueCandidateAt j)
                    (f := fun y : ℝ => (x0 + y * Complex.I - breathingRoot j)⁻¹))
  have hsum :
      boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction x0 x1 y0 y1 =
        ∑ j : ZMod CycleLen,
          UFRF.ResidueDefinition.residueCandidateAt j •
            boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1 := by
    calc
      boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction x0 x1 y0 y1
          =
            ((∑ j : ZMod CycleLen,
                UFRF.ResidueDefinition.residueCandidateAt j •
                  (∫ x : ℝ in x0..x1, (x + y0 * Complex.I - breathingRoot j)⁻¹)) -
              (∑ j : ZMod CycleLen,
                UFRF.ResidueDefinition.residueCandidateAt j •
                  (∫ x : ℝ in x0..x1, (x + y1 * Complex.I - breathingRoot j)⁻¹)) +
              Complex.I •
                (∑ j : ZMod CycleLen,
                  UFRF.ResidueDefinition.residueCandidateAt j •
                    (∫ y : ℝ in y0..y1, (x1 + y * Complex.I - breathingRoot j)⁻¹)) -
              Complex.I •
                (∑ j : ZMod CycleLen,
                  UFRF.ResidueDefinition.residueCandidateAt j •
                    (∫ y : ℝ in y0..y1, (x0 + y * Complex.I - breathingRoot j)⁻¹))) := by
              rw [boundaryRectIntegral, hbottom_pf, htop_pf, hright_pf, hleft_pf]
      _ =
          ∑ j : ZMod CycleLen,
            UFRF.ResidueDefinition.residueCandidateAt j •
              boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1 := by
                symm
                simp_rw [boundaryRectIntegral, smul_sub, smul_add, smul_smul, sub_eq_add_neg]
                have h1 :
                    ∑ x : ZMod CycleLen,
                      UFRF.ResidueDefinition.residueCandidateAt x •
                        ((∫ x_1 : ℝ in x0..x1, (x_1 + y0 * Complex.I + -breathingRoot x)⁻¹) +
                          -(∫ x_1 : ℝ in x0..x1, (x_1 + y1 * Complex.I + -breathingRoot x)⁻¹)) =
                      (∑ x : ZMod CycleLen,
                        UFRF.ResidueDefinition.residueCandidateAt x •
                          (∫ x_1 : ℝ in x0..x1, (x_1 + y0 * Complex.I + -breathingRoot x)⁻¹)) +
                      -(∑ x : ZMod CycleLen,
                        UFRF.ResidueDefinition.residueCandidateAt x •
                          (∫ x_1 : ℝ in x0..x1, (x_1 + y1 * Complex.I + -breathingRoot x)⁻¹)) := by
                    simp_rw [smul_add, smul_neg]
                    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
                have h2 :
                    ∑ x : ZMod CycleLen,
                      (UFRF.ResidueDefinition.residueCandidateAt x * Complex.I) •
                        (∫ y : ℝ in y0..y1, (x1 + y * Complex.I + -breathingRoot x)⁻¹) =
                      Complex.I •
                        (∑ x : ZMod CycleLen,
                          UFRF.ResidueDefinition.residueCandidateAt x •
                            (∫ y : ℝ in y0..y1, (x1 + y * Complex.I + -breathingRoot x)⁻¹)) := by
                    calc
                      ∑ x : ZMod CycleLen,
                          (UFRF.ResidueDefinition.residueCandidateAt x * Complex.I) •
                            (∫ y : ℝ in y0..y1, (x1 + y * Complex.I + -breathingRoot x)⁻¹)
                          =
                            ∑ x : ZMod CycleLen,
                              Complex.I •
                                (UFRF.ResidueDefinition.residueCandidateAt x •
                                  (∫ y : ℝ in y0..y1, (x1 + y * Complex.I + -breathingRoot x)⁻¹)) := by
                                    simp_rw [smul_smul, mul_comm Complex.I]
                      _ =
                          Complex.I •
                            (∑ x : ZMod CycleLen,
                              UFRF.ResidueDefinition.residueCandidateAt x •
                                (∫ y : ℝ in y0..y1, (x1 + y * Complex.I + -breathingRoot x)⁻¹)) := by
                                  rw [← Finset.smul_sum]
                have h3 :
                    ∑ x : ZMod CycleLen,
                      -((UFRF.ResidueDefinition.residueCandidateAt x * Complex.I) •
                        (∫ y : ℝ in y0..y1, (x0 + y * Complex.I + -breathingRoot x)⁻¹)) =
                      -(Complex.I •
                        (∑ x : ZMod CycleLen,
                          UFRF.ResidueDefinition.residueCandidateAt x •
                            (∫ y : ℝ in y0..y1, (x0 + y * Complex.I + -breathingRoot x)⁻¹))) := by
                    calc
                      ∑ x : ZMod CycleLen,
                          -((UFRF.ResidueDefinition.residueCandidateAt x * Complex.I) •
                            (∫ y : ℝ in y0..y1, (x0 + y * Complex.I + -breathingRoot x)⁻¹))
                          =
                            ∑ x : ZMod CycleLen,
                              -(Complex.I •
                                (UFRF.ResidueDefinition.residueCandidateAt x •
                                  (∫ y : ℝ in y0..y1, (x0 + y * Complex.I + -breathingRoot x)⁻¹))) := by
                                    simp_rw [smul_smul, mul_comm Complex.I]
                      _ =
                          -(∑ x : ZMod CycleLen,
                            Complex.I •
                              (UFRF.ResidueDefinition.residueCandidateAt x •
                                (∫ y : ℝ in y0..y1, (x0 + y * Complex.I + -breathingRoot x)⁻¹))) := by
                                  rw [Finset.sum_neg_distrib]
                      _ =
                          -(Complex.I •
                            (∑ x : ZMod CycleLen,
                              UFRF.ResidueDefinition.residueCandidateAt x •
                                (∫ y : ℝ in y0..y1, (x0 + y * Complex.I + -breathingRoot x)⁻¹))) := by
                                  rw [← Finset.smul_sum]
                rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                rw [h1, h2, h3]
  have hkernel_zero :
      ∀ j : ZMod CycleLen, j ≠ k →
        boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1 = 0 := by
    intro j hj
    exact boundaryRectIntegral_sub_inv_eq_zero_of_not_mem_closedRect (hother' j hj)
  have hkernel_main :
      boundaryRectIntegral (fun z : ℂ => (z - breathingRoot k)⁻¹) x0 x1 y0 y1 =
        2 * Real.pi * Complex.I := by
    simpa [a, x0, x1, y0, y1] using
      boundaryRectIntegral_sub_inv_arbitraryCenterSquare (a := breathingRoot k) (r := r) hr
  calc
    boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction x0 x1 y0 y1
        =
          ∑ j : ZMod CycleLen,
            UFRF.ResidueDefinition.residueCandidateAt j •
              boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1 := hsum
    _ =
        UFRF.ResidueDefinition.residueCandidateAt k •
          boundaryRectIntegral (fun z : ℂ => (z - breathingRoot k)⁻¹) x0 x1 y0 y1 := by
            refine Finset.sum_eq_single k ?_ ?_
            · intro j hj hne
              simp [hkernel_zero j hne]
            · intro hk
              simp at hk
    _ = (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt k := by
          rw [hkernel_main]
          simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]

private lemma mem_closedBall_of_mem_closedRect_centered {a z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hz : z ∈ closedRect (a.re - r) (a.re + r) (a.im - r) (a.im + r)) :
    z ∈ Metric.closedBall a (2 * r) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hre : a.re - r ≤ a.re + r := by linarith
  have him : a.im - r ≤ a.im + r := by linarith
  have hzre : z.re ∈ Set.Icc (a.re - r) (a.re + r) := by
    simpa [closedRect, Set.uIcc_of_le hre] using hz.1
  have hzim : z.im ∈ Set.Icc (a.im - r) (a.im + r) := by
    simpa [closedRect, Set.uIcc_of_le him] using hz.2
  have hzre' : |(z - a).re| ≤ r := by
    rw [sub_re, abs_le]
    rcases hzre with ⟨h0, h1⟩
    constructor <;> linarith
  have hzim' : |(z - a).im| ≤ r := by
    rw [sub_im, abs_le]
    rcases hzim with ⟨h0, h1⟩
    constructor <;> linarith
  calc
    ‖z - a‖ ≤ |(z - a).re| + |(z - a).im| := Complex.norm_le_abs_re_add_abs_im (z - a)
    _ ≤ r + r := add_le_add hzre' hzim'
    _ = 2 * r := by ring

/--
The canonical quarter-`infsep` square around `breathingRoot k` excludes every
other breathing root.

This upgrades the local square theorem's explicit no-other-roots hypothesis to
a canonical geometric fact derived from the global breathing-root separation
package.
-/
theorem quarter_infsep_closedRect_excludes_other_breathingRoots
    (k : ZMod CycleLen) :
    ∀ j : ZMod CycleLen, j ≠ k →
      breathingRoot j ∉ closedRect
        ((breathingRoot k).re - ((Set.range breathingRoot : Set ℂ).infsep / 4))
        ((breathingRoot k).re + ((Set.range breathingRoot : Set ℂ).infsep / 4))
        ((breathingRoot k).im - ((Set.range breathingRoot : Set ℂ).infsep / 4))
        ((breathingRoot k).im + ((Set.range breathingRoot : Set ℂ).infsep / 4)) := by
  intro j hj hmem
  let r : ℝ := ((Set.range breathingRoot : Set ℂ).infsep) / 4
  have hpos : 0 < (Set.range breathingRoot : Set ℂ).infsep := breathingRootSet_infsep_pos
  have hr : 0 ≤ r := by positivity
  have hrad : 2 * r = ((Set.range breathingRoot : Set ℂ).infsep) / 2 := by
    unfold r
    ring
  have hball' :
      breathingRoot j ∈ Metric.closedBall (breathingRoot k) (2 * r) :=
    mem_closedBall_of_mem_closedRect_centered
      (a := breathingRoot k) (z := breathingRoot j) hr (by simpa [r] using hmem)
  have hball :
      breathingRoot j ∈ Metric.closedBall (breathingRoot k)
        (((Set.range breathingRoot : Set ℂ).infsep) / 2) := by
    simpa [hrad] using hball'
  exact (half_infsep_closedBall_excludes_other_breathingRoots k j hj) hball

/--
The breathing function integrates to `2πi` times the explicit residue
candidate on the canonical quarter-`infsep` square around any chosen breathing
root.

This is the canonical noncircular local contour theorem for the specific
function `z ↦ 1 / (z^13 - 1)`.
-/
theorem boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_quarter_infsep_centeredSquare
    (k : ZMod CycleLen) :
    boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction
      ((breathingRoot k).re - ((Set.range breathingRoot : Set ℂ).infsep / 4))
      ((breathingRoot k).re + ((Set.range breathingRoot : Set ℂ).infsep / 4))
      ((breathingRoot k).im - ((Set.range breathingRoot : Set ℂ).infsep / 4))
      ((breathingRoot k).im + ((Set.range breathingRoot : Set ℂ).infsep / 4)) =
      (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt k := by
  have hpos : 0 < (Set.range breathingRoot : Set ℂ).infsep := breathingRootSet_infsep_pos
  have hr : 0 < ((Set.range breathingRoot : Set ℂ).infsep / 4) := by positivity
  simpa using
    boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_of_no_otherRoots_centeredSquare
      k hr (quarter_infsep_closedRect_excludes_other_breathingRoots k)

/--
For any finite family of breathing roots, the sum of the canonical
quarter-`infsep` local square boundary integrals equals `2πi` times the sum of
the explicit residue candidates.

This is the local-square analogue of the earlier finite-family circle-sum
formula.
-/
theorem sum_boundaryRectIntegral_breathingFunction_quarter_infsep_centeredSquare_eq_two_pi_I_mul_sum_residueCandidate
    (S : Finset (ZMod CycleLen)) :
    Finset.sum S (fun k =>
      boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction
        ((breathingRoot k).re - ((Set.range breathingRoot : Set ℂ).infsep / 4))
        ((breathingRoot k).re + ((Set.range breathingRoot : Set ℂ).infsep / 4))
        ((breathingRoot k).im - ((Set.range breathingRoot : Set ℂ).infsep / 4))
        ((breathingRoot k).im + ((Set.range breathingRoot : Set ℂ).infsep / 4))) =
      (2 * Real.pi * Complex.I) *
        Finset.sum S UFRF.ResidueDefinition.residueCandidateAt := by
  calc
    Finset.sum S (fun k =>
        boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction
          ((breathingRoot k).re - ((Set.range breathingRoot : Set ℂ).infsep / 4))
          ((breathingRoot k).re + ((Set.range breathingRoot : Set ℂ).infsep / 4))
          ((breathingRoot k).im - ((Set.range breathingRoot : Set ℂ).infsep / 4))
          ((breathingRoot k).im + ((Set.range breathingRoot : Set ℂ).infsep / 4)))
        =
          Finset.sum S (fun k =>
            (2 * Real.pi * Complex.I) *
              UFRF.ResidueDefinition.residueCandidateAt k) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_quarter_infsep_centeredSquare k
    _ =
        (2 * Real.pi * Complex.I) *
          Finset.sum S UFRF.ResidueDefinition.residueCandidateAt := by
            rw [Finset.mul_sum]

private lemma bottom_edge_not_mem_interior_closedRect
    {x0 x1 y0 y1 x : ℝ} (hx : x0 < x1) (hy : y0 < y1) :
    x + y0 * Complex.I ∉ interior (closedRect x0 x1 y0 y1) := by
  intro hmem
  rw [closedRect, interior_reProdIm, Set.uIcc_of_le hx.le, Set.uIcc_of_le hy.le,
    interior_Icc, mem_reProdIm] at hmem
  have hy0' : y0 ∈ Set.Ioo y0 y1 := by
    simpa using hmem.2
  exact (lt_irrefl y0) hy0'.1

private lemma top_edge_not_mem_interior_closedRect
    {x0 x1 y0 y1 x : ℝ} (hx : x0 < x1) (hy : y0 < y1) :
    x + y1 * Complex.I ∉ interior (closedRect x0 x1 y0 y1) := by
  intro hmem
  rw [closedRect, interior_reProdIm, Set.uIcc_of_le hx.le, Set.uIcc_of_le hy.le,
    interior_Icc, mem_reProdIm] at hmem
  have hy1' : y1 ∈ Set.Ioo y0 y1 := by
    simpa using hmem.2
  exact (lt_irrefl y1) hy1'.2

private lemma right_edge_not_mem_interior_closedRect
    {x0 x1 y0 y1 y : ℝ} (hx : x0 < x1) (hy : y0 < y1) :
    x1 + y * Complex.I ∉ interior (closedRect x0 x1 y0 y1) := by
  intro hmem
  rw [closedRect, interior_reProdIm, Set.uIcc_of_le hx.le, Set.uIcc_of_le hy.le,
    interior_Icc, mem_reProdIm] at hmem
  have hx1' : x1 ∈ Set.Ioo x0 x1 := by
    simpa using hmem.1
  exact (lt_irrefl x1) hx1'.2

private lemma left_edge_not_mem_interior_closedRect
    {x0 x1 y0 y1 y : ℝ} (hx : x0 < x1) (hy : y0 < y1) :
    x0 + y * Complex.I ∉ interior (closedRect x0 x1 y0 y1) := by
  intro hmem
  rw [closedRect, interior_reProdIm, Set.uIcc_of_le hx.le, Set.uIcc_of_le hy.le,
    interior_Icc, mem_reProdIm] at hmem
  have hx0' : x0 ∈ Set.Ioo x0 x1 := by
    simpa using hmem.1
  exact (lt_irrefl x0) hx0'.1

private theorem boundaryRectIntegral_breathingFunction_eq_sum_residueCandidateAt_kernel_of_edge_den_nonzero
    {x0 x1 y0 y1 : ℝ}
    (hbottom_den :
      ∀ x ∈ uIcc x0 x1,
        UFRF.ResidueDefinition.breathingDenominator (x + y0 * Complex.I) ≠ 0)
    (htop_den :
      ∀ x ∈ uIcc x0 x1,
        UFRF.ResidueDefinition.breathingDenominator (x + y1 * Complex.I) ≠ 0)
    (hright_den :
      ∀ y ∈ uIcc y0 y1,
        UFRF.ResidueDefinition.breathingDenominator (x1 + y * Complex.I) ≠ 0)
    (hleft_den :
      ∀ y ∈ uIcc y0 y1,
        UFRF.ResidueDefinition.breathingDenominator (x0 + y * Complex.I) ≠ 0) :
    boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction x0 x1 y0 y1 =
      ∑ j : ZMod CycleLen,
        UFRF.ResidueDefinition.residueCandidateAt j •
          boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1 := by
  have hbottom_kernel_int :
      ∀ j : ZMod CycleLen,
        IntervalIntegrable
          (fun x : ℝ => (x + y0 * Complex.I - breathingRoot j)⁻¹)
          MeasureTheory.volume x0 x1 := by
    intro j
    refine intervalIntegrable_sub_inv_horizontal_of_ne ?_
    intro x hx hzero
    exact (hbottom_den x hx) (by
      simpa [hzero] using UFRF.ResidueDefinition.breathingDenominator_vanishes_at_root j)
  have htop_kernel_int :
      ∀ j : ZMod CycleLen,
        IntervalIntegrable
          (fun x : ℝ => (x + y1 * Complex.I - breathingRoot j)⁻¹)
          MeasureTheory.volume x0 x1 := by
    intro j
    refine intervalIntegrable_sub_inv_horizontal_of_ne ?_
    intro x hx hzero
    exact (htop_den x hx) (by
      simpa [hzero] using UFRF.ResidueDefinition.breathingDenominator_vanishes_at_root j)
  have hright_kernel_int :
      ∀ j : ZMod CycleLen,
        IntervalIntegrable
          (fun y : ℝ => (x1 + y * Complex.I - breathingRoot j)⁻¹)
          MeasureTheory.volume y0 y1 := by
    intro j
    refine intervalIntegrable_sub_inv_vertical_of_ne ?_
    intro y hy hzero
    exact (hright_den y hy) (by
      simpa [hzero] using UFRF.ResidueDefinition.breathingDenominator_vanishes_at_root j)
  have hleft_kernel_int :
      ∀ j : ZMod CycleLen,
        IntervalIntegrable
          (fun y : ℝ => (x0 + y * Complex.I - breathingRoot j)⁻¹)
          MeasureTheory.volume y0 y1 := by
    intro j
    refine intervalIntegrable_sub_inv_vertical_of_ne ?_
    intro y hy hzero
    exact (hleft_den y hy) (by
      simpa [hzero] using UFRF.ResidueDefinition.breathingDenominator_vanishes_at_root j)
  have hbottom_pf :
      (∫ x : ℝ in x0..x1, UFRF.ResidueDefinition.breathingFunction (x + y0 * Complex.I)) =
        ∑ j : ZMod CycleLen,
          UFRF.ResidueDefinition.residueCandidateAt j •
            (∫ x : ℝ in x0..x1, (x + y0 * Complex.I - breathingRoot j)⁻¹) := by
    calc
      (∫ x : ℝ in x0..x1, UFRF.ResidueDefinition.breathingFunction (x + y0 * Complex.I))
          =
            ∫ x : ℝ in x0..x1,
              ∑ j : ZMod CycleLen,
                UFRF.ResidueDefinition.residueCandidateAt j •
                  (x + y0 * Complex.I - breathingRoot j)⁻¹ := by
                    refine intervalIntegral.integral_congr ?_
                    intro x hx
                    simpa [smul_eq_mul] using
                      UFRF.ResidueDefinition.breathingFunction_eq_sum_residueCandidateAt_sub_inv
                        (z := x + y0 * Complex.I) (hbottom_den x hx)
      _ =
          ∑ j : ZMod CycleLen,
            ∫ x : ℝ in x0..x1,
              UFRF.ResidueDefinition.residueCandidateAt j •
                (x + y0 * Complex.I - breathingRoot j)⁻¹ := by
                  simpa using
                    (intervalIntegral.integral_finset_sum
                      (s := Finset.univ)
                      (f := fun j x =>
                        UFRF.ResidueDefinition.residueCandidateAt j •
                          (x + y0 * Complex.I - breathingRoot j)⁻¹)
                      (fun j hj => (hbottom_kernel_int j).smul
                        (UFRF.ResidueDefinition.residueCandidateAt j)))
      _ =
          ∑ j : ZMod CycleLen,
            UFRF.ResidueDefinition.residueCandidateAt j •
              (∫ x : ℝ in x0..x1, (x + y0 * Complex.I - breathingRoot j)⁻¹) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [smul_eq_mul]
                exact
                  (intervalIntegral.integral_const_mul
                    (a := x0) (b := x1)
                    (r := UFRF.ResidueDefinition.residueCandidateAt j)
                    (f := fun x : ℝ => (x + y0 * Complex.I - breathingRoot j)⁻¹))
  have htop_pf :
      (∫ x : ℝ in x0..x1, UFRF.ResidueDefinition.breathingFunction (x + y1 * Complex.I)) =
        ∑ j : ZMod CycleLen,
          UFRF.ResidueDefinition.residueCandidateAt j •
            (∫ x : ℝ in x0..x1, (x + y1 * Complex.I - breathingRoot j)⁻¹) := by
    calc
      (∫ x : ℝ in x0..x1, UFRF.ResidueDefinition.breathingFunction (x + y1 * Complex.I))
          =
            ∫ x : ℝ in x0..x1,
              ∑ j : ZMod CycleLen,
                UFRF.ResidueDefinition.residueCandidateAt j •
                  (x + y1 * Complex.I - breathingRoot j)⁻¹ := by
                    refine intervalIntegral.integral_congr ?_
                    intro x hx
                    simpa [smul_eq_mul] using
                      UFRF.ResidueDefinition.breathingFunction_eq_sum_residueCandidateAt_sub_inv
                        (z := x + y1 * Complex.I) (htop_den x hx)
      _ =
          ∑ j : ZMod CycleLen,
            ∫ x : ℝ in x0..x1,
              UFRF.ResidueDefinition.residueCandidateAt j •
                (x + y1 * Complex.I - breathingRoot j)⁻¹ := by
                  simpa using
                    (intervalIntegral.integral_finset_sum
                      (s := Finset.univ)
                      (f := fun j x =>
                        UFRF.ResidueDefinition.residueCandidateAt j •
                          (x + y1 * Complex.I - breathingRoot j)⁻¹)
                      (fun j hj => (htop_kernel_int j).smul
                        (UFRF.ResidueDefinition.residueCandidateAt j)))
      _ =
          ∑ j : ZMod CycleLen,
            UFRF.ResidueDefinition.residueCandidateAt j •
              (∫ x : ℝ in x0..x1, (x + y1 * Complex.I - breathingRoot j)⁻¹) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [smul_eq_mul]
                exact
                  (intervalIntegral.integral_const_mul
                    (a := x0) (b := x1)
                    (r := UFRF.ResidueDefinition.residueCandidateAt j)
                    (f := fun x : ℝ => (x + y1 * Complex.I - breathingRoot j)⁻¹))
  have hright_pf :
      (∫ y : ℝ in y0..y1, UFRF.ResidueDefinition.breathingFunction (x1 + y * Complex.I)) =
        ∑ j : ZMod CycleLen,
          UFRF.ResidueDefinition.residueCandidateAt j •
            (∫ y : ℝ in y0..y1, (x1 + y * Complex.I - breathingRoot j)⁻¹) := by
    calc
      (∫ y : ℝ in y0..y1, UFRF.ResidueDefinition.breathingFunction (x1 + y * Complex.I))
          =
            ∫ y : ℝ in y0..y1,
              ∑ j : ZMod CycleLen,
                UFRF.ResidueDefinition.residueCandidateAt j •
                  (x1 + y * Complex.I - breathingRoot j)⁻¹ := by
                    refine intervalIntegral.integral_congr ?_
                    intro y hy
                    simpa [smul_eq_mul] using
                      UFRF.ResidueDefinition.breathingFunction_eq_sum_residueCandidateAt_sub_inv
                        (z := x1 + y * Complex.I) (hright_den y hy)
      _ =
          ∑ j : ZMod CycleLen,
            ∫ y : ℝ in y0..y1,
              UFRF.ResidueDefinition.residueCandidateAt j •
                (x1 + y * Complex.I - breathingRoot j)⁻¹ := by
                  simpa using
                    (intervalIntegral.integral_finset_sum
                      (s := Finset.univ)
                      (f := fun j y =>
                        UFRF.ResidueDefinition.residueCandidateAt j •
                          (x1 + y * Complex.I - breathingRoot j)⁻¹)
                      (fun j hj => (hright_kernel_int j).smul
                        (UFRF.ResidueDefinition.residueCandidateAt j)))
      _ =
          ∑ j : ZMod CycleLen,
            UFRF.ResidueDefinition.residueCandidateAt j •
              (∫ y : ℝ in y0..y1, (x1 + y * Complex.I - breathingRoot j)⁻¹) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [smul_eq_mul]
                exact
                  (intervalIntegral.integral_const_mul
                    (a := y0) (b := y1)
                    (r := UFRF.ResidueDefinition.residueCandidateAt j)
                    (f := fun y : ℝ => (x1 + y * Complex.I - breathingRoot j)⁻¹))
  have hleft_pf :
      (∫ y : ℝ in y0..y1, UFRF.ResidueDefinition.breathingFunction (x0 + y * Complex.I)) =
        ∑ j : ZMod CycleLen,
          UFRF.ResidueDefinition.residueCandidateAt j •
            (∫ y : ℝ in y0..y1, (x0 + y * Complex.I - breathingRoot j)⁻¹) := by
    calc
      (∫ y : ℝ in y0..y1, UFRF.ResidueDefinition.breathingFunction (x0 + y * Complex.I))
          =
            ∫ y : ℝ in y0..y1,
              ∑ j : ZMod CycleLen,
                UFRF.ResidueDefinition.residueCandidateAt j •
                  (x0 + y * Complex.I - breathingRoot j)⁻¹ := by
                    refine intervalIntegral.integral_congr ?_
                    intro y hy
                    simpa [smul_eq_mul] using
                      UFRF.ResidueDefinition.breathingFunction_eq_sum_residueCandidateAt_sub_inv
                        (z := x0 + y * Complex.I) (hleft_den y hy)
      _ =
          ∑ j : ZMod CycleLen,
            ∫ y : ℝ in y0..y1,
              UFRF.ResidueDefinition.residueCandidateAt j •
                (x0 + y * Complex.I - breathingRoot j)⁻¹ := by
                  simpa using
                    (intervalIntegral.integral_finset_sum
                      (s := Finset.univ)
                      (f := fun j y =>
                        UFRF.ResidueDefinition.residueCandidateAt j •
                          (x0 + y * Complex.I - breathingRoot j)⁻¹)
                      (fun j hj => (hleft_kernel_int j).smul
                        (UFRF.ResidueDefinition.residueCandidateAt j)))
      _ =
          ∑ j : ZMod CycleLen,
            UFRF.ResidueDefinition.residueCandidateAt j •
              (∫ y : ℝ in y0..y1, (x0 + y * Complex.I - breathingRoot j)⁻¹) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [smul_eq_mul]
                exact
                  (intervalIntegral.integral_const_mul
                    (a := y0) (b := y1)
                    (r := UFRF.ResidueDefinition.residueCandidateAt j)
                    (f := fun y : ℝ => (x0 + y * Complex.I - breathingRoot j)⁻¹))
  calc
    boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction x0 x1 y0 y1
        =
          ((∑ j : ZMod CycleLen,
              UFRF.ResidueDefinition.residueCandidateAt j •
                (∫ x : ℝ in x0..x1, (x + y0 * Complex.I - breathingRoot j)⁻¹)) -
            (∑ j : ZMod CycleLen,
              UFRF.ResidueDefinition.residueCandidateAt j •
                (∫ x : ℝ in x0..x1, (x + y1 * Complex.I - breathingRoot j)⁻¹)) +
            Complex.I •
              (∑ j : ZMod CycleLen,
                UFRF.ResidueDefinition.residueCandidateAt j •
                  (∫ y : ℝ in y0..y1, (x1 + y * Complex.I - breathingRoot j)⁻¹)) -
            Complex.I •
              (∑ j : ZMod CycleLen,
                UFRF.ResidueDefinition.residueCandidateAt j •
                  (∫ y : ℝ in y0..y1, (x0 + y * Complex.I - breathingRoot j)⁻¹))) := by
            rw [boundaryRectIntegral, hbottom_pf, htop_pf, hright_pf, hleft_pf]
    _ =
        ∑ j : ZMod CycleLen,
          UFRF.ResidueDefinition.residueCandidateAt j •
            boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1 := by
              symm
              simp_rw [boundaryRectIntegral, smul_sub, smul_add, smul_smul, sub_eq_add_neg]
              have h1 :
                  ∑ x : ZMod CycleLen,
                    UFRF.ResidueDefinition.residueCandidateAt x •
                      ((∫ x_1 : ℝ in x0..x1, (x_1 + y0 * Complex.I + -breathingRoot x)⁻¹) +
                        -(∫ x_1 : ℝ in x0..x1, (x_1 + y1 * Complex.I + -breathingRoot x)⁻¹)) =
                    (∑ x : ZMod CycleLen,
                      UFRF.ResidueDefinition.residueCandidateAt x •
                        (∫ x_1 : ℝ in x0..x1, (x_1 + y0 * Complex.I + -breathingRoot x)⁻¹)) +
                    -(∑ x : ZMod CycleLen,
                      UFRF.ResidueDefinition.residueCandidateAt x •
                        (∫ x_1 : ℝ in x0..x1, (x_1 + y1 * Complex.I + -breathingRoot x)⁻¹)) := by
                  simp_rw [smul_add, smul_neg]
                  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
              have h2 :
                  ∑ x : ZMod CycleLen,
                    (UFRF.ResidueDefinition.residueCandidateAt x * Complex.I) •
                      (∫ y : ℝ in y0..y1, (x1 + y * Complex.I + -breathingRoot x)⁻¹) =
                    Complex.I •
                      (∑ x : ZMod CycleLen,
                        UFRF.ResidueDefinition.residueCandidateAt x •
                          (∫ y : ℝ in y0..y1, (x1 + y * Complex.I + -breathingRoot x)⁻¹)) := by
                  calc
                    ∑ x : ZMod CycleLen,
                        (UFRF.ResidueDefinition.residueCandidateAt x * Complex.I) •
                          (∫ y : ℝ in y0..y1, (x1 + y * Complex.I + -breathingRoot x)⁻¹)
                        =
                          ∑ x : ZMod CycleLen,
                            Complex.I •
                              (UFRF.ResidueDefinition.residueCandidateAt x •
                                (∫ y : ℝ in y0..y1, (x1 + y * Complex.I + -breathingRoot x)⁻¹)) := by
                                  simp_rw [smul_smul, mul_comm Complex.I]
                    _ =
                        Complex.I •
                          (∑ x : ZMod CycleLen,
                            UFRF.ResidueDefinition.residueCandidateAt x •
                              (∫ y : ℝ in y0..y1, (x1 + y * Complex.I + -breathingRoot x)⁻¹)) := by
                                rw [← Finset.smul_sum]
              have h3 :
                  ∑ x : ZMod CycleLen,
                    -((UFRF.ResidueDefinition.residueCandidateAt x * Complex.I) •
                      (∫ y : ℝ in y0..y1, (x0 + y * Complex.I + -breathingRoot x)⁻¹)) =
                    -(Complex.I •
                      (∑ x : ZMod CycleLen,
                        UFRF.ResidueDefinition.residueCandidateAt x •
                          (∫ y : ℝ in y0..y1, (x0 + y * Complex.I + -breathingRoot x)⁻¹))) := by
                  calc
                    ∑ x : ZMod CycleLen,
                        -((UFRF.ResidueDefinition.residueCandidateAt x * Complex.I) •
                          (∫ y : ℝ in y0..y1, (x0 + y * Complex.I + -breathingRoot x)⁻¹))
                        =
                          ∑ x : ZMod CycleLen,
                            -(Complex.I •
                              (UFRF.ResidueDefinition.residueCandidateAt x •
                                (∫ y : ℝ in y0..y1, (x0 + y * Complex.I + -breathingRoot x)⁻¹))) := by
                                  simp_rw [smul_smul, mul_comm Complex.I]
                    _ =
                        -(∑ x : ZMod CycleLen,
                          Complex.I •
                            (UFRF.ResidueDefinition.residueCandidateAt x •
                              (∫ y : ℝ in y0..y1, (x0 + y * Complex.I + -breathingRoot x)⁻¹))) := by
                                rw [Finset.sum_neg_distrib]
                    _ =
                        -(Complex.I •
                          (∑ x : ZMod CycleLen,
                            UFRF.ResidueDefinition.residueCandidateAt x •
                              (∫ y : ℝ in y0..y1, (x0 + y * Complex.I + -breathingRoot x)⁻¹))) := by
                                rw [← Finset.smul_sum]
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
              rw [h1, h2, h3]

/--
If every breathing root is either strictly inside a positively oriented
rectangle or completely outside its closed region, then the breathing-function
boundary integral around that rectangle is `2πi` times the sum of the explicit
residue candidates for exactly the enclosed roots.

This is the first honest finite-enclosure rectangle theorem for the specific
function `z ↦ 1 / (z^13 - 1)`.
-/
theorem boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_sum_residueCandidate_of_interior_or_outside
    {x0 x1 y0 y1 : ℝ}
    (hx : x0 < x1) (hy : y0 < y1)
    (hclass :
      ∀ k : ZMod CycleLen,
        breathingRoot k ∈ interior (closedRect x0 x1 y0 y1) ∨
          breathingRoot k ∉ closedRect x0 x1 y0 y1) :
    boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction x0 x1 y0 y1 =
      (2 * Real.pi * Complex.I) *
        Finset.sum (breathingRootsInInteriorRect x0 x1 y0 y1)
          UFRF.ResidueDefinition.residueCandidateAt := by
  classical
  let S : Finset (ZMod CycleLen) := breathingRootsInInteriorRect x0 x1 y0 y1
  have hx0_mem : x0 ∈ uIcc x0 x1 := by
    simp [hx.le]
  have hx1_mem : x1 ∈ uIcc x0 x1 := by
    simp [hx.le]
  have hy0_mem : y0 ∈ uIcc y0 y1 := by
    simp [hy.le]
  have hy1_mem : y1 ∈ uIcc y0 y1 := by
    simp [hy.le]
  have hbottom_den :
      ∀ x ∈ uIcc x0 x1,
        UFRF.ResidueDefinition.breathingDenominator (x + y0 * Complex.I) ≠ 0 := by
    intro x hxmem hzero
    obtain ⟨j, hj⟩ := exists_breathingRoot_of_breathingDenominator_eq_zero hzero
    rcases hclass j with hjin | hjout
    · exact bottom_edge_not_mem_interior_closedRect (x := x) hx hy (by simpa [hj] using hjin)
    · apply hjout
      rw [closedRect, ← hj]
      constructor
      · simpa using hxmem
      · simpa using hy0_mem
  have htop_den :
      ∀ x ∈ uIcc x0 x1,
        UFRF.ResidueDefinition.breathingDenominator (x + y1 * Complex.I) ≠ 0 := by
    intro x hxmem hzero
    obtain ⟨j, hj⟩ := exists_breathingRoot_of_breathingDenominator_eq_zero hzero
    rcases hclass j with hjin | hjout
    · exact top_edge_not_mem_interior_closedRect (x := x) hx hy (by simpa [hj] using hjin)
    · apply hjout
      rw [closedRect, ← hj]
      constructor
      · simpa using hxmem
      · simpa using hy1_mem
  have hright_den :
      ∀ y ∈ uIcc y0 y1,
        UFRF.ResidueDefinition.breathingDenominator (x1 + y * Complex.I) ≠ 0 := by
    intro y hymem hzero
    obtain ⟨j, hj⟩ := exists_breathingRoot_of_breathingDenominator_eq_zero hzero
    rcases hclass j with hjin | hjout
    · exact right_edge_not_mem_interior_closedRect (y := y) hx hy (by simpa [hj] using hjin)
    · apply hjout
      rw [closedRect, ← hj]
      constructor
      · simpa using hx1_mem
      · simpa using hymem
  have hleft_den :
      ∀ y ∈ uIcc y0 y1,
        UFRF.ResidueDefinition.breathingDenominator (x0 + y * Complex.I) ≠ 0 := by
    intro y hymem hzero
    obtain ⟨j, hj⟩ := exists_breathingRoot_of_breathingDenominator_eq_zero hzero
    rcases hclass j with hjin | hjout
    · exact left_edge_not_mem_interior_closedRect (y := y) hx hy (by simpa [hj] using hjin)
    · apply hjout
      rw [closedRect, ← hj]
      constructor
      · simpa using hx0_mem
      · simpa using hymem
  have hsum :
      boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction x0 x1 y0 y1 =
        ∑ j : ZMod CycleLen,
          UFRF.ResidueDefinition.residueCandidateAt j •
            boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1 :=
    boundaryRectIntegral_breathingFunction_eq_sum_residueCandidateAt_kernel_of_edge_den_nonzero
      hbottom_den htop_den hright_den hleft_den
  have hkernel_inside :
      ∀ j ∈ S,
        boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1 =
          2 * Real.pi * Complex.I := by
    intro j hj
    have hjin : breathingRoot j ∈ interior (closedRect x0 x1 y0 y1) := by
      simpa [S] using hj
    exact boundaryRectIntegral_sub_inv_eq_two_pi_I_of_mem_interior_closedRect hx hy hjin
  have hkernel_outside :
      ∀ j ∈ Sᶜ,
        boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1 = 0 := by
    intro j hj
    have hjnotS : j ∉ S := Finset.mem_compl.mp hj
    have hjout : breathingRoot j ∉ closedRect x0 x1 y0 y1 := by
      rcases hclass j with hjin | hjout
      · exact False.elim (hjnotS (by simpa [S] using hjin))
      · exact hjout
    exact boundaryRectIntegral_sub_inv_eq_zero_of_not_mem_closedRect hjout
  have hinside :
      Finset.sum S (fun j =>
        UFRF.ResidueDefinition.residueCandidateAt j •
          boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1) =
        (2 * Real.pi * Complex.I) *
          Finset.sum S UFRF.ResidueDefinition.residueCandidateAt := by
    calc
      Finset.sum S (fun j =>
          UFRF.ResidueDefinition.residueCandidateAt j •
            boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1)
          =
            Finset.sum S (fun j =>
              UFRF.ResidueDefinition.residueCandidateAt j • (2 * Real.pi * Complex.I)) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [hkernel_inside j hj]
      _ =
          Finset.sum S (fun j =>
            UFRF.ResidueDefinition.residueCandidateAt j * (2 * Real.pi * Complex.I)) := by
              simp_rw [smul_eq_mul]
      _ =
          Finset.sum S (fun j =>
            (2 * Real.pi * Complex.I) * UFRF.ResidueDefinition.residueCandidateAt j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ =
          (2 * Real.pi * Complex.I) *
            Finset.sum S UFRF.ResidueDefinition.residueCandidateAt := by
              rw [Finset.mul_sum]
  have houtside_zero :
      Finset.sum Sᶜ (fun j =>
        UFRF.ResidueDefinition.residueCandidateAt j •
          boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    simp [hkernel_outside j hj]
  calc
    boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction x0 x1 y0 y1
        =
          ∑ j : ZMod CycleLen,
            UFRF.ResidueDefinition.residueCandidateAt j •
              boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1 := hsum
    _ =
        Finset.sum S (fun j =>
          UFRF.ResidueDefinition.residueCandidateAt j •
            boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1) +
        Finset.sum Sᶜ (fun j =>
          UFRF.ResidueDefinition.residueCandidateAt j •
            boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1) := by
              rw [← S.sum_add_sum_compl (fun j : ZMod CycleLen =>
                UFRF.ResidueDefinition.residueCandidateAt j •
                  boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1)]
    _ =
        Finset.sum S (fun j =>
          UFRF.ResidueDefinition.residueCandidateAt j •
            boundaryRectIntegral (fun z : ℂ => (z - breathingRoot j)⁻¹) x0 x1 y0 y1) := by
              rw [houtside_zero, add_zero]
    _ =
        (2 * Real.pi * Complex.I) *
          Finset.sum S UFRF.ResidueDefinition.residueCandidateAt := hinside
    _ =
        (2 * Real.pi * Complex.I) *
          Finset.sum (breathingRootsInInteriorRect x0 x1 y0 y1)
            UFRF.ResidueDefinition.residueCandidateAt := by
              simp [S]

private theorem breathingRoot_interior_or_outside_of_no_boundary_roots
    {x0 x1 y0 y1 : ℝ}
    (hboundary :
      ∀ k : ZMod CycleLen, breathingRoot k ∉ frontier (closedRect x0 x1 y0 y1)) :
    ∀ k : ZMod CycleLen,
      breathingRoot k ∈ interior (closedRect x0 x1 y0 y1) ∨
        breathingRoot k ∉ closedRect x0 x1 y0 y1 := by
  intro k
  by_cases hk : breathingRoot k ∈ closedRect x0 x1 y0 y1
  · exact Or.inl ((mem_interior_iff_notMem_frontier hk).2 (hboundary k))
  · exact Or.inr hk

/--
If a positively oriented rectangle has no breathing roots on its boundary,
then the breathing-function boundary integral around that rectangle is `2πi`
times the sum of the explicit residue candidates for exactly the breathing
roots in its interior.

This packages the finite-enclosure rectangle theorem under the natural
boundary-clean geometric hypothesis, without promoting the result to a generic
rectangle residue API.
-/
theorem boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_sum_residueCandidate_of_no_boundary_roots
    {x0 x1 y0 y1 : ℝ}
    (hx : x0 < x1) (hy : y0 < y1)
    (hboundary :
      ∀ k : ZMod CycleLen, breathingRoot k ∉ frontier (closedRect x0 x1 y0 y1)) :
    boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction x0 x1 y0 y1 =
      (2 * Real.pi * Complex.I) *
        Finset.sum (breathingRootsInInteriorRect x0 x1 y0 y1)
          UFRF.ResidueDefinition.residueCandidateAt := by
  exact
    boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_sum_residueCandidate_of_interior_or_outside
      hx hy (breathingRoot_interior_or_outside_of_no_boundary_roots hboundary)

/--
A boundary-clean outer rectangle has the same breathing-function boundary
integral as the sum of the canonical quarter-`infsep` local square boundary
integrals around exactly the enclosed breathing roots.

This packages the outer-rectangle to local-squares comparison theorem without
introducing any generic multi-boundary residue API.
-/
theorem boundaryRectIntegral_breathingFunction_eq_sum_quarter_infsep_centeredSquareIntegrals_of_no_boundary_roots
    {x0 x1 y0 y1 : ℝ}
    (hx : x0 < x1) (hy : y0 < y1)
    (hboundary :
      ∀ k : ZMod CycleLen, breathingRoot k ∉ frontier (closedRect x0 x1 y0 y1)) :
    boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction x0 x1 y0 y1 =
      Finset.sum (breathingRootsInInteriorRect x0 x1 y0 y1) (fun k =>
        boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction
          ((breathingRoot k).re - ((Set.range breathingRoot : Set ℂ).infsep / 4))
          ((breathingRoot k).re + ((Set.range breathingRoot : Set ℂ).infsep / 4))
          ((breathingRoot k).im - ((Set.range breathingRoot : Set ℂ).infsep / 4))
          ((breathingRoot k).im + ((Set.range breathingRoot : Set ℂ).infsep / 4))) := by
  rw [boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_sum_residueCandidate_of_no_boundary_roots
    hx hy hboundary]
  rw [sum_boundaryRectIntegral_breathingFunction_quarter_infsep_centeredSquare_eq_two_pi_I_mul_sum_residueCandidate
    (S := breathingRootsInInteriorRect x0 x1 y0 y1)]

/--
If every breathing root lies strictly inside a positively oriented rectangle,
then the breathing-function boundary integral around that rectangle is zero.

This is the all-roots cancellation corollary of the boundary-clean rectangle
residue formula and the global identity
`∑ k, residueCandidateAt k = 0`.
-/
theorem boundaryRectIntegral_breathingFunction_eq_zero_of_all_breathingRoots_mem_interior_closedRect
    {x0 x1 y0 y1 : ℝ}
    (hx : x0 < x1) (hy : y0 < y1)
    (hinside :
      ∀ k : ZMod CycleLen,
        breathingRoot k ∈ interior (closedRect x0 x1 y0 y1)) :
    boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction x0 x1 y0 y1 = 0 := by
  have hboundary :
      ∀ k : ZMod CycleLen, breathingRoot k ∉ frontier (closedRect x0 x1 y0 y1) := by
    intro k
    exact (mem_interior_iff_notMem_frontier (interior_subset (hinside k))).1 (hinside k)
  have hS : breathingRootsInInteriorRect x0 x1 y0 y1 = Finset.univ := by
    ext k
    simp [hinside k]
  rw [boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_sum_residueCandidate_of_no_boundary_roots
    hx hy hboundary, hS, UFRF.ResidueDefinition.total_residue_candidate_zero, mul_zero]

/--
Every breathing root lies strictly inside the centered square `[-R, R] × [-R, R]`
whenever `R > 1`.

This is the variable-radius rectangle analogue of the existing outer-circle
regime `R > 1`.
-/
theorem breathingRoot_mem_interior_closedRect_centeredSquare_of_one_lt
    {R : ℝ} (hR : 1 < R) (k : ZMod CycleLen) :
    breathingRoot k ∈ interior (closedRect (-R) R (-R) R) := by
  have hside : -R < R := by linarith
  have hre : (breathingRoot k).re ∈ Set.Ioo (-R) R := by
    have hre' : |(breathingRoot k).re| < R := by
      calc
        |(breathingRoot k).re| ≤ ‖breathingRoot k‖ := Complex.abs_re_le_norm _
        _ = 1 := norm_breathingRoot_eq_one k
        _ < R := hR
    exact abs_lt.mp hre'
  have him : (breathingRoot k).im ∈ Set.Ioo (-R) R := by
    have him' : |(breathingRoot k).im| < R := by
      calc
        |(breathingRoot k).im| ≤ ‖breathingRoot k‖ := Complex.abs_im_le_norm _
        _ = 1 := norm_breathingRoot_eq_one k
        _ < R := hR
    exact abs_lt.mp him'
  simpa [closedRect, interior_reProdIm, Set.uIcc_of_le hside.le, interior_Icc, mem_reProdIm]
    using And.intro hre him

/--
For every variable radius `R > 1`, the boundary integral of `breathingFunction`
around the centered square `[-R, R] × [-R, R]` is zero.

This keeps the large-rectangle convenience theorem parameterized by `R`,
rather than hardcoding a single enclosing box.
-/
theorem boundaryRectIntegral_breathingFunction_eq_zero_of_one_lt_centeredSquare
    {R : ℝ} (hR : 1 < R) :
    boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction (-R) R (-R) R = 0 := by
  have hside : -R < R := by linarith
  exact
    boundaryRectIntegral_breathingFunction_eq_zero_of_all_breathingRoots_mem_interior_closedRect
      hside hside (breathingRoot_mem_interior_closedRect_centeredSquare_of_one_lt hR)

/--
If a positively oriented rectangle strictly contains the unit square
`[-1, 1] × [-1, 1]`, then every breathing root lies in its interior.

This is the asymmetric rectangle version of the centered-square `R > 1`
enclosure theorem.
-/
theorem breathingRoot_mem_interior_closedRect_of_encloses_unitSquare
    {x0 x1 y0 y1 : ℝ}
    (hx0 : x0 < -1) (hx1 : 1 < x1)
    (hy0 : y0 < -1) (hy1 : 1 < y1)
    (k : ZMod CycleLen) :
    breathingRoot k ∈ interior (closedRect x0 x1 y0 y1) := by
  have hx : x0 < x1 := by linarith
  have hy : y0 < y1 := by linarith
  have hre_mem : (breathingRoot k).re ∈ Set.Ioo x0 x1 := by
    have hre_abs : |(breathingRoot k).re| ≤ 1 := by
      calc
        |(breathingRoot k).re| ≤ ‖breathingRoot k‖ := Complex.abs_re_le_norm _
        _ = 1 := norm_breathingRoot_eq_one k
    rcases abs_le.mp hre_abs with ⟨hre_lo, hre_hi⟩
    exact ⟨by linarith, by linarith⟩
  have him_mem : (breathingRoot k).im ∈ Set.Ioo y0 y1 := by
    have him_abs : |(breathingRoot k).im| ≤ 1 := by
      calc
        |(breathingRoot k).im| ≤ ‖breathingRoot k‖ := Complex.abs_im_le_norm _
        _ = 1 := norm_breathingRoot_eq_one k
    rcases abs_le.mp him_abs with ⟨him_lo, him_hi⟩
    exact ⟨by linarith, by linarith⟩
  simpa [closedRect, interior_reProdIm, Set.uIcc_of_le hx.le, Set.uIcc_of_le hy.le,
    interior_Icc, mem_reProdIm] using And.intro hre_mem him_mem

/--
If a positively oriented rectangle strictly contains the unit square
`[-1, 1] × [-1, 1]`, then the boundary integral of `breathingFunction` around
that rectangle is zero.

This packages the current all-roots-interior rectangle theorem as the smallest
asymmetric large-rectangle convenience corollary.
-/
theorem boundaryRectIntegral_breathingFunction_eq_zero_of_encloses_unitSquare
    {x0 x1 y0 y1 : ℝ}
    (hx0 : x0 < -1) (hx1 : 1 < x1)
    (hy0 : y0 < -1) (hy1 : 1 < y1) :
    boundaryRectIntegral UFRF.ResidueDefinition.breathingFunction x0 x1 y0 y1 = 0 := by
  have hx : x0 < x1 := by linarith
  have hy : y0 < y1 := by linarith
  exact
    boundaryRectIntegral_breathingFunction_eq_zero_of_all_breathingRoots_mem_interior_closedRect
      hx hy (breathingRoot_mem_interior_closedRect_of_encloses_unitSquare hx0 hx1 hy0 hy1)

/--
If the breathing denominator never vanishes on a closed rectangle, then the
boundary integral of the breathing function around that rectangle is zero.

This is the first noncircular outer-boundary theorem in the residue pipeline.
It is still specific to `z ↦ 1 / (z^13 - 1)` and relies only on Mathlib's
rectangle-boundary Cauchy-Goursat theorem.
-/
theorem integral_boundary_rect_breathingFunction_eq_zero_of_breathingDenominator_ne_zero
    (z w : ℂ)
    (hden :
      ∀ x ∈ (uIcc z.re w.re ×ℂ uIcc z.im w.im),
        UFRF.ResidueDefinition.breathingDenominator x ≠ 0) :
    (∫ x : ℝ in z.re..w.re, UFRF.ResidueDefinition.breathingFunction (x + z.im * Complex.I)) -
      (∫ x : ℝ in z.re..w.re, UFRF.ResidueDefinition.breathingFunction (x + w.im * Complex.I)) +
      Complex.I •
        (∫ y : ℝ in z.im..w.im,
          UFRF.ResidueDefinition.breathingFunction (w.re + y * Complex.I)) -
      Complex.I •
        (∫ y : ℝ in z.im..w.im,
          UFRF.ResidueDefinition.breathingFunction (z.re + y * Complex.I)) = 0 := by
  let rect : Set ℂ := uIcc z.re w.re ×ℂ uIcc z.im w.im
  let openRect : Set ℂ :=
    Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)
  have hcontDen : ContinuousOn UFRF.ResidueDefinition.breathingDenominator rect := by
    intro x hx
    change ContinuousWithinAt (fun u : ℂ => u ^ UFRF.ResidueDefinition.CycleLen - (1 : ℂ)) rect x
    fun_prop
  have hcont :
      ContinuousOn UFRF.ResidueDefinition.breathingFunction rect := by
    simpa [rect, UFRF.ResidueDefinition.breathingFunction] using
      (continuousOn_const.div hcontDen hden)
  have hdiffDen : DifferentiableOn ℂ UFRF.ResidueDefinition.breathingDenominator openRect := by
    intro x hx
    change DifferentiableWithinAt ℂ
      (fun u : ℂ => u ^ UFRF.ResidueDefinition.CycleLen - (1 : ℂ)) openRect x
    fun_prop
  have hconst : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) openRect := by
    intro x hx
    exact (differentiableAt_const (c := (1 : ℂ))).differentiableWithinAt
  have hden_open :
      ∀ x ∈ openRect, UFRF.ResidueDefinition.breathingDenominator x ≠ 0 := by
    intro x hx
    apply hden x
    have hxint : x ∈ interior rect := by
      simpa [rect, openRect, interior_reProdIm, uIcc, interior_Icc] using hx
    exact interior_subset hxint
  have hdiff :
      DifferentiableOn ℂ UFRF.ResidueDefinition.breathingFunction openRect := by
    simpa [openRect, UFRF.ResidueDefinition.breathingFunction] using
      hconst.div hdiffDen hden_open
  exact Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    UFRF.ResidueDefinition.breathingFunction z w hcont hdiff

/--
If a closed rectangle contains no breathing root, then the boundary integral
of the breathing function around that rectangle is zero.

This packages the rectangle theorem above in the breathing-root language, using
the proved classification of every zero of `z^13 - 1` as a breathing root.
-/
theorem integral_boundary_rect_breathingFunction_eq_zero_of_no_breathingRoots
    (z w : ℂ)
    (hroot :
      ∀ k : ZMod CycleLen,
        breathingRoot k ∉ (uIcc z.re w.re ×ℂ uIcc z.im w.im)) :
    (∫ x : ℝ in z.re..w.re, UFRF.ResidueDefinition.breathingFunction (x + z.im * Complex.I)) -
      (∫ x : ℝ in z.re..w.re, UFRF.ResidueDefinition.breathingFunction (x + w.im * Complex.I)) +
      Complex.I •
        (∫ y : ℝ in z.im..w.im,
          UFRF.ResidueDefinition.breathingFunction (w.re + y * Complex.I)) -
      Complex.I •
        (∫ y : ℝ in z.im..w.im,
          UFRF.ResidueDefinition.breathingFunction (z.re + y * Complex.I)) = 0 := by
  apply integral_boundary_rect_breathingFunction_eq_zero_of_breathingDenominator_ne_zero z w
  intro x hx hzero
  obtain ⟨k, hkx⟩ := exists_breathingRoot_of_breathingDenominator_eq_zero hzero
  exact hroot k (hkx ▸ hx)

end UFRF.CircleIntegralBreathing
