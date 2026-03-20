import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.MetricSpace.Infsep
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

end UFRF.CircleIntegralBreathing
