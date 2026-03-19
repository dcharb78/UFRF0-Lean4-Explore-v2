import UFRF.Padic
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# UFRF.InverseLimit

**The One Ring: The Inverse Limit Construction**

The "One Ring" ℤ_[p] is not just a definition — it is the UNIQUE object
that unifies all the finite layers. It is the Inverse Limit of the tower.

ℤ_[p] ≅ lim ← ℤ/pⁿℤ

This file establishes the defining universal property of the p-adic integers
as the inverse limit of the finite modular rings, ensuring that the 13-lattice
spiral structure remains consistent at every continuous depth.

## The Projection Law's Other Half

The forward direction (`padic_is_coherent`): given an intrinsic value
(a p-adic integer), you can project it to any scale and get a consistent
observation. This is ln O = ln O* + correction.

The reverse direction (`padic_is_inverse_limit`): given compatible
observations at ALL scales, you can reconstruct the unique intrinsic value
they came from. This is the INVERSE of the projection law.

Together: intrinsic and measured are connected by an isomorphism when
you have access to all scales simultaneously.

## Status
- `padic_is_coherent`: ✅ PROVEN
- `padic_is_inverse_limit`: ✅ PROVEN (via Mathlib's PadicInt API)
-/

section InverseLimit

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- Helper: Projection from level n+1 to n. -/
def cast_down (n : ℕ) : ZMod (p ^ (n + 1)) →+* ZMod (p ^ n) :=
  ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))

/--
**The coherence predicate.**
A sequence is coherent if xₙ₊₁ projects to xₙ. This defines the continuity
of the spiral geometry.
-/
def IsCoherent (seq : (n : ℕ) → ZMod (p ^ n)) : Prop :=
  ∀ n, cast_down p n (seq (n + 1)) = seq n

/--
**Theorem: The p-adic Integers Form Coherent Sequences**
Every p-adic integer naturally generates a coherent sequence down the finite
modular rings. This is the structural proof that the 13-lattice is preserved.

✅ PROVEN
-/
theorem padic_is_coherent (x : ℤ_[p]) : IsCoherent p (fun n => PadicInt.toZModPow n x) := by
  intro n
  dsimp [cast_down]
  rw [PadicInt.cast_toZModPow n (n+1) (Nat.le_succ n)]

/--
**Theorem: Universal Property of the Spiral (Inverse Limit)**
Any coherent sequence of finite modular rings (a spiral) uniquely defines
a single p-adic integer. This is the core guarantee of UFRF's scale-invariance.

The proof uses Mathlib's `PadicInt.ofIntSeq` to construct the p-adic integer
from the coherent sequence's integer lifts, then `toZModPow_ofIntSeq_of_pow_dvd_sub`
to verify reductions, and `ext_of_toZModPow` for uniqueness.

✅ PROVEN
-/
theorem padic_is_inverse_limit (seq : (n : ℕ) → ZMod (p ^ n)) (h_coh : IsCoherent p seq) :
    ∃! (x : ℤ_[p]), ∀ n, PadicInt.toZModPow n x = seq n := by
  -- Build integer-valued sequence from ZMod.val
  -- f(n) = val(seq(n)) : ℤ
  let f : ℕ → ℤ := fun n => (seq n).val
  -- Coherence implies p^i divides f(i+1) - f(i)
  -- Because: coherence says (seq(i+1) : ZMod(p^i)) = seq(i),
  -- which means val(seq(i+1)) ≡ val(seq(i)) mod p^i
  have hdvd : ∀ i, (p : ℤ) ^ i ∣ f (i + 1) - f i := by
    intro i
    have hc := h_coh i
    simp only [cast_down, ZMod.castHom_apply] at hc
    -- Convert to ZMod divisibility criterion
    suffices h : ((f (i + 1) - f i : ℤ) : ZMod (p ^ i)) = 0 by
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    dsimp only [f]
    push_cast
    simp only [ZMod.natCast_zmod_val]
    rw [show ((seq (i + 1)).val : ZMod (p ^ i)) =
      ZMod.cast (seq (i + 1)) from ZMod.natCast_val _]
    rw [hc, sub_self]
  -- Construct the p-adic integer
  let x := PadicInt.ofIntSeq f (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub f p hdvd)
  -- Show it reduces correctly at every level
  have hx : ∀ n, PadicInt.toZModPow n x = seq n := by
    intro n
    have := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub f p hdvd n
    -- this : toZModPow n x = f n (equality in ZMod(p^n))
    -- f n = ↑val(seq n) : ℤ, so RHS = Int.cast(val(seq n))
    -- which simplifies to seq n by cast roundtrip
    simp only [f, Int.cast_natCast, ZMod.natCast_zmod_val] at this
    exact this
  -- Package: witness + property + uniqueness
  exact ⟨x, hx, fun y hy => PadicInt.ext_of_toZModPow.mp (fun n => by rw [hy n, hx n])⟩

end InverseLimit
