import UFRF.CollatzSolenoid
import UFRF.Recursion
import Mathlib.Tactic

namespace UFRF.ConcurrentScales

open UFRF.CollatzWindow

/-!
# CollatzConcurrentScales: The Unsafe Residue Resolution Theorem

## Background

At each tower level k (modulus 13·2^k), the contraction certificate uses
v₂(3r+1) for the residue representative r. For "unsafe" residues where
2^k ∣ 3r+1, the representative's v₂ may overcount the actual v₂ for
integers n ≡ r (mod 13·2^k).

## The Key Insight (user, 2026-04-01)

"k=13 exists from 0-1. then 0-1 becomes nodes of nodes. 1-13. then 1-13
become nodes of nodes. Trinity is root. Every prime starts its own trinity."

This is not a gap to patch — it IS the concurrent recursive structure.
The unsafe residue at level k carries ambiguity: v₂(3n+1) ≥ k is known,
but the exact value depends on higher bits. Passing to level k+1 resolves
exactly ONE bit. The two preimages of r in ZMod(13·2^(k+1)) split as:
one safe (v₂ resolved to k), one unsafe (v₂ ≥ k+1) — same pattern, next scale.

## The Coupling Constant 39 = 3·13

The split is driven by the parity of 39 = 3·13 (Trinity root × cycle length).
Since 39 is odd, exactly one of {m, m+39} is even for any m, giving the
clean 50/50 split between safe and unsafe children.

## Theorem Chain

```
unsafe_splits              (core: every unsafe r has exactly one safe child)
  ↓
safe_child_exists          (existential form)
  ↓
integer_resolves_at_v2     (every n is safe at its native level k=v₂(3n+1))
  ↓
collatz_convergence        (full convergence — OPEN, requires general W(k) bound)
```
-/

/-! ## Section 1: Definitions -/

/-- A residue r is **unsafe** at level k when 2^k divides 3r+1.
    The contraction certificate may overcount v₂ for integers n ≡ r (mod 13·2^k),
    since v₂(3r+1) ≥ k but actual v₂(3n+1) may equal k (not higher). -/
def isUnsafe (r k : ℕ) : Prop := 2 ^ k ∣ 3 * r + 1

/-- The upper lift of r from level k to level k+1.
    ZMod(13·2^(k+1)) → ZMod(13·2^k) has two preimages for each odd residue:
    r itself (lower lift) and r + 13·2^k (upper lift). -/
def upperLift (r k : ℕ) : ℕ := r + 13 * 2 ^ k

/-! ## Section 2: The Trinity Coupling Constant 39 = 3·13 -/

/-- 39 = 3·13: Collatz coefficient (Trinity root) × UFRF cycle length.
    This is the bridge constant between consecutive tower levels. -/
theorem trinity_coupling : (3 : ℕ) * 13 = 39 := by norm_num

/-- 39 is odd — the single fact that forces the splitting theorem. -/
theorem coupling_is_odd : ¬ 2 ∣ (39 : ℕ) := by decide

/-- Key arithmetic: 3·(r + 13·2^k) + 1 = (3r+1) + 39·2^k. -/
lemma upper_lift_val (r k : ℕ) :
    3 * upperLift r k + 1 = 3 * r + 1 + 39 * 2 ^ k := by
  simp [upperLift]; ring

/-! ## Section 3: The Splitting Theorem -/

/-- **Concurrent Scale Splitting Theorem**

    If r is unsafe at level k (i.e., 2^k ∣ 3r+1), then at level k+1:
    - lower lift r is unsafe at k+1  ↔  upper lift is SAFE at k+1
    - lower lift r is SAFE at k+1   ↔  upper lift is unsafe at k+1

    Exactly one lift is safe, exactly one is unsafe.

    Proof: Write 3r+1 = 2^k·m. Then 3·(r+13·2^k)+1 = 2^k·(m+39).
    - 2^(k+1) ∣ 2^k·m   ↔   2 ∣ m         (cancel 2^k)
    - 2^(k+1) ∣ 2^k·(m+39) ↔  2 ∣ m+39    (cancel 2^k)
    - 2∣m ↔ ¬(2∣m+39) because 39 is odd. ∎ -/
theorem unsafe_splits (k r : ℕ) (hr : isUnsafe r k) :
    isUnsafe r (k + 1) ↔ ¬ isUnsafe (upperLift r k) (k + 1) := by
  simp only [isUnsafe, upper_lift_val]
  obtain ⟨m, hm⟩ := hr
  -- hm : 3 * r + 1 = 2 ^ k * m
  have hpow : (0 : ℕ) < 2 ^ k := pow_pos (by norm_num) k
  constructor
  · -- Forward: 2^(k+1) ∣ 3r+1  →  ¬(2^(k+1) ∣ 3r+1+39·2^k)
    rintro ⟨q, hq⟩ ⟨p, hp⟩
    -- hq : 3*r+1 = 2^(k+1) * q
    -- hp : 3*r+1 + 39*2^k = 2^(k+1) * p
    -- Cancel 2^k: m = 2q and m+39 = 2p → 39 is even: contradiction
    have hm_even : m = 2 * q := by
      apply Nat.eq_of_mul_eq_mul_left hpow
      calc 2 ^ k * m = 3 * r + 1        := hm.symm
        _ = 2 ^ (k + 1) * q             := hq
        _ = 2 ^ k * (2 * q)             := by ring
    have hm39_even : m + 39 = 2 * p := by
      apply Nat.eq_of_mul_eq_mul_left hpow
      calc 2 ^ k * (m + 39)
          = 2 ^ k * m + 39 * 2 ^ k      := by ring
        _ = (3 * r + 1) + 39 * 2 ^ k   := by rw [← hm]
        _ = 2 ^ (k + 1) * p             := hp
        _ = 2 ^ k * (2 * p)             := by ring
    -- m = 2q and m+39 = 2p → 39 = 2(p-q): impossible since 39 is odd
    omega
  · -- Backward: ¬(2^(k+1) ∣ 3r+1+39·2^k)  →  2^(k+1) ∣ 3r+1
    intro h
    -- Step 1: 2 ∤ (m+39) — extract from h
    have hm39_not_even : ¬ 2 ∣ m + 39 := by
      intro ⟨p, hp⟩
      apply h
      exact ⟨p, by calc 3 * r + 1 + 39 * 2 ^ k
                        = 2 ^ k * m + 39 * 2 ^ k    := by rw [← hm]
                      _ = 2 ^ k * (m + 39)           := by ring
                      _ = 2 ^ k * (2 * p)            := by rw [hp]
                      _ = 2 ^ (k + 1) * p            := by ring⟩
    -- Step 2: since 39 is odd and m+39 is odd, m must be even
    have hm_even : 2 ∣ m := by
      rcases Nat.even_or_odd m with ⟨q, hq⟩ | ⟨q, hq⟩
      · -- Even case: m = q + q
        exact ⟨q, by omega⟩
      · -- Odd case: m = 2*q+1 → m+39 = 2*(q+20): contradicts hm39_not_even
        exfalso; apply hm39_not_even; exact ⟨q + 20, by omega⟩
    -- Step 3: construct the witness at level k+1
    obtain ⟨q, hq⟩ := hm_even
    exact ⟨q, by calc 3 * r + 1
                    = 2 ^ k * m        := hm
                  _ = 2 ^ k * (2 * q) := by rw [hq]
                  _ = 2 ^ (k + 1) * q := by ring⟩

/-! ## Section 4: Consequences -/

/-- Every unsafe residue at level k has at least one safe child at k+1. -/
theorem safe_child_exists (k r : ℕ) (hr : isUnsafe r k) :
    ¬ isUnsafe r (k + 1) ∨ ¬ isUnsafe (upperLift r k) (k + 1) := by
  rcases Classical.em (isUnsafe r (k + 1)) with h | h
  · exact Or.inr ((unsafe_splits k r hr).mp h)
  · exact Or.inl h

/-- The two lifts are distinct (differ by 13·2^k > 0). -/
theorem lifts_distinct (k r : ℕ) : r ≠ upperLift r k := by
  simp only [upperLift, ne_eq]
  intro heq
  have hpos : 0 < 13 * 2 ^ k := by positivity
  linarith

/-- Full concurrent resolution: exactly one safe child, exactly one unsafe child.
    (Variable renamed from `unsafe` to `unsf` since `unsafe` is a Lean keyword.) -/
theorem concurrent_resolution (k r : ℕ) (hr : isUnsafe r k) :
    ∃ (safe unsf : ℕ),
      (safe = r ∨ safe = upperLift r k) ∧
      (unsf = r ∨ unsf = upperLift r k) ∧
      safe ≠ unsf ∧
      ¬ isUnsafe safe (k + 1) ∧
      isUnsafe unsf (k + 1) := by
  rcases Classical.em (isUnsafe r (k + 1)) with h | h
  · -- r is unsafe ⟹ upperLift is safe
    exact ⟨upperLift r k, r,
      Or.inr rfl,
      Or.inl rfl,
      (lifts_distinct k r).symm,
      (unsafe_splits k r hr).mp h,
      h⟩
  · -- r is safe ⟹ upperLift is unsafe
    refine ⟨r, upperLift r k, Or.inl rfl, Or.inr rfl, lifts_distinct k r, h, ?_⟩
    exact Classical.byContradiction (fun h2 => h ((unsafe_splits k r hr).mpr h2))

/-! ## Section 5: Connection to the Recursive Scale Structure -/

/-- The splitting theorem is the Collatz instance of
    `Recursion.zero_point_isomorphism`: every "zero point" (unsafe residue)
    at scale k resolves into the full breathing cycle at scale k+1.

    Compare: `Recursion.bridge_to_seed` (positions 10,11,12 at scale S
    become seeds 0,1,2 at scale S+1) — the unsafe residue IS the bridge node.

    The two lifts are the two preimages under the natural projection
    ZMod(13·2^(k+1)) → ZMod(13·2^k). One resolves (safe child), one descends. -/
theorem splits_are_scale_descent (k r : ℕ) (hr : isUnsafe r k) :
    (¬ isUnsafe r (k + 1) → isUnsafe (upperLift r k) (k + 1)) ∧
    (¬ isUnsafe (upperLift r k) (k + 1) → isUnsafe r (k + 1)) := by
  exact ⟨
    fun h => Classical.byContradiction (fun h2 => h ((unsafe_splits k r hr).mpr h2)),
    fun h => (unsafe_splits k r hr).mpr h⟩

/-! ## Section 6: The Native Scale Resolution -/

/-- **Bridge Lemma**: v2Fuel computes the exact 2-adic valuation when fuel is adequate.
    Specifically: for n > 0 with n < 2^fuel, 2^(v2Fuel fuel n + 1) does NOT divide n.
    Proof: by induction on fuel, branching on parity of n. -/
private lemma v2Fuel_not_upper_dvd (fuel n : ℕ) (hn : 0 < n) (hfuel : n < 2 ^ fuel) :
    ¬ 2 ^ (v2Fuel fuel n + 1) ∣ n := by
  induction fuel generalizing n with
  | zero => simp at hfuel; omega
  | succ f ih =>
    by_cases heven : n % 2 = 0
    · -- n is even: v2Fuel (f+1) n = 1 + v2Fuel f (n/2)
      have hv : v2Fuel (f + 1) n = 1 + v2Fuel f (n / 2) := by
        cases n with
        | zero => omega
        | succ m =>
          have : v2Fuel (f + 1) (m + 1) =
              if (m + 1) % 2 = 0 then 1 + v2Fuel f ((m + 1) / 2) else 0 := rfl
          rw [this, if_pos heven]
      rw [hv]
      have hpos2 : 0 < n / 2 := by omega
      have hlt2 : n / 2 < 2 ^ f := by rw [pow_succ] at hfuel; omega
      intro hdvd
      apply ih (n / 2) hpos2 hlt2
      -- hdvd : 2^(1 + v2Fuel f (n/2) + 1) ∣ n
      -- goal : 2^(v2Fuel f (n/2) + 1) ∣ n/2
      obtain ⟨q, hq⟩ := hdvd
      exact ⟨q, Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
        (calc 2 * (n / 2) = n := by omega
          _ = 2 ^ (1 + v2Fuel f (n / 2) + 1) * q := hq
          _ = 2 * (2 ^ (v2Fuel f (n / 2) + 1) * q) := by ring)⟩
    · -- n is odd: v2Fuel (f+1) n = 0
      have hv : v2Fuel (f + 1) n = 0 := by
        cases n with
        | zero => omega
        | succ m =>
          have : v2Fuel (f + 1) (m + 1) =
              if (m + 1) % 2 = 0 then 1 + v2Fuel f ((m + 1) / 2) else 0 := rfl
          rw [this, if_neg heven]
      rw [hv, zero_add, pow_one]
      intro ⟨q, hq⟩; omega

/-- **Every integer resolves at its native scale.**
    For odd n, at level k = v₂(3n+1) (computed via canonical self-fueled v₂),
    the exact valuation is k — NOT k+1 or higher.
    In other words: 2^(k+1) does NOT divide 3n+1.

    This proves n is safe at level k+1 (when n itself is used as the residue).
    Proof: apply the bridge lemma with fuel = 3n+1 (always adequate by Nat.lt_two_pow_self). -/
theorem integer_resolves_at_native_scale (n : ℕ) (hn : Odd n) :
    ¬ isUnsafe n (v2 (3 * n + 1) + 1) := by
  simp only [isUnsafe, v2]
  apply v2Fuel_not_upper_dvd
  · positivity
  · exact Nat.lt_two_pow_self

/-! ## Section 7: The Contraction Power Bound -/

set_option exponentiation.threshold 2000 in
/-- The integer encoding of log₂3 < 1.585: verifies 3^1000 < 2^1585.
    This is the foundation for converting contraction certificates into
    actual size bounds on Collatz orbits. -/
lemma three_pow_1000_lt : (3 : ℕ) ^ 1000 < 2 ^ 1585 := by norm_num

/-- **Contraction Power Bound**
    If the modular certificate data satisfies 1000·S > W·1585 (negative drift),
    then 3^W < 2^S (size actually shrinks over W steps).

    Proof: raise both sides to the 1000th power:
      (3^W)^1000 = (3^1000)^W < (2^1585)^W = 2^(1585W) ≤ 2^(1000S) = (2^S)^1000
    The first inequality uses 3^1000 < 2^1585; the last step uses 1585W < 1000S. -/
lemma contraction_pow_bound (W S : ℕ) (h : 1000 * S > W * 1585) : (3 : ℕ) ^ W < 2 ^ S := by
  have h3 := three_pow_1000_lt
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · -- W=0: 3^0 = 1 < 2^S (S ≥ 1 since 1000*S > 0)
    simp only [pow_zero]
    calc (1 : ℕ) < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) (by omega)
  · by_contra hle
    push_neg at hle
    have h_lo : (2 ^ S) ^ 1000 ≤ (3 ^ W) ^ 1000 := Nat.pow_le_pow_left hle 1000
    have h_hi : (3 ^ W) ^ 1000 < (2 ^ S) ^ 1000 :=
      calc (3 ^ W) ^ 1000
          = (3 ^ 1000) ^ W   := by ring
        _ < (2 ^ 1585) ^ W   := Nat.pow_lt_pow_left h3 hW.ne'
        _ = 2 ^ (1585 * W)   := by ring
        _ ≤ 2 ^ (1000 * S)   := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2 ^ S) ^ 1000   := by ring
    linarith

open UFRF.CollatzSolenoid in
/-- k=3 certificate in the ContractionAt form. -/
theorem contracting_at_3 : ∃ (W S : ℕ),
    (∀ r : Fin 52, v2Sum 104 W (2 * r.val + 1) ≥ S) ∧ 1000 * S > W * 1585 :=
  ⟨10, 16, contraction_k3, by norm_num⟩

open UFRF.CollatzSolenoid in
/-- k=4 certificate. -/
theorem contracting_at_4 : ∃ (W S : ℕ),
    (∀ r : Fin 104, v2Sum 208 W (2 * r.val + 1) ≥ S) ∧ 1000 * S > W * 1585 :=
  ⟨22, 35, contraction_k4, by norm_num⟩

open UFRF.CollatzSolenoid in
/-- **General W(k) Contraction Theorem**
    At every tower scale k ≥ 3, there exist W, S such that:
    (1) every odd residue mod 13·2^k has v₂ sum ≥ S over W steps, and
    (2) 1000·S > W·1585 (negative log₂ drift — combined with contraction_pow_bound,
        gives 3^W < 2^S, i.e., actual size decrease).

    Python data for W(k) = {3:10, 4:22, 5:26, 6:42, 7:52, 8:54, 9:59, 10:78}.
    Key open condition: W(k) < 13·2^k (window fits in one period).
    This would follow from: max bad streak ≤ k+1 + bounded recovery time.
    OPEN: the main proof obligation for Collatz convergence. -/
theorem contraction_at_all_scales (k : ℕ) (hk : 3 ≤ k) :
    ∃ (W S : ℕ),
      (∀ r : Fin (13 * 2 ^ (k - 1)),
        v2Sum (13 * 2 ^ k) W (2 * r.val + 1) ≥ S) ∧
      1000 * S > W * 1585 := by
  sorry

/-- **Collatz convergence from concurrent scale structure**

    The complete proof chain (open obligations marked ⬜):

    ✅ 1. Every odd n resolves at its native scale k = v₂(3n+1):
          ¬ 2^(k+1) ∣ 3n+1         [integer_resolves_at_native_scale]
    ✅ 2. Negative drift is equivalent to size decrease:
          1000·S > W·1585 → 3^W < 2^S   [contraction_pow_bound]
    ⬜ 3. For all scales k ≥ 3, a W(k) contraction certificate exists:
          ∀ k ≥ 3, ∃ W S, (bound over odd residues) ∧ (negative drift)
                          [contraction_at_all_scales — main open obligation]
    ⬜ 4. The modular orbit at scale k = v₂(3n+1) correctly reflects the actual
          Collatz orbit of n (safe residues → v₂ is exact).
    ⬜ 5. After W steps the orbit shrinks: n' < n (compose 2,3,4 over W steps).
    ⬜ 6. Geometric decrease → termination by well-foundedness.

    Open obligations (3)–(6) reduce to:
    - Proving the general W(k) exists for ALL k (the analytic heart)
    - Connecting the modular safe-orbit to actual integer arithmetic -/
theorem collatz_convergence_from_concurrent_scales (n : ℕ) (hn : Odd n) :
    ∃ t : ℕ, (Nat.rec n (fun _ m => if m % 2 = 0 then m / 2 else 3 * m + 1) t) = 1 := by
  sorry

end UFRF.ConcurrentScales
