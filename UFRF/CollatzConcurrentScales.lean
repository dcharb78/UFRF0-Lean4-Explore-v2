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

/-! ## Section 6.5: Two-Adic Bridge — Connecting Divisibility to v₂

These lemmas provide the exact two-way bridge between divisibility conditions
(`isUnsafe r k = 2^k ∣ 3r+1`) and the canonical v₂ function. Together they
form the mathematical core of **Step 4** of the convergence chain:

> If n ≡ r (mod 13·2^(k+1)) and r is **exactly** at scale k
> (i.e., 2^k ∣ 3r+1 but 2^(k+1) ∤ 3r+1), then v₂(3n+1) = k.

The proof chain: modular congruence mod 13·2^(k+1) implies congruence mod
2^(k+1), which (by the exact v₂ characterization) forces v₂(3n+1) = k.
-/

/-- v2Fuel (f+1) (n+1) unfolds to the if-then-else branch.
    (Defined here to be available in v2Fuel_dvd_lower and later.) -/
private lemma v2Fuel_succ_succ (f n : ℕ) :
    v2Fuel (f + 1) (n + 1) =
      if (n + 1) % 2 = 0 then 1 + v2Fuel f ((n + 1) / 2) else 0 := rfl

/-- Lower bound companion to `v2Fuel_not_upper_dvd`:
    2^(v2Fuel fuel n) always divides n, for any fuel. -/
private lemma v2Fuel_dvd_lower (fuel n : ℕ) : 2 ^ v2Fuel fuel n ∣ n := by
  induction fuel generalizing n with
  | zero => simp [v2Fuel]
  | succ f ih =>
    cases n with
    | zero => simp [v2Fuel]
    | succ m =>
      rw [v2Fuel_succ_succ]
      by_cases hev : (m + 1) % 2 = 0
      · rw [if_pos hev]
        obtain ⟨q, hq⟩ := ih ((m + 1) / 2)
        -- Abstract v₂ to avoid circular rewriting: hq has (m+1)/2 on both sides
        set v := v2Fuel f ((m + 1) / 2) with hv_def
        -- Now hq : (m+1)/2 = 2^v * q, where v is opaque (no (m+1)/2 in RHS)
        refine ⟨q, ?_⟩
        calc m + 1 = 2 * ((m + 1) / 2) := by omega
          _ = 2 * (2 ^ v * q)           := by rw [hq]
          _ = 2 ^ (1 + v) * q           := by ring
      · rw [if_neg hev]; exact one_dvd _

/-- The canonical v₂ is characterized exactly by the divisibility gap:
    v2 n = k ↔ (2^k ∣ n ∧ ¬ 2^(k+1) ∣ n), for n > 0. -/
lemma v2_eq_of_dvd_not_dvd {n : ℕ} (hn : 0 < n) {k : ℕ}
    (hdvd : 2 ^ k ∣ n) (hndvd : ¬ 2 ^ (k + 1) ∣ n) : v2 n = k := by
  simp only [v2]
  have hlo : 2 ^ v2Fuel n n ∣ n := v2Fuel_dvd_lower n n
  have hhi : ¬ 2 ^ (v2Fuel n n + 1) ∣ n :=
    v2Fuel_not_upper_dvd n n hn Nat.lt_two_pow_self
  -- Uniqueness of the 2-adic valuation: both k and v2Fuel n n are the exact v₂
  rcases Nat.lt_trichotomy (v2Fuel n n) k with hlt | heq | hgt
  · -- v2Fuel n n < k: then 2^(v2Fuel n n + 1) ∣ 2^k ∣ n, contradicting hhi
    exact absurd (dvd_trans (Nat.pow_dvd_pow 2 hlt) hdvd) hhi
  · exact heq
  · -- v2Fuel n n > k: then 2^(k+1) ∣ 2^(v2Fuel n n) ∣ n, contradicting hndvd
    exact absurd (dvd_trans (Nat.pow_dvd_pow 2 hgt) hlo) hndvd

/-- **Two-adic congruence preserves v₂**:
    If n ≡ r (mod 2^(k+1)) and v₂(3r+1) = k, then v₂(3n+1) = k.
    The key: congruence mod 2^(k+1) forces 3n+1 and 3r+1 to share the same
    exact 2-adic valuation k. -/
lemma two_adic_congr_v2 (n r k : ℕ)
    (hmod : n % 2 ^ (k + 1) = r % 2 ^ (k + 1))
    (hv2r : v2 (3 * r + 1) = k) : v2 (3 * n + 1) = k := by
  -- Extract divisibility facts from hv2r
  simp only [v2] at hv2r
  have hr_pos : 0 < 3 * r + 1 := by omega
  have hr_lo : 2 ^ k ∣ 3 * r + 1 :=
    hv2r ▸ v2Fuel_dvd_lower (3 * r + 1) (3 * r + 1)
  have hr_hi : ¬ 2 ^ (k + 1) ∣ 3 * r + 1 :=
    hv2r ▸ v2Fuel_not_upper_dvd _ _ hr_pos Nat.lt_two_pow_self
  -- 3n+1 ≡ 3r+1 (mod 2^(k+1)) from the congruence on n and r (linear in n, r)
  have hcongr : (3 * n + 1) % 2 ^ (k + 1) = (3 * r + 1) % 2 ^ (k + 1) :=
    Nat.ModEq.add_right 1 (Nat.ModEq.mul_left 3 hmod)
  -- 2^k ∣ 3n+1: use congruence mod 2^k ≤ 2^(k+1)
  have hcongr_k : (3 * n + 1) % 2 ^ k = (3 * r + 1) % 2 ^ k := by
    have h1 := Nat.mod_mod_of_dvd (3 * n + 1) (Nat.pow_dvd_pow 2 (Nat.le_succ k))
    have h2 := Nat.mod_mod_of_dvd (3 * r + 1) (Nat.pow_dvd_pow 2 (Nat.le_succ k))
    -- h1 : (3n+1) % 2^(k+1) % 2^k = (3n+1) % 2^k
    -- h2 : (3r+1) % 2^(k+1) % 2^k = (3r+1) % 2^k
    rw [← h1, hcongr, h2]
  have hn_lo : 2 ^ k ∣ 3 * n + 1 := by
    rwa [Nat.dvd_iff_mod_eq_zero, hcongr_k, ← Nat.dvd_iff_mod_eq_zero]
  have hn_hi : ¬ 2 ^ (k + 1) ∣ 3 * n + 1 := by
    rwa [Nat.dvd_iff_mod_eq_zero, hcongr, ← Nat.dvd_iff_mod_eq_zero]
  exact v2_eq_of_dvd_not_dvd (by omega) hn_lo hn_hi

/-- **Safe lift v₂ agreement** (Step 4, one step):
    If n ≡ r (mod 13·2^(k+1)) and r is *exactly* at scale k
    (isUnsafe r k but ¬ isUnsafe r (k+1)), then v₂(3n+1) = k = v₂(3r+1).

    Proof: 13·2^(k+1) divisibility → 2^(k+1) divisibility (13 is odd) →
           two_adic_congr_v2.  ✅ PROVEN -/
theorem safe_lift_v2_agrees (n r k : ℕ)
    (hmod : n % (13 * 2 ^ (k + 1)) = r % (13 * 2 ^ (k + 1)))
    (hr_k : isUnsafe r k) (hr_k1 : ¬ isUnsafe r (k + 1)) :
    v2 (3 * n + 1) = k ∧ v2 (3 * r + 1) = k := by
  -- Extract v₂(3r+1) = k from isUnsafe conditions
  have hv2r : v2 (3 * r + 1) = k :=
    v2_eq_of_dvd_not_dvd (by omega) hr_k hr_k1
  -- Reduce to 2^(k+1) congruence: 2^(k+1) ∣ 13·2^(k+1), so mod 13·2^(k+1) → mod 2^(k+1)
  have hmod_2 : n % 2 ^ (k + 1) = r % 2 ^ (k + 1) := by
    have h1 := Nat.mod_mod_of_dvd n (dvd_mul_left (2 ^ (k + 1)) 13)
    have h2 := Nat.mod_mod_of_dvd r (dvd_mul_left (2 ^ (k + 1)) 13)
    -- h1 : n % (13·2^(k+1)) % 2^(k+1) = n % 2^(k+1)
    -- h2 : r % (13·2^(k+1)) % 2^(k+1) = r % 2^(k+1)
    rw [← h1, hmod, h2]
  exact ⟨two_adic_congr_v2 n r k hmod_2 hv2r, hv2r⟩

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
/-- k=5 certificate. -/
theorem contracting_at_5 : ∃ (W S : ℕ),
    (∀ r : Fin 208, v2Sum 416 W (2 * r.val + 1) ≥ S) ∧ 1000 * S > W * 1585 :=
  ⟨26, 42, contraction_k5, by norm_num⟩

open UFRF.CollatzSolenoid in
/-- k=6 certificate. -/
theorem contracting_at_6 : ∃ (W S : ℕ),
    (∀ r : Fin 416, v2Sum 832 W (2 * r.val + 1) ≥ S) ∧ 1000 * S > W * 1585 :=
  ⟨42, 67, contraction_k6, by norm_num⟩

open UFRF.CollatzSolenoid in
/-- k=7 certificate. -/
theorem contracting_at_7 : ∃ (W S : ℕ),
    (∀ r : Fin 832, v2Sum 1664 W (2 * r.val + 1) ≥ S) ∧ 1000 * S > W * 1585 :=
  ⟨52, 83, contraction_k7, by norm_num⟩

open UFRF.CollatzSolenoid in
/-- k=8 certificate. -/
theorem contracting_at_8 : ∃ (W S : ℕ),
    (∀ r : Fin 1664, v2Sum 3328 W (2 * r.val + 1) ≥ S) ∧ 1000 * S > W * 1585 :=
  ⟨54, 87, contraction_k8, by norm_num⟩

open UFRF.CollatzSolenoid in
/-- k=9 certificate. -/
theorem contracting_at_9 : ∃ (W S : ℕ),
    (∀ r : Fin 3328, v2Sum 6656 W (2 * r.val + 1) ≥ S) ∧ 1000 * S > W * 1585 :=
  ⟨59, 95, contraction_k9, by norm_num⟩

open UFRF.CollatzSolenoid in
/-- k=10 certificate. -/
theorem contracting_at_10 : ∃ (W S : ℕ),
    (∀ r : Fin 6656, v2Sum 13312 W (2 * r.val + 1) ≥ S) ∧ 1000 * S > W * 1585 :=
  ⟨78, 125, contraction_k10, by norm_num⟩

open UFRF.CollatzSolenoid in
/-- k=11 certificate. -/
theorem contracting_at_11 : ∃ (W S : ℕ),
    (∀ r : Fin 13312, v2Sum 26624 W (2 * r.val + 1) ≥ S) ∧ 1000 * S > W * 1585 :=
  ⟨84, 134, contraction_k11, by norm_num⟩

open UFRF.CollatzSolenoid in
/-- k=12 certificate. -/
theorem contracting_at_12 : ∃ (W S : ℕ),
    (∀ r : Fin 26624, v2Sum 53248 W (2 * r.val + 1) ≥ S) ∧ 1000 * S > W * 1585 :=
  ⟨80, 128, contraction_k12, by norm_num⟩

open UFRF.CollatzSolenoid in
/-- **Contraction at scales 3..12**: `contraction_at_all_scales` is proved
    for k ∈ {3,...,12} by dispatching to the pre-verified certificates.

    ✅ PROVEN (k=3..12) -/
theorem contraction_at_scales_3_to_12 (k : ℕ) (hk3 : 3 ≤ k) (hk12 : k ≤ 12) :
    ∃ (W S : ℕ),
      (∀ r : Fin (13 * 2 ^ (k - 1)),
        v2Sum (13 * 2 ^ k) W (2 * r.val + 1) ≥ S) ∧
      1000 * S > W * 1585 := by
  interval_cases k
  · exact contracting_at_3
  · exact contracting_at_4
  · exact contracting_at_5
  · exact contracting_at_6
  · exact contracting_at_7
  · exact contracting_at_8
  · exact contracting_at_9
  · exact contracting_at_10
  · exact contracting_at_11
  · exact contracting_at_12

/-! NOTE: `contraction_at_all_scales` (for all k ≥ 3) was sorry'd here because the
    statement is **FALSE for k = 13** (period-14 orbit at r=8191, avg v₂ ≈ 1.143 < log₂3).
    The correct proved result is `contraction_at_scales_3_to_12` above (k ∈ {3,...,12}).
    For k ≥ 13, a multi-scale or direct argument is needed; see Section 10. -/

/-! ## Section 5.5: Exact Syracuse Step and One-Step Shrinkage (Step 5)

These definitions and theorems implement **Step 5** of the 6-step convergence chain:
given that the modular orbit contracts (Step 3), show the actual integer orbit decreases.

`syracuseExact n = (3n+1) / 2^v₂(3n+1)` is the standard Collatz odd-step ("Syracuse") map.

**Immediately provable case** (✅): when v₂(3n+1) ≥ 2, one application of `syracuseExact`
already yields a strictly smaller result (`syracuse_shrinks_when_v2_ge2`). This covers all
residues at certified scales k ≥ 2 where v₂(3n+1) = k ≥ 2.

**Hard open case** (⬜): when v₂(3n+1) = 1 (a bad step), the first Syracuse step gives
(3n+1)/2 > n, so W steps with a window argument are needed (`orbit_shrinks_W_steps`).
This is equivalent to the Collatz conjecture — see §7.1 for why no fixed W works
(n = 2^K−1 creates K−1 consecutive v₂=1 steps) and why the modular-to-integer
bridge (solenoid coherence) fails. One-step v₂ matching: `safe_lift_v2_agrees` (✅).
-/

/-- The exact Syracuse / Collatz odd-step map:
    n ↦ (3n+1) divided by its exact 2-adic valuation.
    Equivalently: the largest odd divisor of 3n+1. -/
def syracuseExact (n : ℕ) : ℕ := (3 * n + 1) / 2 ^ v2 (3 * n + 1)

/-- **One-step shrinkage when v₂(3n+1) ≥ 2.**
    For n > 1, if at least two factors of 2 are removed in the Syracuse step, the
    result is strictly smaller than n.

    Proof: 2^v₂ ≥ 2^2 = 4, so
      (3n+1)/2^v₂ ≤ (3n+1)/4 < n   (since 3n+1 < 4n ↔ n > 1).
    ✅ PROVEN -/
theorem syracuse_shrinks_when_v2_ge2 (n : ℕ) (hn : 1 < n) (hv2 : 2 ≤ v2 (3 * n + 1)) :
    syracuseExact n < n := by
  unfold syracuseExact
  have h4 : (4 : ℕ) ≤ 2 ^ v2 (3 * n + 1) :=
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ v2 (3 * n + 1) := Nat.pow_le_pow_right (by norm_num) hv2
  -- Larger denominator → smaller quotient: (3n+1)/2^v₂ ≤ (3n+1)/4
  have hstep : (3 * n + 1) / 2 ^ v2 (3 * n + 1) ≤ (3 * n + 1) / 4 :=
    Nat.div_le_div_left h4 (by omega)
  -- (3n+1)/4 < n because 3n+1 < 4n ↔ n > 1
  omega

/-- **Corollary for certified scales**: at any scale k ∈ {3,...,12} where v₂(3n+1) = k,
    one Syracuse step already strictly decreases n (since k ≥ 3 ≥ 2).
    ✅ PROVEN -/
theorem safe_orbit_reflects_integer (n : ℕ) (hn : 1 < n) (hn_odd : n % 2 = 1)
    (k : ℕ) (hk3 : 3 ≤ k) (hk12 : k ≤ 12)
    (hv2k : v2 (3 * n + 1) = k) :
    syracuseExact n < n :=
  -- v₂(3n+1) = k ≥ 3 ≥ 2, so syracuse_shrinks_when_v2_ge2 applies directly.
  syracuse_shrinks_when_v2_ge2 n hn (by omega)

/-- **W-step orbit shrinkage** (Step 5, general case — ⬜ OPEN)

    Every odd n > 1 has some W > 0 such that `(syracuseExact^[W] n) < n`.

    **Proved sub-case** (v₂ ≥ 2): W = 1 works directly by `syracuse_shrinks_when_v2_ge2`.

    **Open sub-case** (v₂ = 1): The first step gives (3n+1)/2 > n. The contraction
    **Status (revised 2026-04-02)**: The original plan was to use `solenoid_coherence_W_steps`
    to bridge modular contraction certificates to the integer orbit with fixed W = 10.
    This approach fails for two reasons:

    (A) **`solenoid_coherence_W_steps` is FALSE as stated** (see Section 7.1 below).
        The modular v₂ sum overcounts because `v2Fuel 64 (3r+1)` can exceed the
        2-adic precision v₂(m) of the modulus. Counterexample: m=8, n=13, W=1.

    (B) **No fixed W gives universal contraction**. The integers n = 2^K − 1
        have K−1 consecutive v₂ = 1 steps, giving `v2SumExact W n = W` for W ≤ K−1.
        Since 3^W > 2^W for all W ≥ 1, no fixed-W certificate handles all n.
        Verified: `v2SumExact 10 2047 = 10`, while `contraction_k3` claims v₂ sum ≥ 16.
        The window W needed to shrink n = 2^K − 1 grows with K (e.g., K=24 needs W=71).

    **Conclusion**: `orbit_shrinks_W_steps` (∃ W for each n) IS the Collatz conjecture
    for odd numbers. The v₂ ≥ 2 case and small cases are resolved; the general case
    remains the famous open problem.

    ⬜ EQUIVALENT TO THE COLLATZ CONJECTURE -/
theorem orbit_shrinks_W_steps (n : ℕ) (hn : 1 < n) (hn_odd : n % 2 = 1) :
    ∃ W : ℕ, 0 < W ∧ (syracuseExact^[W] n) < n := by
  -- The v₂ ≥ 2 case: one step suffices immediately.
  by_cases hv2 : 2 ≤ v2 (3 * n + 1)
  · exact ⟨1, Nat.one_pos, syracuse_shrinks_when_v2_ge2 n hn hv2⟩
  -- v₂ = 1: the first step expands (3n+1)/2 > n.
  · push_neg at hv2
    -- v₂(3n+1) = 1 exactly (≥1 since n odd → 3n+1 even, <2 by hv2)
    have hv2_ge1 : 1 ≤ v2 (3 * n + 1) := by
      simp only [v2]; rw [v2Fuel_succ_succ, if_pos (by omega)]; omega
    have hv2_one : v2 (3 * n + 1) = 1 := Nat.le_antisymm (by omega) hv2_ge1
    -- Small cases: n odd, 1 < n, v₂=1 → n ≡ 3 (mod 4).
    -- Enumerate n ∈ {3, 7} (the only odd n > 1 with v₂=1 and n < 11).
    by_cases hn_small : n < 11
    · interval_cases n
      -- n=2: impossible (even)
      · omega
      -- n=3: syscuseExact^2 3 = 1 < 3
      · exact ⟨2, by norm_num, by native_decide⟩
      -- n=4: impossible (even)
      · omega
      -- n=5: v₂(16)=4 ≠ 1 — contradicts hv2_one
      · simp [v2, v2Fuel] at hv2_one
      -- n=6: impossible (even)
      · omega
      -- n=7: syscuseExact^4 7 = 5 < 7
      · exact ⟨4, by norm_num, by native_decide⟩
      -- n=8: impossible (even)
      · omega
      -- n=9: v₂(28)=2 → v₂ ≥ 2 — contradicts hv2 (which says v₂ < 2)
      · simp [v2, v2Fuel] at hv2
      -- n=10: impossible (even)
      · omega
    · -- n ≥ 11, v₂ = 1: THIS IS THE COLLATZ CONJECTURE.
      --
      -- The orbit expands by factor 3/2 at each v₂=1 step. To shrink, the orbit
      -- must eventually encounter enough v₂ ≥ 2 steps to compensate.
      -- n = 2^K − 1 creates K−1 consecutive v₂=1 steps, so no fixed W works
      -- universally. Each n does eventually shrink (computationally verified
      -- for n up to 2^68), but proving this for all n is the Collatz conjecture.
      --
      -- The UFRF framework provides:
      -- ✅ exact_orbit_formula: 2^S · q = 3^W · n + ε (structural identity)
      -- ✅ contraction_pow_bound: 1000·S > W·1585 → 3^W < 2^S
      -- ✅ contraction certificates k=3..12 (modular v₂ sums)
      -- ⬜ Bridge from modular to integer v₂ sums (solenoid coherence — see §7.1)
      --    The bridge as originally formulated is FALSE; the correct version
      --    requires orbit synchronization which fails at fixed moduli.
      push_neg at hn_small
      sorry

/-! ## Section 5.6: Oddness Preservation and Well-Founded Descent (Step 6)

`syracuseExact n = (3n+1) / 2^v₂(3n+1)` is the **odd part** of 3n+1.
When n is odd, 3n+1 is even, and dividing by the exact power of 2 leaves an odd number.
This is proved in `syracuseExact_odd`.

With oddness preservation in hand, **Step 6** (`orbit_reaches_one_conditional`) closes
the convergence proof **conditionally**: given any W-step shrinkage property (like
`orbit_shrinks_W_steps`), strong induction yields termination. -/

/-- `syracuseExact` maps odd numbers to odd numbers: the odd part of an even number is odd.
    ✅ PROVEN -/
lemma syracuseExact_odd {n : ℕ} (hn : n % 2 = 1) : (syracuseExact n) % 2 = 1 := by
  unfold syracuseExact
  set k := v2 (3 * n + 1) with hk_def
  have h3n1_pos : 0 < 3 * n + 1 := by omega
  -- 2^k ∣ 3n+1 (lower bound)
  have hlo : 2 ^ k ∣ 3 * n + 1 := by
    rw [hk_def]; exact v2Fuel_dvd_lower _ _
  -- ¬ 2^(k+1) ∣ 3n+1 (upper bound)
  have hhi : ¬ 2 ^ (k + 1) ∣ 3 * n + 1 := by
    rw [hk_def]; exact v2Fuel_not_upper_dvd _ _ h3n1_pos Nat.lt_two_pow_self
  -- Write 3n+1 = 2^k * q; then q is odd
  obtain ⟨q, hq⟩ := hlo
  have hq_odd : ¬ 2 ∣ q := by
    intro ⟨r, hr⟩
    exact hhi ⟨r, by rw [hq, hr, pow_succ]; ring⟩
  -- (3n+1)/2^k = q (odd)
  have hq_eq : (3 * n + 1) / 2 ^ k = q := by
    calc (3 * n + 1) / 2 ^ k
        = 2 ^ k * q / 2 ^ k := by rw [hq]
      _ = q := Nat.mul_div_cancel_left q (by positivity)
  rw [hq_eq]; omega

/-- Iteration of `syracuseExact` preserves oddness (by induction on W). ✅ PROVEN -/
lemma syracuseExact_iter_odd (n : ℕ) (hn : n % 2 = 1) (W : ℕ) :
    (syracuseExact^[W] n) % 2 = 1 := by
  induction W with
  | zero => simpa using hn
  | succ W ih =>
    rw [Function.iterate_succ_apply']
    exact syracuseExact_odd ih

/-- **Step 6: Well-founded descent** (✅ PROVEN, conditional on `orbit_shrinks_W_steps`)

    Given any W-step shrinkage hypothesis, every odd n eventually reaches 1 under
    iterated `syracuseExact`.

    Proof: bounded induction via ∀ (k n), n < k → P n. At each step:
    - If n ≤ 1 (odd → n = 1): done in 0 steps.
    - If n > 1: get W from the shrinkage hypothesis, giving n' = syracuseExact^[W] n < n.
      n' is odd (by `syracuseExact_iter_odd`) and satisfies n' < k (since n < k+1 and n' < n).
      By IH, some t steps reach 1 from n'. So t + W steps reach 1 from n.

    ✅ PROVEN  (conditional on `orbit_shrinks_W_steps`, which has 1 sorry in the
    v₂=1, n≥11 case — equivalent to the Collatz conjecture, see §7.1–§7.2) -/
theorem orbit_reaches_one_conditional
    (hshrink : ∀ m : ℕ, 1 < m → m % 2 = 1 →
                ∃ W : ℕ, 0 < W ∧ (syracuseExact^[W] m) < m)
    (n : ℕ) (hn_odd : n % 2 = 1) :
    ∃ t : ℕ, syracuseExact^[t] n = 1 := by
  -- Bounded induction: suffices ∀ k n, n < k → odd n → ∃ t, f^[t] n = 1
  suffices h : ∀ (k n : ℕ), n < k → n % 2 = 1 → ∃ t, syracuseExact^[t] n = 1 from
    h (n + 1) n (Nat.lt_succ_self n) hn_odd
  intro k
  induction k with
  | zero => intro n hn _; exact absurd hn (Nat.not_lt_zero n)
  | succ k ih =>
    intro n hn hn_odd
    by_cases hn1 : n ≤ 1
    · -- n is odd and ≤ 1, so n = 1; reached in 0 steps
      exact ⟨0, by simp [show n = 1 from by omega]⟩
    · push_neg at hn1
      obtain ⟨W, _, hlt⟩ := hshrink n hn1 hn_odd
      -- n' = syracuseExact^[W] n satisfies n' < n ≤ k
      have hn'_lt_k : syracuseExact^[W] n < k :=
        Nat.lt_of_lt_of_le hlt (Nat.lt_succ_iff.mp hn)
      -- n' is odd (by iteration lemma)
      have hn'_odd : (syracuseExact^[W] n) % 2 = 1 := syracuseExact_iter_odd n hn_odd W
      -- IH gives t steps from n' to 1
      obtain ⟨t, ht⟩ := ih (syracuseExact^[W] n) hn'_lt_k hn'_odd
      -- Combined: t + W steps from n reach 1
      exact ⟨t + W, by rw [Function.iterate_add_apply]; exact ht⟩

/-! ## Section 5.7: Standard Collatz Map and Key Bridge Theorem

This section defines `collatzMap` (the standard Collatz recurrence: halve if even,
triple-plus-one if odd) and proves the crucial bridge connecting it to `syracuseExact`:

  **For odd n: `collatzMap^[v₂(3n+1) + 1] n = syracuseExact n`**

The proof has two sub-steps:
- The first `collatzMap` application sends n ↦ 3n+1 (n is odd).
- The next v₂(3n+1) applications each halve (since 2^i ∣ 3n+1 for i ≤ v₂(3n+1)).
- Combined: (3n+1) / 2^(v₂(3n+1)) = syracuseExact n.

This bridge closes the "connection" obligation in Step 6:
  `orbit_reaches_one_conditional` (syscuseExact) + this bridge →
  the Nat.rec form of Collatz convergence.

The remaining open obligation is `orbit_shrinks_W_steps` (the v₂=1 window argument). -/

/-- The standard Collatz map: halve if even, triple-plus-one if odd. -/
def collatzMap (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `collatzMap` on even input: halve.  ✅ PROVEN -/
lemma collatzMap_even (n : ℕ) (hn : n % 2 = 0) : collatzMap n = n / 2 := by
  simp [collatzMap, hn]

/-- `collatzMap` on odd input: triple-plus-one.  ✅ PROVEN -/
lemma collatzMap_odd_step (n : ℕ) (hn : n % 2 = 1) : collatzMap n = 3 * n + 1 := by
  simp [collatzMap, show n % 2 ≠ 0 from by omega]

/-- **Halving iterate**: when 2^k ∣ m, k applications of `collatzMap` halve m exactly
    k times: collatzMap^[k] m = m / 2^k.

    Proof: induction on k. Step: m even (from 2^(k+1) ∣ m), so collatzMap m = m/2;
    apply IH to m/2 with 2^k ∣ m/2; reconcile via m/2/2^k = m/2^(k+1).
    ✅ PROVEN -/
lemma collatzMap_halving_iterate (k m : ℕ) (h : 2^k ∣ m) :
    collatzMap^[k] m = m / 2^k := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    -- 2 ∣ m (since 2^(k+1) ∣ m)
    have hdvd2 : 2 ∣ m := dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero k)) h
    obtain ⟨q2, hq2⟩ := hdvd2
    have hm_even : m % 2 = 0 := by omega
    -- Extract the quotient at level k+1
    obtain ⟨q, hq⟩ := h
    -- m = 2 * (2^k * q)
    have h1 : m = 2 * (2^k * q) := by rw [hq]; ring
    -- m / 2 = 2^k * q
    have hm2 : m / 2 = 2^k * q := by
      rw [h1, Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)]
    -- 2^k ∣ m / 2
    have h_half_dvd : 2^k ∣ m / 2 := ⟨q, hm2⟩
    -- (m / 2) / 2^k = q
    have h_half_k : (m / 2) / 2^k = q :=
      hm2 ▸ Nat.mul_div_cancel_left q (by positivity)
    -- m / 2^(k+1) = q
    have hm_k1 : m / 2^(k + 1) = q :=
      hq ▸ Nat.mul_div_cancel_left q (by positivity)
    -- Chain: collatzMap^[k+1] m = collatzMap^[k] (m/2) = (m/2)/2^k = q = m/2^(k+1)
    rw [Function.iterate_succ_apply, collatzMap_even m hm_even,
        ih (m / 2) h_half_dvd, h_half_k, hm_k1]

/-- **Key bridge theorem**: for odd n, iterating `collatzMap` exactly v₂(3n+1)+1 times
    from n yields the same result as one application of `syracuseExact`.

    Proof:
    - Step 0 (odd step): collatzMap n = 3n+1.
    - Steps 1..v₂(3n+1) (halving): 2^(v₂(3n+1)) ∣ 3n+1 → collatzMap^[v₂] (3n+1) = (3n+1)/2^(v₂).
    - Definition: (3n+1)/2^(v₂(3n+1)) = syracuseExact n. ✅ PROVEN -/
theorem collatzMap_iterate_eq_syracuseExact (n : ℕ) (hn : n % 2 = 1) :
    collatzMap^[v2 (3 * n + 1) + 1] n = syracuseExact n := by
  set k := v2 (3 * n + 1) with hk_def
  -- Apply one odd step: collatzMap n = 3n+1
  rw [Function.iterate_succ_apply, collatzMap_odd_step n hn]
  -- 2^k ∣ 3n+1 (lower bound from v2)
  have hv2_dvd : 2^k ∣ 3 * n + 1 := by
    rw [hk_def]; exact v2Fuel_dvd_lower _ _
  -- k halving steps
  rw [collatzMap_halving_iterate k (3 * n + 1) hv2_dvd]
  -- Match the definition of syracuseExact
  unfold syracuseExact; rw [← hk_def]

/-- The `Nat.rec` iteration form equals `collatzMap^[t]`.
    Proof: induction; succ case reduces by the Nat.rec rule and `collatzMap` definition.
    ✅ PROVEN -/
lemma natRec_collatz_eq_iterate (n t : ℕ) :
    (Nat.rec n (fun _ m => if m % 2 = 0 then m / 2 else 3 * m + 1) t : ℕ) =
    collatzMap^[t] n := by
  induction t with
  | zero => rfl
  | succ t ih =>
    -- Nat.rec reduces: Nat.rec n f (t+1) = f t (Nat.rec n f t) = collatzMap (Nat.rec n f t)
    show collatzMap (Nat.rec n (fun _ m => if m % 2 = 0 then m / 2 else 3 * m + 1) t) =
         collatzMap^[t + 1] n
    -- Rewrite the recursive call by IH; close using f^[t+1] n = f (f^[t] n)
    rw [ih]
    exact (Function.iterate_succ_apply' collatzMap t n).symm

/-- **Multi-step bridge**: if `syracuseExact` reaches 1 from odd n in t steps,
    then `collatzMap` also reaches 1 from n (in possibly more steps).

    Proof: induction on t. Base: t=0 means n=1, take s=0. Step: use
    `collatzMap_iterate_eq_syracuseExact` to consume the first syscuseExact step
    as v₂(3n+1)+1 collatzMap steps, then apply the IH to the remainder.
    ✅ PROVEN -/
private lemma syracuseExact_reach_one_lifts (t : ℕ) :
    ∀ n : ℕ, n % 2 = 1 → syracuseExact^[t] n = 1 → ∃ s : ℕ, collatzMap^[s] n = 1 := by
  induction t with
  | zero =>
    intro n _ h; exact ⟨0, by simpa using h⟩
  | succ t ih =>
    intro n hn h
    -- Unfold one syscuseExact step: f^[t+1] x = f^[t] (f x)
    rw [Function.iterate_succ_apply] at h
    -- h : syscuseExact^[t] (syscuseExact n) = 1
    obtain ⟨s', hs'⟩ := ih (syracuseExact n) (syracuseExact_odd hn) h
    -- collatzMap^[s' + (v₂(3n+1)+1)] n = collatzMap^[s'] (collatzMap^[v₂+1] n) = collatzMap^[s'] (syscuseExact n) = 1
    exact ⟨s' + (v2 (3 * n + 1) + 1), by
      rw [Function.iterate_add_apply, collatzMap_iterate_eq_syracuseExact n hn]; exact hs'⟩

/-- **Collatz convergence from concurrent scale structure**

    The complete proof chain:

    ✅ 1. Every odd n resolves at its native scale k = v₂(3n+1):
          ¬ 2^(k+1) ∣ 3n+1         [integer_resolves_at_native_scale]
    ✅ 2. Negative drift is equivalent to size decrease:
          1000·S > W·1585 → 3^W < 2^S   [contraction_pow_bound]
    ✅ 3. For k ∈ {3,...,12}, a W(k) modular contraction certificate exists:
          ∀ k ∈ {3,..,12}, ∃ W S, (bound over odd residues) ∧ (negative drift)
                          [contraction_at_scales_3_to_12]
          ⚠️ These certificates overcount: modular v₂ sums can exceed integer v₂ sums.
          See §7.1 for why the modular-to-integer bridge fails.
    ✅ 4. One-step: if n ≡ r (mod 13·2^(k+1)) and r is exactly at scale k,
          then v₂(3n+1) = k    [safe_lift_v2_agrees]
    ✅ 5. If v₂(3n+1) ≥ 2, one step shrinks n  [syracuse_shrinks_when_v2_ge2]
    ✅ 6. orbit_shrinks_W_steps → every odd n reaches 1  [orbit_reaches_one_conditional]
    ✅ 7. collatzMap^[v₂(3n+1)+1] n = syscuseExact n    [collatzMap_iterate_eq_syracuseExact]
    ✅ 8. syscuseExact^[t] n = 1 → collatzMap^[s] n = 1 [syracuseExact_reach_one_lifts]
    ✅ 9. Nat.rec form = collatzMap^[t]                  [natRec_collatz_eq_iterate]
    ✅ 10. Exact orbit formula: 2^S · q = 3^W · n + ε  [exact_orbit_formula]

    **Single open obligation**: `orbit_shrinks_W_steps` — the existential statement
    that every odd n > 1 has some W-step orbit segment that shrinks. This is
    equivalent to the Collatz conjecture (see §7.1 for the full analysis). -/
theorem collatz_convergence_from_concurrent_scales (n : ℕ) (hn : Odd n) :
    ∃ t : ℕ, (Nat.rec n (fun _ m => if m % 2 = 0 then m / 2 else 3 * m + 1) t) = 1 := by
  -- Extract n % 2 = 1 from `Odd n`
  have hn_odd : n % 2 = 1 := Nat.odd_iff.mp hn
  -- Step 6: get syscuseExact convergence (uses orbit_shrinks_W_steps which has sorry)
  obtain ⟨t, ht⟩ :=
    orbit_reaches_one_conditional (fun m hm hm_odd => orbit_shrinks_W_steps m hm hm_odd)
      n hn_odd
  -- Step 8: lift syscuseExact convergence to collatzMap convergence
  obtain ⟨s, hs⟩ := syracuseExact_reach_one_lifts t n hn_odd ht
  -- Step 9: convert collatzMap^[s] to the Nat.rec form
  exact ⟨s, by rw [natRec_collatz_eq_iterate, hs]⟩

/-! ## Section 5.8: Integer V₂ Sum and Exact Orbit Formula

### Key definitions and results (all proven, zero sorry)

* `v2SumExact W n`       — cumulative v₂ along the **integer** Syracuse orbit (✅).
* `v2_odd_ge_one`        — every odd step contributes v₂ ≥ 1 (✅).
* `v2SumExact_ge_W`      — cumulative v₂ sum ≥ W after W steps (✅).
* `correctionTerm W n`   — correction ε in the exact formula; ε₀=0, ε_{W+1}=3^W+2^v₁·ε_W (✅).
* `exact_orbit_formula`  — **2^S · syscuseExact^[W] n = 3^W · n + ε** exactly (✅).
-/

/-- The exact 2-adic valuation sum along the integer Syracuse orbit.
    `v2SumExact W n = Σ_{j<W} v₂(3·(syracuseExact^[j] n)+1)` -/
def v2SumExact : ℕ → ℕ → ℕ
  | 0, _ => 0
  | W + 1, n => v2 (3 * n + 1) + v2SumExact W (syracuseExact n)

/-- For any odd n, v₂(3n+1) ≥ 1 (since 3n+1 is even).
    Proof: v2(m) = v2Fuel m m; since n%2=1 implies (3n+1)%2=0,
    the first recursive step gives v2Fuel (3n+1) (3n+1) = 1 + ... ≥ 1. -/
private lemma v2_odd_ge_one (n : ℕ) (hn : n % 2 = 1) : 1 ≤ v2 (3 * n + 1) := by
  simp only [v2]
  -- v2Fuel ((3n)+1) ((3n)+1): apply the succ-succ unfolding with fuel=arg=3n
  rw [v2Fuel_succ_succ, if_pos (by omega)]
  omega

/-- The correction term in the exact orbit formula.
    ε₀ = 0, ε_{W+1} = 3^W + 2^(v₁) · ε_W  where v₁ = v₂(3n+1).
    In the all-v₁=1 worst case this equals 3^W − 2^W. -/
def correctionTerm : ℕ → ℕ → ℕ
  | 0, _ => 0
  | W + 1, n =>
    let v1 := v2 (3 * n + 1)
    3 ^ W + 2 ^ v1 * correctionTerm W (syracuseExact n)

/-- **Exact multiplicative orbit formula** (✅ PROVEN)

    For any odd n and any W ≥ 0:
      2^(v2SumExact W n) · (syracuseExact^[W] n) = 3^W · n + correctionTerm W n

    This shows the Syracuse orbit obeys an exact multiplicative relation.
    When v2SumExact W n ≥ S and 3^W < 2^S, the correction term determines
    the threshold for net shrinkage.  -/
lemma exact_orbit_formula (W n : ℕ) (hn : n % 2 = 1) :
    2 ^ (v2SumExact W n) * (syracuseExact^[W] n) =
      3 ^ W * n + correctionTerm W n := by
  induction W generalizing n with
  | zero => simp [v2SumExact, correctionTerm]
  | succ W ih =>
    rw [Function.iterate_succ_apply]
    simp only [v2SumExact, correctionTerm]
    -- Key: 2^v₁ · syscuseExact n = 3n+1  (exact division)
    have h_key : 2 ^ v2 (3 * n + 1) * syracuseExact n = 3 * n + 1 := by
      have hdvd : 2 ^ v2 (3 * n + 1) ∣ 3 * n + 1 := v2Fuel_dvd_lower _ _
      unfold syracuseExact
      rw [mul_comm]
      exact Nat.div_mul_cancel hdvd
    -- IH for the next orbit point
    have ih' := ih (syracuseExact n) (syracuseExact_odd hn)
    -- Chain: 2^(v1+S') · f^[W](f n) = 2^v1 · (2^S' · f^[W](f n))
    --      = 2^v1 · (3^W · f n + ε_W)     [IH]
    --      = 3^W · (2^v1 · f n) + 2^v1·ε  [ring]
    --      = 3^W · (3n+1) + 2^v1·ε        [h_key]
    --      = 3^(W+1)·n + (3^W + 2^v1·ε)   [ring]
    calc 2 ^ (v2 (3 * n + 1) + v2SumExact W (syracuseExact n)) *
          syracuseExact^[W] (syracuseExact n)
        = 2 ^ v2 (3 * n + 1) *
          (2 ^ v2SumExact W (syracuseExact n) * syracuseExact^[W] (syracuseExact n)) := by ring
      _ = 2 ^ v2 (3 * n + 1) *
          (3 ^ W * syracuseExact n + correctionTerm W (syracuseExact n)) := by rw [ih']
      _ = 3 ^ W * (2 ^ v2 (3 * n + 1) * syracuseExact n) +
          2 ^ v2 (3 * n + 1) * correctionTerm W (syracuseExact n) := by ring
      _ = 3 ^ W * (3 * n + 1) +
          2 ^ v2 (3 * n + 1) * correctionTerm W (syracuseExact n) := by rw [h_key]
      _ = 3 ^ (W + 1) * n +
          (3 ^ W + 2 ^ v2 (3 * n + 1) * correctionTerm W (syracuseExact n)) := by ring

/-- After W Syracuse steps, the cumulative integer v₂ sum is at least W. -/
lemma v2SumExact_ge_W (W n : ℕ) (hn : n % 2 = 1) : W ≤ v2SumExact W n := by
  induction W generalizing n with
  | zero => simp [v2SumExact]
  | succ W ih =>
    simp only [v2SumExact]
    have h1 : 1 ≤ v2 (3 * n + 1) := v2_odd_ge_one n hn
    have h2 : W ≤ v2SumExact W (syracuseExact n) := ih (syracuseExact n) (syracuseExact_odd hn)
    omega

/-! ### §5.9 Conditional Contraction from the Exact Orbit Formula

The `exact_orbit_formula` gives `2^S · q = 3^W · n + ε`. When `3^W · n + ε < 2^S · n`,
dividing both sides by `2^S` yields `q < n`. This isolates the sorry's dependency:
the Collatz conjecture reduces to showing that for each odd n > 1, there exists W where
the correction term `ε` is small enough relative to `(2^S − 3^W) · n`.

**Council of experts synthesis (2026-04-02)**:
Four domain experts (ergodic theory, p-adic analysis, probabilistic combinatorics, formal
verification) independently concluded that the sorry IS the Collatz conjecture. The gap
between "almost all n descend" (provable by density/measure arguments) and "all n descend"
(the conjecture) cannot be bridged by any known technique. Key obstacles:
- Ergodic theorems on ℤ₂ give measure-zero exceptions, not empty exceptions
- The 2-adic ↔ archimedean bridge has no known crossing
- Modular precision barrier: W steps consume ~2W bits, exhausting all tracking capacity
- The correction term is intrinsically coupled to the orbit (bounding ε ↔ bounding q)  -/

/-- **Conditional contraction**: if the total orbit contribution `3^W·n + ε` fits below
    `2^S · n`, the orbit has shrunk. This is an immediate consequence of `exact_orbit_formula`.

    This makes the sorry's dependency explicit: the Collatz conjecture reduces to showing
    that for each odd n > 1, ∃ W, `3^W * n + correctionTerm W n < 2^(v2SumExact W n) * n`.
    ✅ PROVEN -/
theorem orbit_shrinks_from_formula (W n : ℕ) (hn : n % 2 = 1)
    (_hW : 0 < W) (_hn1 : 0 < n)
    (h : 3 ^ W * n + correctionTerm W n < 2 ^ (v2SumExact W n) * n) :
    syracuseExact^[W] n < n := by
  have hformula := exact_orbit_formula W n hn
  -- hformula : 2^S * q = 3^W * n + ε
  -- h : 3^W * n + ε < 2^S * n
  -- Goal: q < n
  have hpow_pos : 0 < 2 ^ v2SumExact W n := pow_pos (by norm_num) _
  -- 2^S * q = 3^W * n + ε < 2^S * n → 2^S * q < 2^S * n → q < n
  have hmul_lt : 2 ^ v2SumExact W n * syracuseExact^[W] n <
      2 ^ v2SumExact W n * n := by omega
  exact Nat.lt_of_mul_lt_mul_left hmul_lt

/-- The correction term is always nonneg (trivially, since it's a Nat). -/
lemma correctionTerm_nonneg (W n : ℕ) : 0 ≤ correctionTerm W n := Nat.zero_le _

/-! ### §5.10 The Correction Term Bound (Conservation Analysis)

**Key structural theorem**: `correctionTerm W n ≤ (3^W - 2^W) · 2^(v2SumExact W n - W)`

This bound is:
- **n-independent**: the bound depends only on W and the v₂ sum, not on n directly
- **Tight**: equality holds in the worst case (all v₂ = 1, giving S = W)
- **Proved by induction** using only `v₂ ≥ 1` at each step

**Consequence**: Combined with `exact_orbit_formula`, for any orbit with
`3^W < 2^S` (negative drift), the orbit shrinks whenever
`n > ((3/2)^W - 1) / (1 - 3^W/2^S)`.

This is a **finite, computable threshold**: for n above the threshold, orbit
shrinkage is guaranteed; below the threshold, computational verification suffices.

**Computational verification**:
- W=10, S=16: threshold n > 572  (covers all n ≥ 573 with v₂ sum ≥ 16)
- W=10, S=20: threshold n > 60   (strong contraction regime)
- W=22, S=35: threshold n > 86293
Verified tight at 1.0000 for all-v₂=1 bad streaks (n = 2^K−1). -/

/-- **Correction term bound**: ε ≤ (3^W − 2^W) · 2^(S − W) where S = v2SumExact W n.

    Proof by induction on W:
    - Base (W=0): ε = 0 ≤ 0 = (1−1)·anything. ✓
    - Step: ε_{W+1} = 3^W + 2^v₁ · ε_W(f n)
      By IH: ε_W(f n) ≤ (3^W − 2^W) · 2^(S'−W) where S' = v2SumExact W (f n)
      So: ε_{W+1} ≤ 3^W + (3^W − 2^W) · 2^(v₁+S'−W)
      Need: ≤ (3^(W+1) − 2^(W+1)) · 2^(v₁+S'−W−1)
      Simplifies to: 1 ≤ 2^(v₁+S'−W−1), which holds since v₁ ≥ 1 and S' ≥ W. ✓

    ✅ PROVEN -/
lemma correctionTerm_bound (W n : ℕ) (hn : n % 2 = 1) :
    correctionTerm W n * 2 ^ W ≤ (3 ^ W - 2 ^ W) * 2 ^ v2SumExact W n := by
  induction W generalizing n with
  | zero => simp [correctionTerm, v2SumExact]
  | succ W ih =>
    simp only [correctionTerm, v2SumExact]
    set v1 := v2 (3 * n + 1)
    set fn := syracuseExact n
    set S' := v2SumExact W fn
    have hfn_odd : fn % 2 = 1 := syracuseExact_odd hn
    have hih := ih fn hfn_odd
    -- hih : correctionTerm W fn * 2^W ≤ (3^W - 2^W) * 2^S'
    have hv1 : 1 ≤ v1 := v2_odd_ge_one n hn
    have hS'W : W ≤ S' := v2SumExact_ge_W W fn hfn_odd
    -- Goal: (3^W + 2^v1 * correctionTerm W fn) * 2^(W+1) ≤ (3^(W+1) - 2^(W+1)) * 2^(v1+S')
    -- Strategy: expand, use IH, reduce to 3^W * 2^(W+1) ≤ 3^W * 2^(v1+S')
    -- i.e., W+1 ≤ v1+S', which holds since v1 ≥ 1 and S' ≥ W.
    have hexp : W + 1 ≤ v1 + S' := by omega
    -- 2^(W+1) ≤ 2^(v1+S')
    have hpow : 2 ^ (W + 1) ≤ 2 ^ (v1 + S') := Nat.pow_le_pow_right (by norm_num) hexp
    -- 3^W ≥ 2^W (for the subtraction to be meaningful)
    have h3ge2 : 2 ^ W ≤ 3 ^ W := Nat.pow_le_pow_left (by norm_num) W
    have h3ge2' : 2 ^ (W + 1) ≤ 3 ^ (W + 1) := Nat.pow_le_pow_left (by norm_num) (W + 1)
    -- Use zify to lift to ℤ where subtraction is clean and ring identities hold.
    -- In ℤ: (3^(W+1) - 2^(W+1)) * 2^(v1+S') = (3*3^W - 2*2^W) * 2^(v1+S')
    --      = 3^W*2^(v1+S') + (3^W-2^W)*2*2^(v1+S')
    -- LHS = 3^W*2^(W+1) + ct*2^W*2^(v1+1)
    --     ≤ 3^W*2^(v1+S') + (3^W-2^W)*2^S'*2^(v1+1)  [by hpow for first term, IH for second]
    --     = 3^W*2^(v1+S') + (3^W-2^W)*2*2^(v1+S')    [rearranging 2^S'*2^(v1+1)=2*2^(v1+S')]
    --     = RHS ✓
    zify [h3ge2, h3ge2'] at *
    -- hih  : (ct:ℤ)*2^W ≤ (3^W - 2^W)*2^S'
    -- hpow : (2:ℤ)^(W+1) ≤ 2^(v1+S')
    -- h3ge2  : (2:ℤ)^W ≤ 3^W
    -- h3ge2' : (2:ℤ)^(W+1) ≤ 3^(W+1)
    -- Goal: ((3:ℤ)^W + 2^v1 * ct) * 2^(W+1) ≤ (3^(W+1) - 2^(W+1)) * 2^(v1+S')
    have hct_scaled : (correctionTerm W fn : ℤ) * 2 ^ W * 2 ^ (v1 + 1) ≤
        (3 ^ W - 2 ^ W) * 2 ^ S' * 2 ^ (v1 + 1) :=
      mul_le_mul_of_nonneg_right hih (by positivity)
    have h3W_scaled : (3 : ℤ) ^ W * 2 ^ (W + 1) ≤ 3 ^ W * 2 ^ (v1 + S') :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    -- In ℤ, all ring identities work:
    -- (3^W - 2^W)*2^S'*2^(v1+1) = (3^W - 2^W)*2*2^(v1+S')
    have hrearrange : ((3 : ℤ) ^ W - 2 ^ W) * 2 ^ S' * 2 ^ (v1 + 1) =
        (3 ^ W - 2 ^ W) * 2 * 2 ^ (v1 + S') := by
      rw [pow_add, pow_add]; ring
    -- (3^(W+1) - 2^(W+1)) * 2^(v1+S') = 3^W*2^(v1+S') + (3^W - 2^W)*2*2^(v1+S')
    have hrhs_eq : ((3 : ℤ) ^ (W + 1) - 2 ^ (W + 1)) * 2 ^ (v1 + S') =
        3 ^ W * 2 ^ (v1 + S') + (3 ^ W - 2 ^ W) * 2 * 2 ^ (v1 + S') := by
      rw [pow_succ 3 W, pow_succ 2 W]; ring
    -- ((3:ℤ)^W + 2^v1 * ct) * 2^(W+1) = 3^W*2^(W+1) + ct*2^W*2^(v1+1)
    have hexpand : ((3 : ℤ) ^ W + 2 ^ v1 * (correctionTerm W fn : ℤ)) * 2 ^ (W + 1) =
        3 ^ W * 2 ^ (W + 1) + (correctionTerm W fn : ℤ) * 2 ^ W * 2 ^ (v1 + 1) := by
      rw [pow_add]; ring
    rw [hexpand, hrhs_eq]
    -- ct*2^W*2^(v1+1) ≤ (3^W-2^W)*2*2^(v1+S')
    have step1 : (correctionTerm W fn : ℤ) * 2 ^ W * 2 ^ (v1 + 1) ≤
        (3 ^ W - 2 ^ W) * 2 * 2 ^ (v1 + S') := by linarith [hrearrange]
    linarith

/-! ### Solenoid Coherence: Why the Bridge Fails

**The original `solenoid_coherence_W_steps` was FALSE as stated.**

The lemma claimed: `∀ W m n, v2Sum m W (n%m) ≤ v2SumExact W n`.

**Counterexample**: m = 8, n = 13, W = 1.
- `v2Sum 8 1 (13%8) = v2Sum 8 1 5 = v2Fuel 64 (3·5+1) = v2Fuel 64 16 = 4`
- `v2SumExact 1 13 = v2(3·13+1) = v2(40) = 3`
- 4 ≤ 3 is false. ∎

**Root cause**: `v2Fuel 64 (3r+1)` computes the exact v₂ of the *number* 3r+1,
which can exceed the 2-adic precision v₂(m) of the modulus. When v₂(3r+1) > v₂(m),
integers n ≡ r (mod m) can have v₂(3n+1) < v₂(3r+1).

**Impact on certificates**: The contraction certificates overcount. `contraction_k3`
claims `v2Sum 104 10 r ≥ 16` for all odd r, but `v2SumExact 10 n` can be as low
as 10 (at n = 2047 = 2¹¹−1, which has 10 consecutive v₂=1 steps).

**No fixed W gives universal contraction**: n = 2^K−1 creates bad streaks of K−1
consecutive v₂=1 steps: `v2SumExact W (2^K−1) = W` for W ≤ K−1. Since 3^W > 2^W,
no fixed-W certificate can handle all n. The existential statement
`∀ n, ∃ W, syracuseExact^[W] n < n` is equivalent to the Collatz conjecture.

**Orbit divergence**: Even with a capped v₂, the W-step bridge fails because
the modular orbit (`syracuseMod m`) and integer orbit (`syracuseExact`) can diverge.
When v₂(3r+1) ≠ v₂(3n+1), different divisions by powers of 2 send the orbits
to different residues. After the first disagreement, the orbits may never resynchronize.
For m = 104, the orbit diverges by step 3 for n = 63 (integer orbit visits 215 ≡ 7 mod 104,
but modular orbit visits 59 — different residues).

**What IS true (one-step, capped)**: if v = min(v₂(3r+1), v₂(m)) and r = n%m,
then 2^v ∣ (3n+1). This is because 2^v ∣ (3r+1), 2^v ∣ m, and m ∣ (n−r). -/

/-! ### §7.2 Equivalence of `orbit_shrinks_W_steps` and the Collatz Conjecture

`orbit_shrinks_W_steps` states: ∀ odd n > 1, ∃ W, syracuseExact^[W] n < n.

**(⇒)** If this holds, then by well-founded descent on ℕ, every odd number eventually
reaches 1. This is formalized as `orbit_reaches_one_conditional`.

**(⇐)** If the Collatz conjecture holds, then for odd n > 1 the orbit reaches 1;
since 1 < n, the orbit passes through some value < n, giving the required W.

The v₂ ≥ 2 case (one step shrinks) and small cases (n < 11) are formalized.
The remaining case (v₂ = 1, n ≥ 11) requires showing that every sufficiently
long orbit segment has enough large-v₂ steps to overcome the (3/2)-expansion
from the v₂ = 1 steps. No fixed window W works universally because n = 2^K − 1
creates K − 1 consecutive v₂ = 1 steps (verified computationally for K up to 24;
e.g., n = 16777215 = 2²⁴−1 needs W = 71 to shrink).  -/

/-! ## Section 8: Algebraic Bad-Streak Bound (Lemma A)

**Why `unsafe_splits` would be wrong here**:
`unsafe_splits` tracks 2^k | 3r+1 (tower-level divisibility at a single node).
Bad streaks track v₂=1 at CONSECUTIVE orbit steps — different 2-adic invariant.
These are orthogonal concepts; `unsafe_splits` doesn't help with streak bounds.

**The structural result** (Lemma A):
If m = 13·2^k, then a bad streak of ≥ k consecutive steps starting from r forces
2^k | r+1 (i.e., r ≡ -1 mod 2^k). This reduces checking max-streak ≤ k+1 to
verifying at most 13 specific candidates — feasible by native_decide for each k.
-/

/-- Iterated Syracuse step: apply `syracuseMod m` exactly `i` times starting from `r`. -/
def iterSyracuse (m : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | i + 1, r => syracuseMod m (iterSyracuse m i r)

/-- `iterSyracuse m i (syracuseMod m r) = iterSyracuse m (i+1) r`. -/
lemma iterSyracuse_succ (m i r : ℕ) :
    iterSyracuse m i (syracuseMod m r) = iterSyracuse m (i + 1) r := by
  induction i with
  | zero => rfl
  | succ i ih => exact congrArg (syracuseMod m) ih

/-- **Additivity of iterSyracuse**: composing a steps then b steps = a+b steps. -/
lemma iterSyracuse_add (m a b r : ℕ) :
    iterSyracuse m (a + b) r = iterSyracuse m b (iterSyracuse m a r) := by
  induction b with
  | zero => simp [iterSyracuse]
  | succ b ih =>
    -- After rewrites, remaining goal is definitionally equal: rfl closes it
    rw [Nat.add_succ, iterSyracuse, ih]
    rfl

/-- **Period stability**: if iterSyracuse m P r = r, then iterSyracuse m (P*q) r = r. -/
lemma iterSyracuse_mul_period (m P q r : ℕ) (hperiod : iterSyracuse m P r = r) :
    iterSyracuse m (P * q) r = r := by
  induction q with
  | zero => simp [iterSyracuse]
  | succ q ih =>
    rw [Nat.mul_succ, iterSyracuse_add, ih, hperiod]

open UFRF.CollatzSolenoid in
/-- **v2Sum additivity**: running a+b steps = a steps then b steps from the result.
    The key bridge between single-period v2Sum and multi-period v2Sum. -/
lemma v2Sum_add (m a b r : ℕ) :
    v2Sum m (a + b) r = v2Sum m a r + v2Sum m b (iterSyracuse m a r) := by
  induction a generalizing r with
  | zero => simp [v2Sum, iterSyracuse]
  | succ a ih =>
    rw [show Nat.succ a + b = (a + b) + 1 by omega]
    simp only [v2Sum, ih (syracuseMod m r), iterSyracuse_succ]
    omega

open UFRF.CollatzSolenoid in
/-- **v2Sum over q periods**: if the orbit has period P, then v2Sum over P·q steps
    is exactly q times the per-period sum. -/
lemma v2Sum_period_additive (m P q r : ℕ) (hperiod : iterSyracuse m P r = r) :
    v2Sum m (P * q) r = q * v2Sum m P r := by
  induction q with
  | zero => simp [v2Sum]
  | succ q ih =>
    rw [Nat.mul_succ, v2Sum_add, iterSyracuse_mul_period m P q r hperiod, ih]
    -- Goal: q * v2Sum m P r + v2Sum m P r = (q + 1) * v2Sum m P r
    ring

/-- v2Fuel 64 n = 1 implies n ≡ 2 (mod 4), i.e. n = 2·(odd). -/
private lemma v2Fuel_one_mod4 {n : ℕ} (hv : v2Fuel 64 n = 1) : n % 4 = 2 := by
  cases n with
  | zero => simp [v2Fuel] at hv
  | succ n =>
    have hv64 : v2Fuel 64 (n + 1) = v2Fuel (63 + 1) (n + 1) := rfl
    rw [hv64, v2Fuel_succ_succ] at hv
    by_cases hev : (n + 1) % 2 = 0
    · rw [if_pos hev] at hv
      -- hv : 1 + v2Fuel 63 ((n+1)/2) = 1, so v2Fuel 63 ((n+1)/2) = 0
      have hv63 : v2Fuel 63 ((n + 1) / 2) = 0 := by omega
      cases h2 : ((n + 1) / 2) with
      | zero => omega
      | succ k =>
        have hv63' : v2Fuel 63 (k + 1) = v2Fuel (62 + 1) (k + 1) := rfl
        rw [h2, hv63', v2Fuel_succ_succ] at hv63
        by_cases hev2 : (k + 1) % 2 = 0
        · rw [if_pos hev2] at hv63; omega
        · rw [if_neg hev2] at hv63  -- hv63 : 0 = 0 ✓
          -- (k+1)%2≠0 → (k+1)%2=1; h2 : (n+1)/2=k+1; hev : (n+1)%2=0 → (n+1)%4=2
          omega
    · rw [if_neg hev] at hv; omega

/-- When v2Fuel 64 (3r+1) = 1, `syracuseMod m r = (3r+1)/2 % m`. -/
private lemma syracuseMod_v2_one {m r : ℕ} (hv : v2Fuel 64 (3 * r + 1) = 1) :
    syracuseMod m r = (3 * r + 1) / 2 % m := by
  simp [syracuseMod, hv]

/-- If `a ∣ m` then `n % m % a = n % a`. -/
private lemma mod_dvd_mod (n : ℕ) {a m : ℕ} (h : a ∣ m) : n % m % a = n % a :=
  Nat.mod_mod_of_dvd n h

/-- **Lemma A** (Bad-Streak → 2-Adic Constraint):
    If the Syracuse orbit from r (mod m) has L consecutive bad steps (all v₂=1),
    and 2^L ∣ m, then 2^L ∣ r+1 (equivalently: r ≡ -1 mod 2^L).

    The proof goes by induction on L:
    - Base (L=0): trivial.
    - Step: by IH, r₁ = syracuseMod m r satisfies 2^L ∣ r₁+1.
      From v₂(3r+1)=1: (3r+1)/2+1 = (3r+3)/2, so 2^(L+1) ∣ 3(r+1).
      Since gcd(3, 2^(L+1))=1: 2^(L+1) ∣ r+1.

    This reduces "does any residue mod 13·2^k have streak ≥ k+1?" to checking
    only residues with 2^k ∣ r+1 — at most 13 candidates. -/
theorem streak_requires_dvd (m L : ℕ) (hm : 2 ^ L ∣ m) :
    ∀ r : ℕ, r % 2 = 1 →
      (∀ i < L, v2Fuel 64 (3 * iterSyracuse m i r + 1) = 1) →
      2 ^ L ∣ r + 1 := by
  induction L with
  | zero => intro r _ _; simp
  | succ L ih =>
    intro r hr_odd hstreak
    have hm_L : 2 ^ L ∣ m := dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_succ L)) hm
    have hv0 : v2Fuel 64 (3 * r + 1) = 1 := hstreak 0 (Nat.zero_lt_succ L)
    -- Tail: the L steps from r₁ = syracuseMod m r
    have tail_streak : ∀ i < L, v2Fuel 64 (3 * iterSyracuse m i (syracuseMod m r) + 1) = 1 :=
      fun i hi => by rw [iterSyracuse_succ]; exact hstreak (i + 1) (Nat.succ_lt_succ hi)
    -- r₁ is odd: since v₂(3r+1)=1, we have 3r+1≡2 mod 4, so (3r+1)/2 is odd
    have h2m : 2 ∣ m := dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero L)) hm
    have r1_odd : (syracuseMod m r) % 2 = 1 := by
      rw [syracuseMod_v2_one hv0, mod_dvd_mod _ h2m]
      have := v2Fuel_one_mod4 hv0; omega
    -- IH: 2^L ∣ (syracuseMod m r) + 1
    have ih_res : 2 ^ L ∣ (syracuseMod m r) + 1 := ih hm_L _ r1_odd tail_streak
    -- Deduce 2^L ∣ (3r+1)/2 + 1 (mod reduction preserves residue mod 2^L)
    have hdvd_half : 2 ^ L ∣ (3 * r + 1) / 2 + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero] at ih_res ⊢
      rw [syracuseMod_v2_one hv0] at ih_res
      have hred : (3 * r + 1) / 2 % m % 2 ^ L = (3 * r + 1) / 2 % 2 ^ L :=
        mod_dvd_mod _ hm_L
      -- Bridge: (X%m+1)%2^L = (X+1)%2^L, using hred to equate X%m≡X (mod 2^L)
      have hkey : ((3 * r + 1) / 2 % m + 1) % 2 ^ L = ((3 * r + 1) / 2 + 1) % 2 ^ L := by
        have h1 := Nat.add_mod ((3 * r + 1) / 2 % m) 1 (2 ^ L)
        have h2 := Nat.add_mod ((3 * r + 1) / 2) 1 (2 ^ L)
        rw [h1, hred, ← h2]
      linarith
    -- 2^(L+1) ∣ 3(r+1): write 3r+1=2h, then 3(r+1)=2(h+1), and 2^L∣h+1
    have hdvd2 : 2 ∣ 3 * r + 1 := by have := v2Fuel_one_mod4 hv0; omega
    obtain ⟨h, hh⟩ := hdvd2
    have heq_half : (3 * r + 1) / 2 = h := by omega
    obtain ⟨c, hc⟩ := hdvd_half
    rw [heq_half] at hc
    have hdvd_3r1 : 2 ^ (L + 1) ∣ 3 * (r + 1) := by
      refine ⟨c, ?_⟩
      calc 3 * (r + 1) = (3 * r + 1) + 2 := by ring
        _ = 2 * h + 2                     := by linarith
        _ = 2 * (h + 1)                   := by ring
        _ = 2 * (2 ^ L * c)               := by rw [← hc]
        _ = 2 ^ (L + 1) * c               := by ring
    -- Coprimality: gcd(2^(L+1), 3) = 1 → 2^(L+1) ∣ r+1
    have hcop : Nat.Coprime (2 ^ (L + 1)) 3 :=
      Nat.Coprime.pow_left (L + 1) (by decide)
    exact hcop.dvd_of_dvd_mul_right (by rw [mul_comm]; exact hdvd_3r1)

/-- Corollary: in ZMod(13·2^k), any bad streak of length ≥ k must start from
    a residue with 2^k ∣ r+1, i.e., r ∈ {2^k-1, 2·2^k-1, …, 13·2^k-1}.
    At most 13 candidates to check by native_decide for each specific k. -/
theorem streak_reduces_to_13_candidates (k : ℕ) (r : ℕ)
    (_hr_lt : r < 13 * 2 ^ k) (hr_odd : r % 2 = 1)
    (hstreak : ∀ i < k, v2Fuel 64 (3 * iterSyracuse (13 * 2 ^ k) i r + 1) = 1) :
    2 ^ k ∣ r + 1 :=
  streak_requires_dvd (13 * 2 ^ k) k (dvd_mul_left (2 ^ k) 13) r hr_odd hstreak

/-! ## Section 9: Max-Streak Bound via iterSyracuse (k=3..12)

Contraction for k=3..12 is handled by `contraction_at_scales_3_to_12` (Section 7).
This section adds the complementary `max_bad_streak` results in `iterSyracuse` form,
connecting the computational certificates to the algebraic Lemma A infrastructure.

### Open frontiers

1. `contraction_at_all_scales` for k > 12: the theorem is FALSE for k=13.
   See Section 10 for the algebraic obstruction (period-14 orbit at r=8191,
   avg v₂ ≈ 1.143 < log₂(3)). A different argument is needed for k≥13.

2. `collatz_convergence_from_concurrent_scales`: connecting modular safe-orbits
   to actual integer arithmetic (open).
-/

/-- **Max bad streak via iterSyracuse** (k=3..12):
    At modulus 13·2^k, no k+2 consecutive bad steps exist.
    Verified by native_decide for each k ∈ {3,...,12}.

    Key: Lemma A (`streak_requires_dvd`) algebraically reduces this to checking
    13 families r = t·2^k−1 (t=1..13). Of these, only t∈{4,8,10} reach k+1 steps;
    none reaches k+2. This is the tight structural bound.

    ✅ PROVEN (k=3..12) -/
theorem max_bad_streak_iterated (k : ℕ) (hk3 : 3 ≤ k) (hk12 : k ≤ 12) :
    ∀ r : Fin (13 * 2 ^ (k - 1)),
      ¬ (∀ j : Fin (k + 2),
          v2Fuel 64 (3 * iterSyracuse (13 * 2 ^ k) j.val (2 * r.val + 1) + 1) = 1) := by
  interval_cases k <;> native_decide

/-- **Streak bound implies finite candidates**: combining `streak_reduces_to_13_candidates`
    with `max_bad_streak_iterated` gives: for k ∈ {3,...,12}, the ONLY odd residues
    that can achieve a streak of EXACTLY k+1 are among the 13 families r = t·2^k−1. -/
theorem max_streak_families_k3_12 (k : ℕ) (_hk3 : 3 ≤ k) (_hk12 : k ≤ 12) (r : ℕ)
    (hr_lt : r < 13 * 2 ^ k) (hr_odd : r % 2 = 1)
    (hstreak : ∀ i < k + 1, v2Fuel 64 (3 * iterSyracuse (13 * 2 ^ k) i r + 1) = 1) :
    2 ^ k ∣ r + 1 :=
  streak_reduces_to_13_candidates k r hr_lt hr_odd
    (fun i hi => hstreak i (by omega))

/-! ## Section 10: The k≥13 Obstruction

`contraction_at_all_scales` is **FALSE** for k = 13.

### The counterexample

The residue r = 8191 = 2^13 − 1 (the t=1 family: r = 1·2^13 − 1) at modulus
13·2^13 = 106496 has a **period-14 orbit** under iterSyracuse. Over one full period:
  - 12 bad steps (v₂ = 1 each)
  - 2 good steps (v₂ = 2 each)
  - Total v₂ sum = 12·1 + 2·2 = 16

The average v₂ per step is 16/14 ≈ 1.143, which is **below** log₂(3) ≈ 1.585.
This means the orbit GROWS on average — no window W can make it contract.

### Why k = 11, 12 avoid this obstruction

At modulus 13·2^11 = 26624, the orbit from r = 8191 hits a modular reduction at step 4
(62207 mod 26624 = 8959), breaking the period-14 structure. The resulting average v₂
rises above 1.585, restoring contractivity. At k=12 the break occurs at step 5.
At k=13 the orbit completes a full period of 14 before any break occurs.

### Integer certificate

The key inequalities are:
  1000 · 16 = 16000 < 22190 = 14 · 1585   (sub-threshold per-period drift)

For any W = 14·q steps, v2Sum 106496 (14·q) 8191 = 16·q, so:
  1000 · 16·q = 16000·q < 22190·q = (14·q) · 1585 = W · 1585.

No S can satisfy both `v2Sum ≥ S` and `1000·S > W·1585` simultaneously.
-/

/-- The orbit of r=8191 at modulus 13·2^13=106496 has period exactly 14.
    ✅ PROVEN -/
theorem orbit_8191_period14 :
    iterSyracuse 106496 14 8191 = 8191 := by native_decide

open UFRF.CollatzSolenoid in
/-- The total v₂ accumulated over one period (14 steps) is 16.
    Breakdown: 12 steps with v₂=1, 2 steps with v₂=2.  ✅ PROVEN -/
theorem v2sum_period14_8191_k13 :
    v2Sum 106496 14 8191 = 16 := by native_decide

/-- The per-period drift is sub-threshold: 1000·16 < 14·1585.
    Equivalently: avg v₂ = 16/14 ≈ 1.143 < 1.585 ≈ log₂(3).  ✅ PROVEN -/
theorem period14_drift_positive_k13 : 1000 * 16 < 14 * 1585 := by norm_num

open UFRF.CollatzSolenoid in
/-- Consequence: for W = 14·q steps (q > 0), the contraction condition fails for r=8191.
    v2Sum 106496 (14·q) 8191 = 16·q  (by v2Sum_period_additive + orbit_8191_period14)
    and 1000·16·q = 16000·q < 22190·q = (14·q)·1585.  ✅ PROVEN -/
theorem contraction_impossible_at_k13_r8191 (q : ℕ) (hq : 0 < q) :
    1000 * v2Sum 106496 (14 * q) 8191 < (14 * q) * 1585 := by
  rw [v2Sum_period_additive 106496 14 q 8191 orbit_8191_period14,
      v2sum_period14_8191_k13]
  -- Goal: 1000 * (q * 16) < 14 * q * 1585  ↔  16000·q < 22190·q  (holds for q > 0)
  omega

/-! ## Section 11: Modular Obstruction Killing (Concurrent Resolution)

### The Obstruction Mortality Phenomenon

The period-14 divergent cycle at k=13 (modulus 106496) is the ONLY divergent modular
cycle found in the range k=3..20. Computationally verified:
- k=3..12: no divergent cycles (contraction certificates hold)
- k=13: ONE divergent cycle (period 14, avg v₂ = 16/14 ≈ 1.14 < log₂3)
- k=14..20: no divergent cycles (killed at k=14; only convergent cycles remain)
- k=25 (next resonance at ord₁₃(2)+13): no divergent cycle found

### The Killing Mechanism

At k=14 (modulus 212992), the period-14 cycle from k=13 BREAKS at step 6:
- At k=13: syracuseMod(106496, 93311) = 139967 mod 106496 = 33471 (wraps → cycle closes)
- At k=14: syracuseMod(212992, 93311) = 139967 mod 212992 = 139967 (no wrap → cycle breaks)

The value 139967 = 33471 + 106496 is the UPPER LIFT of 33471 in the splitting tree.
At k=13, modular reduction collapsed this to 33471 (creating the cycle artifact).
At k=14, the finer modulus reveals the true orbit escapes the cycle.

This is the **concurrent resolution structure** in action: what appears as a closed cycle
at scale k is revealed to be an open path at scale k+1. The "cycle" was never real —
it was an artifact of insufficient modular precision.

### Theorem: The k=13 Cycle Does Not Survive at k=14

The key fact: `iterSyracuse 212992 14 8191 ≠ 8191`. That is, starting from 8191
at the finer modulus 13·2^14, the orbit does NOT return to 8191 after 14 steps.
The cycle is killed. -/

/-- At modulus 13·2^14 = 212992, the orbit from 8191 does NOT have period 14.
    The period-14 cycle from k=13 is killed by the finer precision at k=14.
    ✅ PROVEN -/
theorem cycle_killed_at_k14 :
    iterSyracuse 212992 14 8191 ≠ 8191 := by native_decide

/-- The specific breaking step: at k=14, syracuseMod maps 93311 to 139967 (not 33471).
    139967 = 33471 + 106496 is the upper lift, revealing the cycle was a modular artifact.
    ✅ PROVEN -/
theorem breaking_step_k14 :
    syracuseMod 212992 93311 = 139967 := by native_decide

/-- At k=13, the same step wraps: 139967 mod 106496 = 33471, creating the cycle artifact.
    ✅ PROVEN -/
theorem wrapping_step_k13 :
    syracuseMod 106496 93311 = 33471 := by native_decide

/-- The upper lift relationship: 139967 = 33471 + 13·2^13.
    This shows the breaking step picks the upper lift in the splitting tree.
    ✅ PROVEN -/
theorem upper_lift_at_breaking_step :
    (139967 : ℕ) = 33471 + 13 * 2 ^ 13 := by norm_num

/-- In the integer world, 8191 (= 2^13 - 1) DOES shrink within 27 steps.
    The modular divergent cycle is purely an artifact — the true orbit contracts.
    ✅ PROVEN -/
theorem integer_8191_shrinks :
    ∃ W : ℕ, 0 < W ∧ syracuseExact^[W] 8191 < 8191 :=
  ⟨27, by norm_num, by native_decide⟩

end UFRF.ConcurrentScales
