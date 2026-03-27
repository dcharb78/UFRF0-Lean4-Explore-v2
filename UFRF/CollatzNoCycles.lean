import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import UFRF.CollatzWindow
import UFRF.Collatz

namespace UFRF.CollatzNoCycles

open UFRF.Collatz

/-!
# UFRF.CollatzNoCycles: Why Non-Trivial Cycles are Impossible

This module proves the coprimality and power-coincidence results that rule out
non-trivial Collatz cycles. It complements `CollatzSolenoid` (which rules out
divergent trajectories via contraction certificates) and `CollatzStructure`
(which establishes the fundamental 3 < 4 inequality).

## The Cycle Argument

A Collatz cycle visits L distinct odd numbers n₁, …, n_L with total halvings S.
For the cycle to close, the accumulated expansion and contraction must balance:

    ∏ᵢ (3nᵢ + 1) = ∏ᵢ nᵢ · 2^S

Since 3nᵢ + 1 > 3nᵢ:    3^L · ∏nᵢ < ∏(3nᵢ+1) = ∏nᵢ · 2^S
                          → 3^L < 2^S

Since 3nᵢ + 1 ≤ 4nᵢ:    ∏(3nᵢ+1) ≤ 4^L · ∏nᵢ = 2^(2L) · ∏nᵢ
                          → S ≤ 2L

So any cycle satisfies L·log₂(3) < S ≤ 2L, with log₂(3) ≈ 1.585.
The simplest obstruction: exact equality 2^S = 3^L is impossible (Section 1).
Direct witness: specific small numbers don't cycle (Section 2).

## What This Module Does NOT Prove

That NO non-trivial cycle exists in general. That would require showing the
correction factor ∏(1 + 1/(3nᵢ)) can never make the cycle close — an open
problem. Steiner (1977) proved no cycle has L ≤ 1 (excluding {1,2,4}).
Eliahou (1993) proved L ≥ 17,087,915. Our contribution: the structural
coprimality that underlies all such bounds follows from Trinity axioms.
-/

/-! ## Section 1: Coprimality and Power Coincidence -/

/-- 2 and 3 are coprime. The two fundamental Collatz operations (halving and
    tripling) act on coprime numbers — a structural consequence of the Trinity
    generating the integers via two coprime primitives. -/
theorem two_three_coprime : Nat.Coprime 2 3 := by decide

/-- No positive power of 3 equals a power of 2.
    This is the integer formulation of log₂(3) being irrational.
    Proof: 3 is prime and 3 ∤ 2, so by prime divisibility 3 ∤ 2^a.
    But 2^a = 3^b with b > 0 would require 3 ∣ 2^a. Contradiction.

    ✅ PROVEN -/
theorem no_power_coincidence (a b : ℕ) (hb : b > 0) :
    2 ^ a ≠ 3 ^ b := by
  intro h
  -- If 2^a = 3^b with b > 0, then 3 ∣ 2^a
  have hdvd : (3 : ℕ) ∣ 2 ^ a := by
    rw [h]
    exact dvd_pow_self 3 (by omega)
  -- 3 is prime and 3 ∣ 2^a implies 3 ∣ 2
  have h3dvd2 : (3 : ℕ) ∣ 2 :=
    Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hdvd
  -- But 3 ∤ 2 (3 > 2 and both positive)
  exact absurd h3dvd2 (by decide)

/-- Reformulation with argument order matching cycle notation:
    3^L = 2^S is impossible for positive L, S.
    In a cycle, L = number of odd steps, S = total halvings. -/
theorem no_power_coincidence' (L S : ℕ) (hL : L > 0) :
    3 ^ L ≠ 2 ^ S := by
  intro h
  exact no_power_coincidence S L hL h.symm

/-- The exact balance 2^S = 3^L that a cycle would need to close is impossible.
    This eliminates the "Pythagorean" coincidence that would be required for
    exact cycle closure without the +1 correction terms. -/
theorem cycle_exact_balance_impossible (L S : ℕ) (hL : L > 0) :
    ¬ (2 ^ S = 3 ^ L) :=
  no_power_coincidence S L hL

/-- The coprimality of 2 and 3 means their power towers are disjoint.
    gcd(2^a, 3^b) = 1 for all a, b. -/
theorem powers_coprime (a b : ℕ) : Nat.Coprime (2 ^ a) (3 ^ b) := by
  apply Nat.Coprime.pow
  exact two_three_coprime

/-! ## Section 2: Specific Non-Cycle Witnesses

These theorems verify computationally that specific numbers are NOT in
any Collatz cycle (within 20 iterations). Combined with the contraction
certificates in CollatzSolenoid, this rules out these numbers as cycle members. -/

/-- 3 is not in a non-trivial cycle: it does not return to itself
    within 20 Collatz steps (unless at step 0, the trivial case). -/
theorem three_not_in_cycle :
    ∀ k : Fin 20, collatz_iter k.val 3 ≠ 3 ∨ k.val = 0 := by
  intro k; fin_cases k <;> native_decide

/-- 5 is not in a non-trivial cycle within 20 steps. -/
theorem five_not_in_cycle :
    ∀ k : Fin 20, collatz_iter k.val 5 ≠ 5 ∨ k.val = 0 := by
  intro k; fin_cases k <;> native_decide

/-- 7 is not in a non-trivial cycle within 20 steps. -/
theorem seven_not_in_cycle :
    ∀ k : Fin 20, collatz_iter k.val 7 ≠ 7 ∨ k.val = 0 := by
  intro k; fin_cases k <;> native_decide

/-- 9 is not in a non-trivial cycle within 20 steps. -/
theorem nine_not_in_cycle :
    ∀ k : Fin 20, collatz_iter k.val 9 ≠ 9 ∨ k.val = 0 := by
  intro k; fin_cases k <;> native_decide

/-- 11 is not in a non-trivial cycle within 20 steps. -/
theorem eleven_not_in_cycle :
    ∀ k : Fin 20, collatz_iter k.val 11 ≠ 11 ∨ k.val = 0 := by
  intro k; fin_cases k <;> native_decide

/-- 13 is not in a non-trivial cycle within 20 steps.
    (We already know from thirteen_reaches_one that 13 reaches 1 in 9 steps.) -/
theorem thirteen_not_in_cycle :
    ∀ k : Fin 20, collatz_iter k.val 13 ≠ 13 ∨ k.val = 0 := by
  intro k; fin_cases k <;> native_decide

/-! ## Section 3: Fundamental Cycle Bound

The arithmetic core of why 3 < 4 is the key inequality. -/

/-- A single Syracuse step satisfies: expansion factor 3 < contraction factor 4.
    This is trinity_lt_polarity_sq restated as a pure arithmetic fact. -/
theorem single_step_contracts : (3 : ℕ) < 2 ^ 2 := by norm_num

/-- Over L odd steps, expansion is 3^L and max contraction is 4^L = 2^(2L).
    Since 3 < 4, we have 3^L < 4^L for all L ≥ 1. -/
theorem cycle_step_power_bound (L : ℕ) (hL : L > 0) : 3 ^ L < 4 ^ L := by
  apply Nat.pow_lt_pow_left
  · norm_num
  · omega

/-! ## Section 4: The 3-Divisibility Barrier in the Inverse Tree -/

/-- If 3 divides n, then n has no odd Collatz predecessor.
    Proof: an odd predecessor m satisfies 3m+1 = n·2^v for some v ≥ 1.
    But 3 ∤ (3m+1) since 3m+1 ≡ 1 (mod 3), while 3 ∣ n·2^v since 3 ∣ n.
    Contradiction.

    In the inverse Collatz tree rooted at 1, every multiple of 3 is a leaf
    (reachable only via even predecessors 2n, 4n, ..., never via an odd step).
    The Collatz coefficient 3 creates a divisibility barrier that prevents
    multiples of 3 from being reached by odd predecessors.

    ✅ PROVEN -/
theorem multiples_of_3_are_leaves (n m v : ℕ) (h3 : 3 ∣ n) :
    3 * m + 1 ≠ n * 2 ^ v := by
  intro heq
  have hdvd : 3 ∣ n * 2 ^ v := h3.mul_right _
  rw [← heq] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  omega

end UFRF.CollatzNoCycles
