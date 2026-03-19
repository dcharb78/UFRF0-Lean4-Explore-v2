import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import UFRF.Constants

/-!
# UFRF.PrimeSemantics

This module separates three different notions that were previously
described in prose more often than in code:

1. `Nat.Prime` / `is_standard_prime` on natural numbers
2. `is_ufrf_prime` on natural numbers (the repo's custom checkpoint predicate)
3. Structural positions on the 13-cycle, modeled in `ZMod 13`

The purpose is not to collapse these notions into one "master prime"
definition, but to give each notion an explicit type and exact finite
classification theorem.
-/

namespace UFRF.PrimeSemantics

open UFRF.Constants

/-- Standard arithmetic primality on natural numbers. -/
abbrev is_standard_prime (n : ℕ) : Prop := Nat.Prime n

/--
The distinguished natural numbers used as cycle-prime checkpoints in the
first 13-position cycle.
-/
def is_cycle_prime_nat (n : ℕ) : Prop :=
  n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13

/-- Structural positions on the 13-cycle. -/
abbrev CyclePos := ZMod 13

/-- The seed/source position of the 13-cycle. -/
def is_seed_position (p : CyclePos) : Prop := p = 0

/-- The entry position immediately after the seed. -/
def is_entry_position (p : CyclePos) : Prop := p = 1

/--
The structurally irreducible positions singled out by the breathing cycle:
the seed/source and the entry.
-/
def is_structurally_irreducible_position (p : CyclePos) : Prop :=
  is_seed_position p ∨ is_entry_position p

/--
The residues of the cycle-prime naturals inside `ZMod 13`.

Naturally, `13` appears here as `0`, because the observer/seed position is
the residue class of the cycle length itself.
-/
def is_cycle_prime_position (p : CyclePos) : Prop :=
  p = 0 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11

/-- `0` is not UFRF-prime as a natural number. -/
theorem zero_is_not_ufrf_prime : ¬ is_ufrf_prime 0 := by
  intro h
  rcases h with h | h
  · omega
  · exact Nat.not_prime_zero h.1

/-- `1` is UFRF-prime by the framework's custom natural-number predicate. -/
theorem one_is_ufrf_prime : is_ufrf_prime 1 := by
  left
  rfl

/-- `2` is excluded from the framework's custom natural-number predicate. -/
theorem two_is_not_ufrf_prime : ¬ is_ufrf_prime 2 := by
  simp [is_ufrf_prime]

/--
Every standard prime other than `2` is UFRF-prime as a natural number.
-/
theorem odd_standard_prime_is_ufrf_prime (n : ℕ)
    (hprime : Nat.Prime n) (hne2 : n ≠ 2) :
    is_ufrf_prime n := by
  exact Or.inr ⟨hprime, hne2⟩

/--
The standard primes below `13` are exactly `{2, 3, 5, 7, 11}`.
-/
theorem standard_primes_below_13 (n : ℕ) (hn : n < 13) :
    is_standard_prime n ↔ n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 := by
  interval_cases n <;> unfold is_standard_prime <;> decide

/--
The UFRF-primes below `13` are exactly `{1, 3, 5, 7, 11}`.
-/
theorem ufrf_primes_below_13 (n : ℕ) (hn : n < 13) :
    is_ufrf_prime n ↔ n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 := by
  interval_cases n <;> unfold is_ufrf_prime <;> decide

/--
Below `13`, standard and UFRF primality agree exactly on `{3, 5, 7, 11}`.
-/
theorem standard_and_ufrf_agree_below_13 (n : ℕ) (hn : n < 13) :
    (Nat.Prime n ∧ is_ufrf_prime n) ↔ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 := by
  interval_cases n <;> unfold is_ufrf_prime <;> decide

/--
Up to `13`, the cycle-prime naturals are exactly the standard primes other
than `2`.
-/
theorem cycle_prime_nats_up_to_13 (n : ℕ) (hn : n ≤ 13) :
    is_cycle_prime_nat n ↔ Nat.Prime n ∧ n ≠ 2 := by
  interval_cases n <;> unfold is_cycle_prime_nat <;> decide

/-- The seed position is structurally irreducible. -/
theorem zero_is_structurally_irreducible :
    is_structurally_irreducible_position (0 : CyclePos) := by
  left
  rfl

/-- The entry position is structurally irreducible. -/
theorem one_is_structurally_irreducible :
    is_structurally_irreducible_position (1 : CyclePos) := by
  right
  rfl

/-- Position `2` is neither the seed nor the entry. -/
theorem two_is_not_structurally_irreducible :
    ¬ is_structurally_irreducible_position (2 : CyclePos) := by
  unfold is_structurally_irreducible_position is_seed_position is_entry_position
  decide

/--
Every cycle-prime natural lands on a cycle-prime position when reduced
modulo `13`.
-/
theorem cycle_prime_nat_casts_to_cycle_prime_position (n : ℕ)
    (hn : is_cycle_prime_nat n) :
    is_cycle_prime_position (n : CyclePos) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;>
    unfold is_cycle_prime_position <;> decide

/--
The five cycle-prime naturals appear in the 13-cycle as the residues
`{3, 5, 7, 11, 0}`.
-/
theorem cycle_prime_positions :
    is_cycle_prime_position (3 : CyclePos) ∧
    is_cycle_prime_position (5 : CyclePos) ∧
    is_cycle_prime_position (7 : CyclePos) ∧
    is_cycle_prime_position (11 : CyclePos) ∧
    is_cycle_prime_position (13 : CyclePos) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    unfold is_cycle_prime_position <;> decide

/--
`13` is simultaneously a cycle-prime natural and the seed position of the
cycle after reduction modulo `13`.
-/
theorem thirteen_is_cycle_prime_and_seed_position :
    is_cycle_prime_nat 13 ∧ is_seed_position (13 : CyclePos) := by
  constructor
  · unfold is_cycle_prime_nat
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr rfl
  · unfold is_seed_position
    decide

end UFRF.PrimeSemantics
