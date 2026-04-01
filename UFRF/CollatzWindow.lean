import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic
import UFRF.Collatz

namespace UFRF.CollatzWindow

/-!
# UFRF.CollatzWindow: Modular Bad-Streak Bounds

This module formalizes results from `analysis/collatz_orbit_analysis.py`.

## The Computational Setting

We work in the **transition graph** on ZMod(13 × 2^k) where:
- Nodes = odd residue classes mod (13 × 2^k)
- Each node r has one outgoing edge: the Syracuse image of r (mod 13 × 2^k)
- Edge weight = v₂(3r+1) (the 2-adic valuation of the Syracuse numerator)

A **bad step** is a step with v₂ = 1 (minimal halving, net growth).
A **bad streak** is a maximal run of consecutive bad steps.

## Main Results (Machine-Verified)

For k=3 (modulus 104 = 13 × 8):
- **`max_bad_streak_k3`**: No 5 consecutive bad steps exist in the graph.
  (Max bad streak = 4, matching `max_bad_streak = k+1` for k=3.)

For k=4 (modulus 208 = 13 × 16):
- **`max_bad_streak_k4`**: No 6 consecutive bad steps exist in the graph.
  (Max bad streak = 5, matching `max_bad_streak = k+1` for k=4.)

## Convergence Windows (Conjectured, Not Yet Proved in Lean)

The Python DP analysis proves that for k=3, any 10-step walk in the residue
graph has negative cumulative log₂-drift. This is a correct result about the
GRAPH structure (52 nodes, deterministic transitions). Formalizing it in Lean
requires rational arithmetic over a finite graph — left as future work.

Python results: W(3)=10, W(4)=22, W(5)=26, W(6)=42, W(7)=52, W(8)=54, W(9)=59, W(10)=78.
-/

/-! ## Section 1: The Fuel-Based 2-Adic Valuation -/

/-- Compute v₂(n) = 2-adic valuation of n, using a fuel parameter for termination.
    v₂_fuel fuel n = v₂(n) for all n ≤ 2^fuel (trivially satisfied for any n). -/
def v2Fuel : ℕ → ℕ → ℕ
  | 0, _ => 0          -- fuel exhausted (unreachable for n < 2^fuel)
  | _, 0 => 0          -- v₂(0) = 0 by convention
  | fuel + 1, n => if n % 2 = 0 then 1 + v2Fuel fuel (n / 2) else 0

/-- Canonical v₂: use n itself as fuel (correct for all n). -/
def v2 (n : ℕ) : ℕ := v2Fuel n n

/-- The residue-level Syracuse step: map odd n to (3n+1)/2^v₂(3n+1) mod m. -/
def syracuseMod (m n : ℕ) : ℕ :=
  ((3 * n + 1) / 2 ^ v2Fuel 64 (3 * n + 1)) % m

/-! ## Section 2: Bad-Streak Bound at k=3 (Modulus 104)

The transition graph on ZMod 104 has 52 odd-residue nodes: {1, 3, 5, ..., 103}.
Claim: no path of length 5 has all edge-weights equal to 1 (i.e., all v₂ = 1).
Equivalently: the maximum bad streak in this graph is 4.

This is verified by exhaustive enumeration over all 52 starting residues. -/

/-- In the Syracuse transition graph on ZMod 104,
    no 5 consecutive steps can all have v₂ = 1.
    (Max bad streak = 4 = k+1 for k=3.)

    ✅ PROVEN -/
theorem max_bad_streak_k3 :
    ∀ r : Fin 52,
      let n₀ := 2 * r.val + 1          -- odd residues: 1, 3, ..., 103
      let n₁ := syracuseMod 104 n₀
      let n₂ := syracuseMod 104 n₁
      let n₃ := syracuseMod 104 n₂
      let n₄ := syracuseMod 104 n₃
      ¬(v2Fuel 64 (3 * n₀ + 1) = 1 ∧
        v2Fuel 64 (3 * n₁ + 1) = 1 ∧
        v2Fuel 64 (3 * n₂ + 1) = 1 ∧
        v2Fuel 64 (3 * n₃ + 1) = 1 ∧
        v2Fuel 64 (3 * n₄ + 1) = 1) := by
  intro r
  fin_cases r <;> native_decide

/-! ## Section 3: Bad-Streak Bound at k=4 (Modulus 208) -/

/-- In the Syracuse transition graph on ZMod 208,
    no 6 consecutive steps can all have v₂ = 1.
    (Max bad streak = 5 = k+1 for k=4.)

    ✅ PROVEN -/
theorem max_bad_streak_k4 :
    ∀ r : Fin 104,
      let n₀ := 2 * r.val + 1          -- odd residues: 1, 3, ..., 207
      let n₁ := syracuseMod 208 n₀
      let n₂ := syracuseMod 208 n₁
      let n₃ := syracuseMod 208 n₂
      let n₄ := syracuseMod 208 n₃
      let n₅ := syracuseMod 208 n₄
      ¬(v2Fuel 64 (3 * n₀ + 1) = 1 ∧
        v2Fuel 64 (3 * n₁ + 1) = 1 ∧
        v2Fuel 64 (3 * n₂ + 1) = 1 ∧
        v2Fuel 64 (3 * n₃ + 1) = 1 ∧
        v2Fuel 64 (3 * n₄ + 1) = 1 ∧
        v2Fuel 64 (3 * n₅ + 1) = 1) := by
  intro r
  fin_cases r <;> native_decide

/-! ## Section 3b: Bad-Streak Bound at k=5 (Modulus 416) -/

/-- In the Syracuse transition graph on ZMod 416,
    no 7 consecutive steps can all have v₂ = 1.
    (Max bad streak = 6 = k+1 for k=5.)

    ✅ PROVEN -/
theorem max_bad_streak_k5 :
    ∀ r : Fin 208,
      let n₀ := 2 * r.val + 1
      let n₁ := syracuseMod 416 n₀
      let n₂ := syracuseMod 416 n₁
      let n₃ := syracuseMod 416 n₂
      let n₄ := syracuseMod 416 n₃
      let n₅ := syracuseMod 416 n₄
      let n₆ := syracuseMod 416 n₅
      ¬(v2Fuel 64 (3 * n₀ + 1) = 1 ∧
        v2Fuel 64 (3 * n₁ + 1) = 1 ∧
        v2Fuel 64 (3 * n₂ + 1) = 1 ∧
        v2Fuel 64 (3 * n₃ + 1) = 1 ∧
        v2Fuel 64 (3 * n₄ + 1) = 1 ∧
        v2Fuel 64 (3 * n₅ + 1) = 1 ∧
        v2Fuel 64 (3 * n₆ + 1) = 1) := by native_decide

/-! ## Section 3c: Bad-Streak Bound at k=6 (Modulus 832) -/

/-- In the Syracuse transition graph on ZMod 832,
    no 8 consecutive steps can all have v₂ = 1.
    (Max bad streak = 7 = k+1 for k=6.)

    ✅ PROVEN -/
theorem max_bad_streak_k6 :
    ∀ r : Fin 416,
      let n₀ := 2 * r.val + 1
      let n₁ := syracuseMod 832 n₀
      let n₂ := syracuseMod 832 n₁
      let n₃ := syracuseMod 832 n₂
      let n₄ := syracuseMod 832 n₃
      let n₅ := syracuseMod 832 n₄
      let n₆ := syracuseMod 832 n₅
      let n₇ := syracuseMod 832 n₆
      ¬(v2Fuel 64 (3 * n₀ + 1) = 1 ∧
        v2Fuel 64 (3 * n₁ + 1) = 1 ∧
        v2Fuel 64 (3 * n₂ + 1) = 1 ∧
        v2Fuel 64 (3 * n₃ + 1) = 1 ∧
        v2Fuel 64 (3 * n₄ + 1) = 1 ∧
        v2Fuel 64 (3 * n₅ + 1) = 1 ∧
        v2Fuel 64 (3 * n₆ + 1) = 1 ∧
        v2Fuel 64 (3 * n₇ + 1) = 1) := by native_decide

/-! ## Section 4: The Pattern (Bad Streak = k+1)

The two theorems above are instances of the general pattern discovered computationally:
  max_bad_streak(13 × 2^k) = k + 1

for k = 3, 4, 5, 6, 7, 8, 9, 10 (all verified by Python, k=3 and k=4 verified in Lean).

This linear growth of bad streaks, combined with the existence of convergence windows,
is the computational foundation for the Collatz approach via UFRF breathing structure. -/

/-- The bad streak bound at k=3 is tight: there EXISTS a path of length 4 with all v₂=1.
    (Residue 31 starts a bad streak of length 4: 31→47→71→107 in ZMod 104.)

    ✅ PROVEN -/
theorem bad_streak_4_exists_k3 :
    let n₀ := (31 : ℕ)  -- known bad-streak starter in ZMod 104
    let n₁ := syracuseMod 104 n₀
    let n₂ := syracuseMod 104 n₁
    let n₃ := syracuseMod 104 n₂
    v2Fuel 64 (3 * n₀ + 1) = 1 ∧
    v2Fuel 64 (3 * n₁ + 1) = 1 ∧
    v2Fuel 64 (3 * n₂ + 1) = 1 ∧
    v2Fuel 64 (3 * n₃ + 1) = 1 := by
  native_decide

end UFRF.CollatzWindow
