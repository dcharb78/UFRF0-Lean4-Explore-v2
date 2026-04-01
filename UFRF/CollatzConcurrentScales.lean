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

/-! ## Section 6: The Open Frontier -/

/-- **Every integer resolves at its native scale.**

    For any odd n, the exact 2-adic valuation v₂(3n+1) determines the scale k
    at which n's residue is safe: the modular certificate correctly reflects
    the actual v₂ at level k = v₂(3n+1).

    OPEN: Requires connecting v₂Fuel to Nat.dvd — specifically showing that
    v₂Fuel n n = k implies 2^k ∣ n but 2^(k+1) ∤ n. The mathematical content
    is clear; the Lean infrastructure connecting the fuel-based v₂ definition
    to divisibility statements is the proof obligation. -/
theorem integer_resolves_at_native_scale (n : ℕ) (hn : Odd n) :
    let k := v2Fuel 64 (3 * n + 1)
    ¬ isUnsafe (n % (13 * 2 ^ k)) (k + 1) := by
  sorry

/-- **Collatz convergence from concurrent scale structure**

    The proof chain:
    1. Every n resolves at its native scale       [integer_resolves_at_native_scale]
    2. At that scale the contraction cert applies  [CollatzSolenoid.contraction_k3 etc.]
    3. Scales are mutually compatible             [CollatzSolenoid.tower_compat_k3_k4 etc.]
    4. Therefore every trajectory contracts

    OPEN OBLIGATIONS:
    (a) General contraction certificate for all k (W(k) theorem, data in CollatzWindow)
    (b) Composing certificates across all steps (solenoid inverse limit argument)
    (c) W(k)/modulus → 0 sub-linear growth bound (the analytic heart)

    The structural foundation — Trinity, 13-cycle, concurrent splitting,
    tower compatibility — is complete. This theorem is the remaining summit. -/
theorem collatz_convergence_from_concurrent_scales (n : ℕ) (hn : Odd n) :
    ∃ t : ℕ, (Nat.rec n (fun _ m => if m % 2 = 0 then m / 2 else 3 * m + 1) t) = 1 := by
  sorry

end UFRF.ConcurrentScales
