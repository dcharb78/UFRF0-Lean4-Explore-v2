import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import UFRF.FineStructure

/-!
# UFRF.NumerizationSeeds

This module adds a narrow arithmetic sidecar lane for the shifted-triangular
"seed" and triangular "completion" quantities discussed in
`docs/NUMERIZATION_SEED_PRIME_INTEGRATION_PLAN.md`.

The intent is deliberately modest:

- formalize the arithmetic expressions,
- prove a small shielding package against divisibility by `3` and `5`,
- prove that the completion quantity is never prime once `n ≥ 3`,
- connect the specific arithmetic seed at `17` to the already-proved
  fine-structure floor `137`.

This module does **not** promote these arithmetic facts into residue theorems,
projection-law theorems, or cycle-position identifications.
-/

namespace UFRF

/-- The shifted triangular arithmetic seed quantity. -/
def numerizationSeed (n : ℕ) : ℕ :=
  n * (n - 1) / 2 + 1

/-- The triangular arithmetic completion quantity. -/
def numerizationCompletion (n : ℕ) : ℕ :=
  n * (n + 1) / 2

/--
The general entry formula for the `n`th numerization stack.

This is the paper's basic arithmetic rule: the `i`th entry in stack `n`
is `n * (n - 1) / 2 + i`.
-/
def numerizationEntry (n i : ℕ) : ℕ :=
  n * (n - 1) / 2 + i

lemma two_mul_numerizationCompletion (n : ℕ) :
    2 * numerizationCompletion n = n * (n + 1) := by
  unfold numerizationCompletion
  have hEven : Even (n * (n + 1)) := by
    simpa [Nat.mul_comm] using Nat.even_mul_succ_self n
  rw [Nat.mul_comm]
  exact Nat.div_two_mul_two_of_even hEven

lemma two_mul_numerizationSeed_succ (n : ℕ) :
    2 * numerizationSeed (n + 1) = (n + 1) * n + 2 := by
  unfold numerizationSeed
  have hEven : Even ((n + 1) * n) := by
    simpa using Nat.even_mul_pred_self (n + 1)
  rw [show (n + 1) * ((n + 1) - 1) = (n + 1) * n by simp]
  rw [left_distrib, mul_comm, Nat.div_two_mul_two_of_even hEven]

/-- The first entry in stack `n` is exactly the numerization seed. -/
theorem numerizationEntry_one_eq_seed (n : ℕ) :
    numerizationEntry n 1 = numerizationSeed n := by
  simp [numerizationEntry, numerizationSeed]

/-- The last valid entry in stack `n` is exactly the numerization completion. -/
theorem numerizationEntry_self_eq_completion (n : ℕ) :
    numerizationEntry n n = numerizationCompletion n := by
  cases n with
  | zero =>
      simp [numerizationEntry, numerizationCompletion]
  | succ n =>
      have hdouble :
          2 * numerizationEntry (n + 1) (n + 1) =
            2 * numerizationCompletion (n + 1) := by
        calc
        2 * numerizationEntry (n + 1) (n + 1)
            = (n + 1) * n + 2 * (n + 1) := by
                unfold numerizationEntry
                have hEven : Even ((n + 1) * n) := by
                  simpa using Nat.even_mul_pred_self (n + 1)
                rw [show (n + 1) * ((n + 1) - 1) = (n + 1) * n by simp]
                rw [left_distrib, mul_comm, Nat.div_two_mul_two_of_even hEven]
        _ = (n + 1) * ((n + 1) + 1) := by
              ring_nf
        _ = 2 * numerizationCompletion (n + 1) := by
              rw [two_mul_numerizationCompletion, Nat.mul_comm]
      omega

/--
Every valid stack entry lies weakly above the numerization seed.
-/
theorem numerizationSeed_le_entry (n i : ℕ) (hi : 1 ≤ i) :
    numerizationSeed n ≤ numerizationEntry n i := by
  unfold numerizationSeed numerizationEntry
  exact Nat.add_le_add_left hi _

/--
Every valid stack entry lies weakly below the numerization completion.
-/
theorem numerizationEntry_le_completion (n i : ℕ) (hi : i ≤ n) :
    numerizationEntry n i ≤ numerizationCompletion n := by
  rw [← numerizationEntry_self_eq_completion]
  unfold numerizationEntry
  exact Nat.add_le_add_left hi _

/--
Any entry with `1 ≤ i ≤ n` lies in the closed interval bounded by the stack
seed and stack completion.
-/
theorem numerizationEntry_mem_stack_interval (n i : ℕ)
    (hi_lower : 1 ≤ i) (hi_upper : i ≤ n) :
    numerizationSeed n ≤ numerizationEntry n i ∧
      numerizationEntry n i ≤ numerizationCompletion n := by
  exact ⟨numerizationSeed_le_entry n i hi_lower,
    numerizationEntry_le_completion n i hi_upper⟩

/--
Each stack entry can also be read as an offset from the previous stack's
completion.
-/
theorem numerizationEntry_eq_completion_pred_add (n i : ℕ) :
    numerizationEntry n i = numerizationCompletion (n - 1) + i := by
  cases n with
  | zero =>
      simp [numerizationEntry, numerizationCompletion]
  | succ n =>
      simp [numerizationEntry, numerizationCompletion, Nat.mul_comm, Nat.add_comm]

/--
The seed of stack `n` is one more than the completion of the previous stack.
-/
theorem numerizationSeed_eq_completion_pred_add_one (n : ℕ) :
    numerizationSeed n = numerizationCompletion (n - 1) + 1 := by
  cases n with
  | zero =>
      simp [numerizationSeed, numerizationCompletion]
  | succ n =>
      simp [numerizationSeed, numerizationCompletion, Nat.mul_comm]

/-- Consecutive stack completions differ by exactly `n + 1`. -/
theorem numerizationCompletion_succ_eq_completion_add_succ (n : ℕ) :
    numerizationCompletion (n + 1) = numerizationCompletion n + (n + 1) := by
  have hdouble :
      2 * numerizationCompletion (n + 1) =
        2 * (numerizationCompletion n + (n + 1)) := by
    calc
      2 * numerizationCompletion (n + 1)
          = (n + 1) * (n + 2) := by
              rw [two_mul_numerizationCompletion]
      _ = n * (n + 1) + 2 * (n + 1) := by
            ring_nf
      _ = 2 * numerizationCompletion n + 2 * (n + 1) := by
            rw [two_mul_numerizationCompletion]
      _ = 2 * (numerizationCompletion n + (n + 1)) := by
            ring_nf
  omega

/--
The completion of stack `n` is the previous completion plus `n`.
-/
theorem numerizationCompletion_eq_completion_pred_add_self (n : ℕ) :
    numerizationCompletion n = numerizationCompletion (n - 1) + n := by
  cases n with
  | zero =>
      simp [numerizationCompletion]
  | succ n =>
      simpa using numerizationCompletion_succ_eq_completion_add_succ n

/-- Every positive stack index is bounded above by its completion value. -/
theorem self_le_numerizationCompletion (n : ℕ) :
    n ≤ numerizationCompletion n := by
  rw [numerizationCompletion_eq_completion_pred_add_self]
  omega

/-- The completion values are strictly increasing with the stack index. -/
theorem numerizationCompletion_lt_succ (n : ℕ) :
    numerizationCompletion n < numerizationCompletion (n + 1) := by
  rw [numerizationCompletion_succ_eq_completion_add_succ]
  omega

/-- The completion values are monotone in the stack index. -/
theorem numerizationCompletion_monotone : Monotone numerizationCompletion :=
  monotone_nat_of_le_succ fun n => (numerizationCompletion_lt_succ n).le

/--
Any valid entry in stack `n` lies strictly above the completion of the
previous stack.
-/
theorem numerizationCompletion_pred_lt_entry (n i : ℕ)
    (hi_lower : 1 ≤ i) :
    numerizationCompletion (n - 1) < numerizationEntry n i := by
  have hseed : numerizationSeed n ≤ numerizationEntry n i :=
    numerizationSeed_le_entry n i hi_lower
  rw [numerizationSeed_eq_completion_pred_add_one] at hseed
  omega

/--
Every positive natural number lands in a unique numerization stack with a
unique valid in-stack index.
-/
theorem existsUnique_numerizationEntry (m : ℕ) (hm : 0 < m) :
    ∃! p : ℕ × ℕ, 1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ numerizationEntry p.1 p.2 = m := by
  let P : ℕ → Prop := fun n => m ≤ numerizationCompletion n
  have hP : ∃ n, P n := by
    refine ⟨m, ?_⟩
    exact self_le_numerizationCompletion m
  let n : ℕ := Nat.find hP
  have hn_completion : m ≤ numerizationCompletion n := by
    exact Nat.find_spec hP
  have hn_pos : 0 < n := by
    by_contra hn_nonpos
    have hn_zero : n = 0 := by omega
    have : m ≤ 0 := by
      simpa [n, hn_zero, P, numerizationCompletion] using hn_completion
    omega
  have hprev_not : ¬ m ≤ numerizationCompletion (n - 1) := by
    have hlt : n - 1 < n := Nat.pred_lt (Nat.ne_of_gt hn_pos)
    simpa [n, P] using Nat.find_min hP hlt
  have hprev_lt_m : numerizationCompletion (n - 1) < m := by
    omega
  let i : ℕ := m - numerizationCompletion (n - 1)
  have hi_lower : 1 ≤ i := by
    dsimp [i]
    exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt hprev_lt_m)
  have hi_upper : i ≤ n := by
    dsimp [i]
    rw [numerizationCompletion_eq_completion_pred_add_self] at hn_completion
    omega
  have hentry : numerizationEntry n i = m := by
    dsimp [i]
    rw [numerizationEntry_eq_completion_pred_add, Nat.add_comm,
      Nat.sub_add_cancel (le_of_lt hprev_lt_m)]
  refine ⟨(n, i), ?_, ?_⟩
  · exact ⟨hi_lower, hi_upper, hentry⟩
  · intro p hp
    rcases p with ⟨n', i'⟩
    rcases hp with ⟨hi'_lower, hi'_upper, hentry'⟩
    have hm_le_completion' : m ≤ numerizationCompletion n' := by
      have hmem := numerizationEntry_mem_stack_interval n' i' hi'_lower hi'_upper
      simpa [hentry'] using hmem.2
    have hn_le_n' : n ≤ n' := by
      exact Nat.find_min' hP (by simpa [P] using hm_le_completion')
    have hn_not_lt_n' : ¬ n < n' := by
      intro hlt
      have hcomp_le :
          numerizationCompletion n ≤ numerizationCompletion (n' - 1) := by
        exact numerizationCompletion_monotone (Nat.le_pred_of_lt hlt)
      have hprev_lt_m' : numerizationCompletion (n' - 1) < m := by
        have hprev := numerizationCompletion_pred_lt_entry n' i' hi'_lower
        simpa [hentry'] using hprev
      have : m ≤ numerizationCompletion (n' - 1) := by
        exact le_trans hn_completion hcomp_le
      exact (not_le.mpr hprev_lt_m') this
    have hn'_le_n : n' ≤ n := not_lt.mp hn_not_lt_n'
    have hn_eq : n' = n := le_antisymm hn'_le_n hn_le_n'
    subst hn_eq
    have hi_eq : i' = i := by
      have hsame : numerizationEntry n i' = numerizationEntry n i := by
        rw [hentry', hentry]
      unfold numerizationEntry at hsame
      omega
    cases hi_eq
    rfl

/--
The shifted triangular arithmetic seed is never divisible by `3`.

The proof avoids any residue/projection interpretation: it doubles the seed to
the division-free polynomial `n(n-1)+2`, then checks that polynomial in
`ZMod 3`.
-/
theorem numerizationSeed_not_dvd_three (n : ℕ) :
    ¬ 3 ∣ numerizationSeed n := by
  cases n with
  | zero =>
      simp [numerizationSeed]
  | succ n =>
      intro h
      have hdouble : 3 ∣ (n + 1) * n + 2 := by
        have hmul : 3 ∣ 2 * numerizationSeed (n + 1) := dvd_mul_of_dvd_right h 2
        rwa [two_mul_numerizationSeed_succ] at hmul
      rcases hdouble with ⟨k, hk⟩
      have hzero : (((n + 1) * n + 2 : ℕ) : ZMod 3) = 0 := by
        rw [hk]
        rw [Nat.cast_mul]
        have hthree : (((3 : ℕ) : ZMod 3) = 0) := by
          decide
        rw [hthree]
        simp
      have hx : (((n : ZMod 3) + 1) * (n : ZMod 3) + 2) = 0 := by
        simpa using hzero
      have hcases : ∀ x : ZMod 3, (x + 1) * x + 2 ≠ 0 := by
        intro x
        fin_cases x <;> decide
      exact hcases (n : ZMod 3) hx

/--
The shifted triangular arithmetic seed is never divisible by `5`.

As in the `mod 3` theorem, we pass through the doubled division-free form
`n(n-1)+2`, now checking the residue in `ZMod 5`.
-/
theorem numerizationSeed_not_dvd_five (n : ℕ) :
    ¬ 5 ∣ numerizationSeed n := by
  cases n with
  | zero =>
      simp [numerizationSeed]
  | succ n =>
      intro h
      have hdouble : 5 ∣ (n + 1) * n + 2 := by
        have hmul : 5 ∣ 2 * numerizationSeed (n + 1) := dvd_mul_of_dvd_right h 2
        rwa [two_mul_numerizationSeed_succ] at hmul
      rcases hdouble with ⟨k, hk⟩
      have hzero : (((n + 1) * n + 2 : ℕ) : ZMod 5) = 0 := by
        rw [hk]
        rw [Nat.cast_mul]
        have hfive : (((5 : ℕ) : ZMod 5) = 0) := by
          decide
        rw [hfive]
        simp
      have hx : (((n : ZMod 5) + 1) * (n : ZMod 5) + 2) = 0 := by
        simpa using hzero
      have hcases : ∀ x : ZMod 5, (x + 1) * x + 2 ≠ 0 := by
        intro x
        fin_cases x <;> decide
      exact hcases (n : ZMod 5) hx

/--
The triangular completion quantity is never prime for `n ≥ 3`.

The proof splits by parity so the triangular expression becomes an explicit
product of two naturals, each distinct from `1`.
-/
theorem numerizationCompletion_not_prime (n : ℕ) (hn : 3 ≤ n) :
    ¬ Nat.Prime (numerizationCompletion n) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  ·
    have hk_ne_one : k ≠ 1 := by
      intro hk
      omega
    have hfac_ne_one : 2 * k + 1 ≠ 1 := by
      omega
    have hfac :
        numerizationCompletion (2 * k) = k * (2 * k + 1) := by
      unfold numerizationCompletion
      rw [show (2 * k) * (2 * k + 1) = 2 * (k * (2 * k + 1)) by ring]
      rw [Nat.mul_div_right _ (by positivity)]
    simpa [hfac] using Nat.not_prime_mul hk_ne_one hfac_ne_one
  ·
    have hleft_ne_one : 2 * k + 1 ≠ 1 := by
      omega
    have hright_ne_one : k + 1 ≠ 1 := by
      omega
    have hfac :
        numerizationCompletion (2 * k + 1) = (2 * k + 1) * (k + 1) := by
      unfold numerizationCompletion
      rw [show (2 * k + 1) * (2 * k + 1 + 1) = 2 * ((2 * k + 1) * (k + 1)) by ring]
      rw [Nat.mul_div_right _ (by positivity)]
    simpa [hfac] using Nat.not_prime_mul hleft_ne_one hright_ne_one

/-- The shifted triangular arithmetic seed at `17` is `137`. -/
theorem numerizationSeed_seventeen_eq_137 :
    numerizationSeed 17 = 137 := by
  norm_num [numerizationSeed]

/--
The already-proved UFRF fine-structure floor matches the arithmetic
numerization seed at `17`.
-/
theorem alpha_inv_floor_eq_numerizationSeed_seventeen :
    Int.floor UFRF.Constants.ufrf_alpha_inv = (numerizationSeed 17 : Int) := by
  rw [alpha_inv_floor_137]
  norm_num [numerizationSeed]

end UFRF
