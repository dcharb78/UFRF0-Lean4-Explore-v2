import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import UFRF.DoublingFlip
import UFRF.Foundation

/-!
# UFRF.C3Umklapp

This module connects the positional doubling theorem to the mod-3 PAM closure
law. The C3 phase ring is not introduced as a separate physical axiom: it is
`ZMod UFRF.Foundation.trinity_dimension`, and the Core theorem
`trinity_dimension = 3` reduces it to the three-state Trinity carrier.

The sign convention below is deliberately explicit:

* `pamPlus = 1` is the incident PAM phase.
* `pamPlus + pamPlus = pamMinus` is the C3 closure `1 + 1 = -1`.
* Under the UFRF chirality bridge, `pamPlus` maps to expansion chirality `-1`,
  while the closed phase `pamMinus` maps to contraction chirality `+1`.

With that bridge fixed, the C3/PAM law is equivalent to the chirality reversal
proved in `UFRF.DoublingFlip`.
-/

namespace UFRF.C3Umklapp

open UFRF.DoublingFlip

/-- The C3 phase carrier, derived from the UFRF Core Trinity dimension. -/
abbrev C3Phase := ZMod UFRF.Foundation.trinity_dimension

/-- Core provenance: the C3 modulus is exactly the Trinity dimension. -/
theorem c3_modulus_is_trinity_dimension :
    UFRF.Foundation.trinity_dimension = 3 := rfl

/-- The incident PAM phase, written as `+1`. -/
def pamPlus : C3Phase := 1

/-- The neutral PAM phase. -/
def pamZero : C3Phase := 0

/-- The closed PAM phase, written as `-1` in C3. -/
def pamMinus : C3Phase := -1

/-- PAM doubling is C3 addition of a phase to itself. -/
def pamDouble (x : C3Phase) : C3Phase := x + x

/-- The mod-3 PAM closure law: `1 + 1 = -1`. -/
theorem c3_pam_closure : pamDouble pamPlus = pamMinus := by
  decide

/--
Transport C3/PAM phases to physical chirality signs.

The values are the integer-scaled Trinity poles: expansion `-1`, mediator `0`,
and contraction `+1`.
-/
def pamChirality (x : C3Phase) : ℤ :=
  if x = pamZero then 0 else if x = pamPlus then -1 else 1

@[simp] theorem pamChirality_zero : pamChirality pamZero = 0 := by
  simp [pamChirality]

@[simp] theorem pamChirality_plus : pamChirality pamPlus = -1 := by
  have h_not_zero : ¬ pamPlus = pamZero := by decide
  simp [pamChirality, h_not_zero]

@[simp] theorem pamChirality_minus : pamChirality pamMinus = 1 := by
  have h_not_zero : ¬ pamMinus = pamZero := by decide
  have h_not_plus : ¬ pamMinus = pamPlus := by decide
  simp [pamChirality, h_not_zero, h_not_plus]

@[simp] theorem pamChirality_double_plus :
    pamChirality (pamDouble pamPlus) = 1 := by
  rw [c3_pam_closure]
  exact pamChirality_minus

/-- The C3 closure reverses the transported Trinity chirality. -/
theorem c3_closure_reverses_trinity_chirality :
    pamChirality (pamDouble pamPlus) = -pamChirality pamPlus := by
  simp

/--
The C3 closure law is the Trinity chirality composition law for the incident
PAM phase.
-/
theorem c3_closure_iff_trinity_chirality_reversal :
    pamDouble pamPlus = pamMinus ↔
      pamChirality (pamDouble pamPlus) = -pamChirality pamPlus := by
  constructor
  · intro h
    rw [h]
    simp
  · intro _h
    exact c3_pam_closure

/--
Main bridge theorem.

Under the C3-to-Trinity chirality bridge, the physical doubling pair
`(chirality p, chirality (double p))` is exactly the PAM closure pair
`(1, 1 + 1)` iff `p` lies in the strict flip-crossing window.
-/
theorem c3_pam_equiv_chirality_reversal_under_doubling (p : ℝ) :
    chirality p = pamChirality pamPlus ∧
      chirality (double p) = pamChirality (pamDouble pamPlus)
        ↔ fp / 2 < p ∧ p < fp := by
  simpa using flip_window_characterization p

/--
The experimental Bi2Se3 position `5.56 -> 11.12` realizes the same C3/PAM
closure pair after transport through the Trinity chirality bridge.
-/
example :
    let p_Eu : ℝ := 5.56
    chirality p_Eu = pamChirality pamPlus ∧
      chirality (double p_Eu) = pamChirality (pamDouble pamPlus) := by
  norm_num [chirality, fp, double]

end UFRF.C3Umklapp
