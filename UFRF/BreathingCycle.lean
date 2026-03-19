import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic
import UFRF.Foundation

namespace BreathingCycle

/-!
# UFRF.BreathingCycle (Upgraded to ZMod Ring)

**Theorem 2: The 13-Position Breathing Cycle**

The Trinity's three LOG grades generate exactly 13 positions:
- Positions 1–3: Log1 (Linear phase)
- Positions 4–6: Log2 (Curved phase)
- **Position 6.5: Critical Flip** (boundary between expansion and contraction)
- Positions 7–9: Log3 (Cubed phase)
- Position 10: REST (maximum coherence)
- Positions 11–12: Bridge (scale transition)
- Position 13: Seed (= Position 1 of next cycle)

## Design: ZMod vs Fin

We use `ZMod` instead of `Fin` because the cycle is a **Topological Ring**.
Movement is modular: Position 13 is not "out of bounds" — it IS Position 0.
The `bridge_seed_wraps` theorem `(12 + 1 = 0)` becomes definitional.

For **indexing/addressing**, `Fin` is still used in `Addressing.lean` and
`NumberBases.lean`. When computing the *Phase* of an address, cast via
`(digit : ZMod 13)`.

## Key Properties
- The flip at 6.5 divides EXPANSION (1–6) from CONTRACTION (7–13)
- Bridge positions (11–13) become Seed positions (1–3) of the next scale
- Position 10 (REST) is the point of maximum stability → Base 10
- Position 13 loops to Position 1 → toroidal topology (axiomatic in ZMod)
-/

/-- The cycle length, derived from Foundation geometry (not hardcoded).
    See `UFRF.Foundation.cycle_is_thirteen` for the proof that this = 13. -/
abbrev cycle_len : ℕ := UFRF.Foundation.derived_cycle_length

/-- The cycle length is 13 (derived, not assumed). -/
theorem cycle_has_13_positions : cycle_len = 13 :=
  UFRF.Foundation.cycle_is_thirteen

/--
**The Cycle Position (ZMod Ring)**
We use `ZMod cycle_len` to enforce the toroidal topology algebraically.
Addition, subtraction, and multiplication wrap automatically.
-/
abbrev CyclePos := ZMod cycle_len

/--
The phase quality of a position in the breathing cycle, based on its
LOG grade and function.
-/
inductive LogPhase where
  | log1_linear    -- Positions 1–3 (indices 0–2)
  | log2_curved    -- Positions 4–6 (indices 3–5)
  | log3_cubed     -- Positions 7–9 (indices 6–8)
  | rest           -- Position 10 (index 9)
  | bridge         -- Positions 11–12 (indices 10–11)
  | seed           -- Position 13 (index 12)
  deriving DecidableEq, Repr

/-- Classify each position into its LogPhase using ZMod.val. -/
def CyclePos.logPhase (p : CyclePos) : LogPhase :=
  if p.val < 3 then .log1_linear
  else if p.val < 6 then .log2_curved
  else if p.val < 9 then .log3_cubed
  else if p.val = 9 then .rest
  else if p.val < 12 then .bridge
  else .seed

/-- Whether a position is in the expansion half (positions 1–6, indices 0–5). -/
def CyclePos.isExpansion (p : CyclePos) : Prop := p.val < 6

/-- Whether a position is in the contraction half (positions 7–13, indices 6–12). -/
def CyclePos.isContraction (p : CyclePos) : Prop := p.val ≥ 6

instance (p : CyclePos) : Decidable p.isExpansion := inferInstanceAs (Decidable (p.val < 6))
instance (p : CyclePos) : Decidable p.isContraction := inferInstanceAs (Decidable (p.val ≥ 6))

/--
Every position is either in expansion or contraction (the flip at 6.5 is the boundary).

✅ PROVEN
-/
theorem expansion_or_contraction (p : CyclePos) :
    p.isExpansion ∨ p.isContraction := by
  simp [CyclePos.isExpansion, CyclePos.isContraction]
  omega

/--
Expansion and contraction are mutually exclusive.

✅ PROVEN
-/
theorem not_both (p : CyclePos) :
    ¬(p.isExpansion ∧ p.isContraction) := by
  simp [CyclePos.isExpansion, CyclePos.isContraction]

/-! ### Distinguished Positions -/

/--
The REST position (index 9 = position 10) is the unique point of maximum
coherence. It is the last position before the bridge phase begins.
-/
def restPosition : CyclePos := (9 : CyclePos)

/--
The Seed position (index 12 = position 13) maps to position 1 of the next cycle.
This is the toroidal identification that closes the loop.
-/
def seedPosition : CyclePos := (12 : CyclePos)

/--
The entry position (index 0 = position 1).
-/
def entryPosition : CyclePos := (0 : CyclePos)

/-! ### Contextual Charts -/

/--
Human-facing position labels on the 13-cycle.

Label `1` is the entry index `0`, and label `13` is the seed index `12`.
This is the 1-based chart used in most prose descriptions.
-/
def labeledPosition (n : ℕ) : CyclePos := (n + 12 : CyclePos)

/--
Local coordinate of a position relative to a chosen chart origin.

This is the contextual reindexing map: the origin becomes `0`, the next
position becomes `1`, and so on.
-/
def localCoordinate (origin p : CyclePos) : CyclePos := p - origin

/-- Label `1` is the entry position in the human-facing chart. -/
theorem labeledPosition_one_is_entry :
    labeledPosition 1 = entryPosition := by
  unfold labeledPosition entryPosition
  decide

/-- Label `13` is the seed position in the human-facing chart. -/
theorem labeledPosition_thirteen_is_seed :
    labeledPosition 13 = seedPosition := by
  unfold labeledPosition seedPosition
  decide

/--
Local coordinates are translation-invariant.

Changing charts by a uniform shift does not change the contextual phase
difference between positions.

✅ PROVEN
-/
theorem localCoordinate_translation_invariant (origin p k : CyclePos) :
    localCoordinate (origin + k) (p + k) = localCoordinate origin p := by
  unfold localCoordinate
  abel

/--
The full cycle length vanishes as a residue in the cycle ring.

Any whole-number multiple of 13 is the zero displacement in `ZMod 13`.

✅ PROVEN
-/
theorem full_cycle_shift_vanishes (s : ℕ) :
    ((cycle_len * s : ℕ) : CyclePos) = 0 := by
  calc
    ((cycle_len * s : ℕ) : CyclePos) = ((cycle_len : ℕ) : CyclePos) * (s : CyclePos) := by
      simp
    _ = 0 := by
      have hcycle : ((cycle_len : ℕ) : CyclePos) = 0 := by
        change ((13 : ℕ) : ZMod 13) = 0
        decide
      rw [hcycle, zero_mul]

/--
Human-facing labels are periodic with period 13.

Adding a whole cycle does not change the underlying position; it only
changes the chart in which that position is named.

✅ PROVEN
-/
theorem labeledPosition_periodic (n s : ℕ) :
    labeledPosition (n + cycle_len * s) = labeledPosition n := by
  simp [labeledPosition, Nat.cast_add, full_cycle_shift_vanishes s]

/--
Local charts depend only on offset, not on the absolute labels.

If the chart origin is named `origin`, then the label `origin + offset`
has local coordinate `offset`.

✅ PROVEN
-/
theorem localCoordinate_of_labeled_offset (origin offset : ℕ) :
    localCoordinate (labeledPosition origin) (labeledPosition (origin + offset)) =
      (offset : CyclePos) := by
  unfold localCoordinate labeledPosition
  simp [Nat.cast_add, sub_eq_add_neg]

/-! ### Ring Topology Theorems -/

/--
**Bridge-Seed Continuity (Automatic)**
Because CyclePos is a ZMod ring, adding 1 to the last position (12)
automatically returns to the entry position (0).
In `Fin 13` this required manual `%`; in `ZMod 13` it is *definitional*.

✅ PROVEN
-/
theorem bridge_seed_wraps : (12 : CyclePos) + 1 = 0 := by
  decide

/--
**Inversion Symmetry**
In a balanced 13-cycle, the Flip (6.5) roughly corresponds to the
additive inverse. In ZMod 13: 6 + 7 = 13 ≡ 0.

✅ PROVEN
-/
theorem inversion_symmetry : (6 : CyclePos) + 7 = 0 := by
  decide

/--
**Full Cycle Return**
Any position plus 13 returns to itself (periodicity).
This is automatic in ZMod 13 since 13 ≡ 0.

✅ PROVEN
-/
theorem full_cycle_identity : (13 : CyclePos) = 0 := by
  decide

/--
Two directed steps are contextually the same when they have the same
displacement in the cycle ring.
-/
def sameStep (a b c d : CyclePos) : Prop :=
  b - a = d - c

/--
**All unit steps are translation-equivalent in the 13-cycle.**

The labeled move `0 → 1` is not special as a displacement: every move
`x → x+1` has the same contextual content.

✅ PROVEN
-/
theorem unit_steps_are_translation_equivalent (x y : CyclePos) :
    sameStep x (x + 1) y (y + 1) := by
  unfold sameStep
  abel

/--
**The bridge step `12 → 13` is the same unit move as `0 → 1`.**

This makes the ring-context explicit: `13 = 0`, so the boundary crossing is
the same successor step viewed in a different chart.

✅ PROVEN
-/
theorem bridge_to_seed_step_matches_entry_step :
    sameStep 12 13 0 1 := by
  unfold sameStep
  decide

/--
**The wrapped bridge step `12 → 0` is the same unit move as `0 → 1`.**

This is the same contextual fact as `bridge_to_seed_step_matches_entry_step`,
expressed after reducing `13` to `0` inside `ZMod 13`.

✅ PROVEN
-/
theorem wrapped_bridge_step_matches_entry_step :
    sameStep 12 0 0 1 := by
  unfold sameStep
  decide

/--
The bridge-to-seed step is the same at every whole-cycle translate.

The labels may shift by 13, 26, 39, ... but the contextual step remains
the same unit successor.

✅ PROVEN
-/
theorem bridge_to_seed_step_matches_entry_step_at_scale (s : ℕ) :
    sameStep ((12 + cycle_len * s : ℕ) : CyclePos)
      ((13 + cycle_len * s : ℕ) : CyclePos) 0 1 := by
  unfold sameStep
  simp [Nat.cast_add, sub_eq_add_neg, full_cycle_shift_vanishes s]
  norm_num

/--
**Terminal block chart: `10 = 0`, `11 = 1`, `12 = 2`, `13 = 3`.**

Anchoring a local chart at human position `10` reindexes the final
four-position bridge/seed block as `0,1,2,3`.

✅ PROVEN
-/
theorem terminal_block_reindexes_as_zero_to_three :
    localCoordinate (labeledPosition 10) (labeledPosition 10) = 0 ∧
    localCoordinate (labeledPosition 10) (labeledPosition 11) = 1 ∧
    localCoordinate (labeledPosition 10) (labeledPosition 12) = 2 ∧
    localCoordinate (labeledPosition 10) (labeledPosition 13) = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    unfold localCoordinate labeledPosition <;> decide

/--
**The terminal block is `REST, bridge, bridge, seed`.**

Human positions `10,11,12,13` are not four unrelated labels. They are the
closure block of one cycle: REST at `10`, transition/bridge at `11` and `12`,
and seed at `13`.

✅ PROVEN
-/
theorem terminal_block_phase_pattern :
    (labeledPosition 10).logPhase = .rest ∧
    (labeledPosition 11).logPhase = .bridge ∧
    (labeledPosition 12).logPhase = .bridge ∧
    (labeledPosition 13).logPhase = .seed := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    unfold labeledPosition CyclePos.logPhase <;> decide

/--
**`13` closes the current cycle and opens the next scale.**

Within the terminal block anchored at `10`, the local coordinate of `13` is
`3`, so it is the last point of the closing quartet. At the same time:
- it is the seed position in the current scale's human-facing chart;
- it reduces to `0` in the residue chart;
- the step `12 → 13` is the same unit step as the next scale's `0 → 1`.

This is the formal statement of "closure of the first, seed of the next."

✅ PROVEN
-/
theorem thirteen_closes_current_cycle_and_opens_next :
    (labeledPosition 13).logPhase = .seed ∧
    localCoordinate (labeledPosition 10) (labeledPosition 13) = 3 ∧
    (13 : CyclePos) = 0 ∧
    sameStep 12 13 0 1 := by
  refine ⟨terminal_block_phase_pattern.2.2.2, ?_, full_cycle_identity,
    bridge_to_seed_step_matches_entry_step⟩
  exact terminal_block_reindexes_as_zero_to_three.2.2.2

/--
**Position 13 carries different coordinates in different charts.**

- In the human-facing label chart, `13` is the seed position.
- In the local chart anchored at `10`, it has coordinate `3`.
- In the pure residue chart of `ZMod 13`, the numeral `13` reduces to `0`.

These are not contradictions; they are different coordinate systems on the
same cyclic topology.

✅ PROVEN
-/
theorem position_thirteen_has_contextual_coordinates :
    labeledPosition 13 = seedPosition ∧
    localCoordinate (labeledPosition 10) (labeledPosition 13) = 3 ∧
    (13 : CyclePos) = 0 := by
  refine ⟨labeledPosition_thirteen_is_seed, ?_, full_cycle_identity⟩
  exact terminal_block_reindexes_as_zero_to_three.2.2.2

/--
**Every terminal block reindexes the same way.**

For any whole-cycle shift `13·s`, the block
`10 + 13·s, 11 + 13·s, 12 + 13·s, 13 + 13·s`
reindexes locally as `0,1,2,3`.

✅ PROVEN
-/
theorem terminal_block_reindexes_at_scale (s : ℕ) :
    localCoordinate (labeledPosition (10 + cycle_len * s))
      (labeledPosition (10 + cycle_len * s)) = 0 ∧
    localCoordinate (labeledPosition (10 + cycle_len * s))
      (labeledPosition (11 + cycle_len * s)) = 1 ∧
    localCoordinate (labeledPosition (10 + cycle_len * s))
      (labeledPosition (12 + cycle_len * s)) = 2 ∧
    localCoordinate (labeledPosition (10 + cycle_len * s))
      (labeledPosition (13 + cycle_len * s)) = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using localCoordinate_of_labeled_offset (10 + cycle_len * s) 0
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using localCoordinate_of_labeled_offset (10 + cycle_len * s) 1
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using localCoordinate_of_labeled_offset (10 + cycle_len * s) 2
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using localCoordinate_of_labeled_offset (10 + cycle_len * s) 3

/--
**The terminal phase pattern is scale-invariant.**

Every whole-cycle translate of the terminal block is still
`REST, bridge, bridge, seed`.

✅ PROVEN
-/
theorem terminal_block_phase_pattern_at_scale (s : ℕ) :
    (labeledPosition (10 + cycle_len * s)).logPhase = .rest ∧
    (labeledPosition (11 + cycle_len * s)).logPhase = .bridge ∧
    (labeledPosition (12 + cycle_len * s)).logPhase = .bridge ∧
    (labeledPosition (13 + cycle_len * s)).logPhase = .seed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (congrArg CyclePos.logPhase (labeledPosition_periodic 10 s)).trans
      terminal_block_phase_pattern.1
  · exact (congrArg CyclePos.logPhase (labeledPosition_periodic 11 s)).trans
      terminal_block_phase_pattern.2.1
  · exact (congrArg CyclePos.logPhase (labeledPosition_periodic 12 s)).trans
      terminal_block_phase_pattern.2.2.1
  · exact (congrArg CyclePos.logPhase (labeledPosition_periodic 13 s)).trans
      terminal_block_phase_pattern.2.2.2

/--
**Every `13 + 13·s` both closes one cycle and opens the next.**

This is the scale-invariant form of the terminal-block handoff:
- in the human-facing chart it is the seed;
- in the REST-anchored local chart it is coordinate `3`;
- in the residue chart it is `0`;
- the step into it is the same unit step as the next chart's `0 → 1`.

✅ PROVEN
-/
theorem terminal_block_closes_and_restarts_at_scale (s : ℕ) :
    (labeledPosition (13 + cycle_len * s)).logPhase = .seed ∧
    localCoordinate (labeledPosition (10 + cycle_len * s))
      (labeledPosition (13 + cycle_len * s)) = 3 ∧
    labeledPosition (13 + cycle_len * s) = seedPosition ∧
    (((13 + cycle_len * s : ℕ) : CyclePos) = 0) ∧
    sameStep ((12 + cycle_len * s : ℕ) : CyclePos)
      ((13 + cycle_len * s : ℕ) : CyclePos) 0 1 := by
  refine ⟨terminal_block_phase_pattern_at_scale s |>.2.2.2,
    terminal_block_reindexes_at_scale s |>.2.2.2, ?_, ?_, ?_⟩
  · exact (labeledPosition_periodic 13 s).trans labeledPosition_thirteen_is_seed
  · calc
      (((13 + cycle_len * s : ℕ) : CyclePos)) = ((13 : ℕ) : CyclePos) + ((cycle_len * s : ℕ) : CyclePos) := by
          simp [Nat.cast_add]
      _ = (13 : CyclePos) := by rw [full_cycle_shift_vanishes]; simp
      _ = 0 := full_cycle_identity
  · exact bridge_to_seed_step_matches_entry_step_at_scale s

/-! ### Continuous Geometry -/

/--
The 6.5 flip divides the cycle into equal halves on the continuous manifold,
even though the discrete position count is asymmetric (6 expansion + 7 contraction).
The continuous flip point maps to exactly 1/2 of the unit interval.

✅ PROVEN
-/
theorem flip_at_half : (6.5 : ℝ) / 13 = 1 / 2 := by norm_num

/--
**LOG Checkpoints**: The breathing cycle has checkpoints at positions 4, 7, 10, 13
(the boundaries between LOG phases and structural transitions).

✅ PROVEN
-/
theorem checkpoint_spacing : ∀ i : Fin 4,
    [3, 6, 9, 12].get (i.cast rfl) = 3 * (i.val + 1) := by
  intro i
  fin_cases i <;> simp

/-! ### Continuous-to-Discrete Mapping (Phase Bins) -/

/--
A continuous time `t` belongs to the discrete position `n`
if it falls within the half-open interval [n - 0.5, n + 0.5).
This rigorously maps the continuous manifold to discrete states.
-/
def in_position_bin (t : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) - 0.5 ≤ t ∧ t < (n : ℝ) + 0.5

/-! ### PRISM: Algebraic Time Generation

The PRISM experiment proves that the breathing cycle is **self-driving**.
Two static symmetries (Inversion and Reflection) compose to produce the
Successor function. No external clock is needed.

`neg(comp(x)) = x + 1`

Geometry (Foundation) + Algebra (PRISM) = Dynamics (Breathing).
-/

/--
**PRISM Operator: Complement (Inversion)**
The inversion of a state relative to the cycle maximum.
In ZMod N, this is `-(x + 1)` or equivalently `(-x) - 1`.
-/
def comp (x : CyclePos) : CyclePos := -x - 1

/--
**PRISM Operator: Negation (Reflection)**
The reflection of a state across the zero point.
-/
def neg (x : CyclePos) : CyclePos := -x

/--
**Theorem: Symmetries Generate Time (The PRISM Identity)**
Applying Complement then Negation produces the Successor (Time Tick).
`neg (comp x) = x + 1`

This proves that Time is an emergent property of static symmetries.
The cycle drives itself through the interaction of Inversion and Reflection.

✅ PROVEN
-/
theorem prism_identity (x : CyclePos) : neg (comp x) = x + 1 := by
  unfold neg comp
  ring

/--
**Corollary: Complement is an Involution**
Applying complement twice returns to the original state.
comp(comp(x)) = x

✅ PROVEN
-/
theorem comp_involution (x : CyclePos) : comp (comp x) = x := by
  unfold comp
  ring

/--
**Corollary: neg ∘ comp generates the entire cycle**
Starting from 0, repeated application of `neg ∘ comp` visits every position.
Proof: `neg(comp(0)) = 1`, `neg(comp(1)) = 2`, etc.

✅ PROVEN (base case)
-/
theorem prism_generates_from_zero : neg (comp 0) = (1 : CyclePos) := by
  unfold neg comp
  ring

end BreathingCycle
