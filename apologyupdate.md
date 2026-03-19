You're absolutely right, and that's actually exactly what Allen was criticizing us for not doing. His paper is published, his transport rules are specified, and he literally told us in his email: "24 phase states × 4 phase advances required for closure = 96. Anyone who knows a simple hexagonal lattice architecture could understand that."

He gave us the answer key and told us to do the homework. So let me actually do it.

From his paper and his email, we have everything we need:

**The transport rules, explicitly stated:**

The QUART chamber has a hexagonal boundary with 6 faces. Internal phase propagation is circular with 24 ordered states. Each sector subtends 24/6 = 4 phase positions. Transport is face-to-face through opposite faces. Parity alternates at each step. The ring-7 boundary has 6 × 7 = 42 cells. Transport closure occurs at 96 steps because 24 phase states require 4 complete circuits (his email confirmed: "24 × 4 = 96").

His paper also specifies the 7 global symmetry modes (3 translations + 3 rotations + 1 scaling), the primary curvature term 5π/(252√3), and both correction terms ε₁ = 1/(42² × 7) and ε₂ = π/(2√3)/(42 × 96). The full formula is stated explicitly.

So the revised plan has **no sorry statements that blame Allen for missing information.** Every sorry should be either a genuine mathematical difficulty we haven't solved yet, or a Lean technicality we need to work through. The QUART transport is fully specified. We should be able to formalize it completely.

The updated `QUART.lean` module should look like:

```lean
namespace QUART

-- All from published paper + author clarification

-- Hex lattice directions (axial coordinates)
def hexDir : ZMod 6 → ℤ × ℤ
  | 0 => (1, 0)    -- East
  | 1 => (0, 1)    -- NE
  | 2 => (-1, 1)   -- NW
  | 3 => (-1, 0)   -- West (opposite face 0)
  | 4 => (0, -1)   -- SW (opposite face 1)
  | 5 => (1, -1)   -- SE (opposite face 2)

-- Phase advance per face crossing: one sector = 4 positions
def phaseAdvance : ZMod 24 := 4

-- Opposite face: entry face + 3 (mod 6)
def oppositeFace (f : ZMod 6) : ZMod 6 := f + 3

-- The full transport state
structure State where
  phase : ZMod 24
  face : ZMod 6
  parity : ZMod 2
  pos : ℤ × ℤ

-- Transport step: fully determined by chamber geometry
def step (s : State) : State where
  phase := s.phase + phaseAdvance
  face := oppositeFace s.face  -- exit through opposite
  parity := s.parity + 1
  pos := (s.pos.1 + (hexDir (oppositeFace s.face)).1,
          s.pos.2 + (hexDir (oppositeFace s.face)).2)

-- Global symmetry modes (from paper)
def globalSymmetryModes : ℕ := 3 + 3 + 1  -- translations + rotations + scaling

-- Published results - all should be PROVABLE from above
theorem raw_states : 24 * 6 = 144 := by norm_num
theorem independent_modes : 144 - 7 = 137 := by norm_num
theorem ring7_boundary : 6 * 7 = 42 := by norm_num
theorem closure_length : 24 * 4 = 96 := by norm_num

-- The curvature terms (these involve reals, harder in Lean)
-- δ₀ = 5π/(252√3)
-- ε₁ = 1/(42² × 7)  
-- ε₂ = π/(2√3)/(42 × 96)
-- α⁻¹ = 137 + δ₀(1 + ε₁ + ε₂)

end QUART
```

The remaining genuine challenges are:

**The spatial closure proof.** We defined `step` but proving that `step^[96]` returns to the initial state requires tracking the hex lattice position through 96 iterations. With the straight-through opposite-face rule, the path goes in a straight line and never closes — which means the parity alternation must modify the exit face selection in a way that creates turning. Allen's paper says "parity-weighted transport closure" but doesn't fully specify the turning rule in the notation I can extract from the PDF. His email says the arithmetic is simple, meaning there's a straightforward hex geometry fact I'm not seeing about how parity alternation creates a closed spatial path. That's the piece to work through computationally before formalizing.

**The real-valued curvature terms.** Lean 4 with Mathlib handles reals, but proving that 137 + 5π/(252√3) × (1 + 1/(42² × 7) + π/(2√3)/(42 × 96)) = 137.035999084 requires either exact real arithmetic or bounding arguments. This is a Lean technicality, not a mathematical gap.

**The connection to UFRF's α⁻¹.** Both formulas produce values near 137.036 from different structures. Proving any relationship between 4π³ + π² + π and 137 + 5π/(252√3)(1+ε) is a real mathematical question — are these two expressions algebraically related, or do they just happen to land near the same number?

So the honest framing isn't "here's where I need your help" — it's "I formalized your published system, here's what I can prove from it, and here's the genuine open question: are these two formulas related or coincidentally close?" That's a question between equals, not a request for missing information.

Not quite. There are a few gaps that would bite you mid-proof. Let me identify them precisely.

**Gap 1: The `step` function is almost certainly wrong.**

I defined it to always exit through the opposite face regardless of parity. But if that's the rule, the lattice path is a straight line forever and never closes. Allen says "parity-weighted transport closure" — meaning parity MUST affect the exit face selection. The step function should look more like:

```lean
def step (s : State) : State :=
  let exitFace := if s.parity = 0 
    then oppositeFace s.face          -- even parity: straight through
    else oppositeFace s.face + 1      -- odd parity: rotated by 60°
  { phase := s.phase + phaseAdvance,
    face := exitFace + 3,  -- enter next chamber through opposite of exit
    parity := s.parity + 1,
    pos := (s.pos.1 + (hexDir exitFace).1,
            s.pos.2 + (hexDir exitFace).2) }
```

But I'm guessing at the +1 rotation. It could be -1 (other chirality), or +2, or something else entirely. The specific turning rule determines the spatial closure length. My simulation earlier showed that +1 and -1 both give spatial closure at 12 steps, not 96. So either the turning is more subtle, or "96" counts something other than transport steps (like total phase position ticks across 4 complete circuits where each circuit IS 24 steps with spatial closure at 24 not 12).

This is the single biggest gap. You'd need to either work through the hex geometry more carefully or computationally test different turning rules until one gives exactly 96-step closure for the full state (phase + face + parity + position).

**Gap 2: The `hexDir` function won't type-check as written.**

ZMod 6 doesn't pattern-match on 0,1,2,3,4,5 in Lean 4. You'd need something like:

```lean
def hexDir (f : Fin 6) : ℤ × ℤ :=
  match f with
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (0, 1)
  | ⟨2, _⟩ => (-1, 1)
  | ⟨3, _⟩ => (-1, 0)
  | ⟨4, _⟩ => (0, -1)
  | ⟨5, _⟩ => (1, -1)
```

Or use `ZMod.val` to convert to `ℕ` first. This matters because `ZMod 6` is a quotient type, not `Fin 6`, and the Lean elaborator will reject naive pattern matching on it. You'll need to decide early whether to use `ZMod 6` (for ring structure and Mathlib compatibility) or `Fin 6` (for clean pattern matching). Similar issue for `ZMod 24` and `ZMod 2`.

**Gap 3: Missing Mathlib import list.**

I didn't specify the exact imports needed. For the plan to be actionable:

```lean
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Algebra
import Mathlib.GroupTheory.Subgroup.Basic  
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
```

But these need to be cross-checked against what v3_explore's `lakefile.lean` already imports from Mathlib. If v3_explore uses an older Mathlib pin, some of these paths may differ.

**Gap 4: I didn't specify how to actually PROVE the Z₆ ↪ Z₁₂ embedding.**

I stated the theorem but left it sorry. The actual proof needs:

```lean
theorem Z6_embeds_Z12 : 
    ∃ (f : ZMod 6 →+ ZMod 12), Function.Injective f := by
  refine ⟨{  
    toFun := fun x => 2 * (ZMod.castHom (by norm_num : 6 ∣ 12) (ZMod 12) x)
    ... }, ?_⟩
  -- Actually this approach is wrong. The natural embedding is:
  -- ZMod 6 → ZMod 12 via x ↦ 2x (maps 0,1,2,3,4,5 to 0,2,4,6,8,10)
  -- This is injective and a group homomorphism
  sorry
```

Even this sketch has issues. The clean way is `ZMod.castHom` which exists in Mathlib when the modulus divides, but it maps x ↦ x (mod 6 to mod 12), which sends {0,1,2,3,4,5} → {0,1,2,3,4,5} ⊂ Z₁₂. That IS injective and IS a ring homomorphism. So:

```lean
theorem Z6_embeds_Z12 : 
    Function.Injective (ZMod.castHom (show 6 ∣ 12 by norm_num) (ZMod 12)) := by
  exact ZMod.castHom_injective (by norm_num)
```

Whether `ZMod.castHom_injective` exists in Mathlib or needs to be constructed from `ZMod.val_cast_of_lt` and friends — that's something you'll discover during implementation.

**Gap 5: The real-number curvature comparison.**

I said "this is a Lean technicality" but didn't give you the approach. For comparing Allen's and UFRF's α⁻¹ formulas, the cleanest route in Lean 4 with Mathlib is bounding:

```lean
-- Allen's formula
noncomputable def allen_alpha_inv : ℝ := 
  137 + (5 * Real.pi) / (252 * Real.sqrt 3) * 
  (1 + 1 / (42^2 * 7) + Real.pi / (2 * Real.sqrt 3) / (42 * 96))

-- UFRF's formula  
noncomputable def ufrf_alpha_inv : ℝ := 
  4 * Real.pi^3 + Real.pi^2 + Real.pi

-- The comparison: how close are they?
theorem formulas_differ_by : 
    |allen_alpha_inv - ufrf_alpha_inv| < 0.001 := by
  -- This requires norm_num extensions for pi bounds
  -- or native_decide with interval arithmetic
  sorry
```

Proving real inequalities involving π in Lean is genuinely hard. The Mathlib approach uses `Real.pi_gt_three` and `Real.pi_lt_four` for coarse bounds, or Brent-style interval arithmetic for tighter ones. This may be a Phase 5 problem rather than something to tackle early.

**Gap 6: I never specified how to connect QUART.lean to the existing UFRF modules.**

The bridge theorems I described depend on what's actually in `BreathingCycle.lean`, `Addressing.lean`, and `Projections.lean`. Without reading those files, I was guessing at type signatures. The imports might look like:

```lean
import UFRF.BreathingCycle  -- for Position type, expansion/contraction
import UFRF.Addressing      -- for ZMod 13 infrastructure
import UFRF.FineStructure   -- for UFRF's α⁻¹
import UFRF.QUART           -- for Allen's system
```

But whether `BreathingCycle` exports a `Position` type, or whether `Addressing` uses `ZMod 13` directly or wraps it in a custom type — these determine whether the bridge theorems type-check. You'll know once you audit.

---

**So to answer your question directly:** the plan has about 80% of what you need. The 20% missing is:

1. The exact parity-dependent turning rule (solvable computationally — run simulations with different rules until one gives 96-step full-state closure)
2. The ZMod vs Fin typing decision and pattern-matching approach
3. The specific Mathlib proof terms for the embedding theorems
4. Knowledge of what the existing v3_explore modules actually export

Items 2-4 you'll resolve in the first hour of implementation. Item 1 is the real work — getting Allen's spatial transport right. Want me to write a Python script that systematically tests all possible parity-alternating hex turning rules to find the one that gives 96-step closure?