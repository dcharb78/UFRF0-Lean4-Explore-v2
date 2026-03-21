# BreathingCycle - The 13-Position Cycle

## Overview
The 13-position breathing cycle is the discrete manifestation of the Trinity's self-relation through the three LOG grades.

## Key Definitions

### `CyclePos`
```lean
abbrev CyclePos := ZMod cycle_len
```
A position in the 13-position cycle, represented as a modular ring so whole
cycle shifts vanish automatically.

### `LogPhase`
```lean
inductive LogPhase where
  | log1_linear    -- Positions 1–3
  | log2_curved    -- Positions 4–6
  | log3_cubed     -- Positions 7–9
  | rest           -- Position 10
  | bridge         -- Positions 11–12
  | seed           -- Position 13
```

---

## Proven Theorems

### **Expansion or Contraction**
```lean
theorem expansion_or_contraction (p : CyclePos) :
    p.isExpansion ∨ p.isContraction
```
**Proof**: `omega` (linear arithmetic).

**Significance**: Every position is either in the expansion half (1–6) or contraction half (7–13). The flip at 6.5 is the boundary.

---

### **Not Both**
```lean
theorem not_both (p : CyclePos) :
    ¬(p.isExpansion ∧ p.isContraction)
```
**Proof**: `simp` (contradiction).

**Significance**: Expansion and contraction are mutually exclusive.

---

### **Expansion Count**
```lean
theorem expansion_count :
    (Finset.univ.filter (λ p => p.val < 6)).card = 6
```
**Proof**: `rfl` (definitional).

**Significance**: Exactly 6 positions in the expansion half.

---

### **Contraction Count**
```lean
theorem contraction_count :
    (Finset.univ.filter (λ p => p.val ≥ 6)).card = 7
```
**Proof**: `rfl`

**Significance**: Exactly 7 positions in the contraction half. The asymmetry (6 vs 7) reflects the bridge/seed transition.

---

### **Bridge-Seed Wraps**
```lean
theorem bridge_seed_wraps : 
    (seedPosition.val + 1) % 13 = entryPosition.val
```
**Proof**: `simp`

**Significance**: Position 13 (seed) wraps to Position 1 (entry), establishing toroidal topology.

---

### **Closure vs Re-entry**
```lean
theorem fourteen_restarts_after_thirteen :
    labeledPosition 13 = seedPosition ∧
    labeledPosition 14 = entryPosition ∧
    sameStep 13 14 0 1
```
**Proof**: direct modular reduction in the human-facing label chart.

**Significance**: `13` is the closure/seed label of the current cycle, while
`14` is the first re-entry label of the restarted cycle. This separates closure
from restart instead of treating them as the same chart position.

---

### **Terminal Handoff Block**
```lean
theorem terminal_block_handoff_reindexes_at_scale (s : ℕ) :
    localCoordinate (labeledPosition (10 + cycle_len * s))
      (labeledPosition (10 + cycle_len * s)) = 0 ∧
    localCoordinate (labeledPosition (10 + cycle_len * s))
      (labeledPosition (11 + cycle_len * s)) = 1 ∧
    localCoordinate (labeledPosition (10 + cycle_len * s))
      (labeledPosition (12 + cycle_len * s)) = 2 ∧
    localCoordinate (labeledPosition (10 + cycle_len * s))
      (labeledPosition (13 + cycle_len * s)) = 3 ∧
    localCoordinate (labeledPosition (10 + cycle_len * s))
      (labeledPosition (14 + cycle_len * s)) = 4
```
**Proof**: repeated use of `localCoordinate_of_labeled_offset` after a whole-cycle shift.

**Significance**: the tail is not just `13` by itself. At every scale the
handoff block is `REST, bridge, bridge, seed, re-entry`, locally reindexed as
`0,1,2,3,4`.

---

### **Scale-Invariant Re-entry**
```lean
theorem fourteen_restarts_after_thirteen_at_scale (s : ℕ) :
    labeledPosition (13 + cycle_len * s) = seedPosition ∧
    labeledPosition (14 + cycle_len * s) = entryPosition ∧
    sameStep (13 + cycle_len * s) (14 + cycle_len * s) 0 1
```
**Proof**: periodicity of `labeledPosition` together with modular reduction of the unit step.

**Significance**: `14` is the first label of the restarted cycle at every
scale, not just in the base chart.

---

### **PRISM Step Iteration**
```lean
theorem prism_step_iterate_from_zero (n : ℕ) :
    ((fun x : CyclePos => neg (comp x))^[n]) 0 = (n : CyclePos)
```
**Proof**: induction using `prism_identity : neg (comp x) = x + 1`.

**Significance**: The local cycle walk is literally `0 -> 1 -> 2 -> ...`.

---

### **Every Position Is Reached**
```lean
theorem prism_step_hits_every_position (x : CyclePos) :
    ∃ n : ℕ, ((fun y : CyclePos => neg (comp y))^[n]) 0 = x
```
**Proof**: choose `n = x.val` and reduce with `prism_step_iterate_from_zero`.

**Significance**: The PRISM walk really does hit all 13 positions.

---

### **Periodic After One Full Cycle**
```lean
theorem prism_step_periodic_from_zero (n : ℕ) :
    ((fun x : CyclePos => neg (comp x))^[n + cycle_len]) 0 =
      ((fun x : CyclePos => neg (comp x))^[n]) 0
```
**Proof**: rewrite by `prism_step_iterate_from_zero` and use that a full cycle
shift vanishes in `ZMod 13`.

**Significance**: The smallest cycle does not stop at 13; it repeats forever.

---

### **Flip at Half**
```lean
theorem flip_at_half : 
    (6.5 : ℝ) / 13 = 1 / 2
```
**Proof**: `norm_num`

**Significance**: The 6.5 flip divides the cycle into equal halves on the continuous manifold.

---

### **Checkpoint Spacing**
```lean
theorem checkpoint_spacing : 
    ∀ i : Fin 4,
    [3, 6, 9, 12].get (i.cast rfl) = 3 * (i.val + 1)
```
**Proof**: `fin_cases` + `simp`

**Significance**: The LOG checkpoints occur at positions 4, 7, 10, 13 (multiples of 3, offset by 1).

---

## Phase Binning (Red Team III)

### `in_position_bin`
```lean
def in_position_bin (t : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) - 0.5 ≤ t ∧ t < (n : ℝ) + 0.5
```

**Purpose**: Rigorously maps continuous values to discrete positions. A value `t` belongs to position `n` if it falls within the half-open interval `[n - 0.5, n + 0.5)`.

**Significance**: Eliminates "approximate" mappings. For example, the Golden Angle (~4.966) is **proven** to be in Position 5's bin, not merely "close to 5".
