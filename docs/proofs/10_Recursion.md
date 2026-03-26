# Recursion - Scale Handoff and Unbounded Descent

## Overview
`UFRF/Recursion.lean` packages the safe recursion reading used elsewhere in the
repo:

- scale is indexed by `ℤ`, so there is no bottom scale,
- the bridge-to-seed strip is explicit,
- the terminal handoff `13 ↦ 3`, `14 ↦ 4` repeats at every whole-cycle
  translate.

This is a scale-indexed repetition claim. It does **not** prove a single
coinductive Lean object containing all scales simultaneously, and it does not
by itself justify broader physical claims beyond the formal scale/handoff
package.

---

## Key Definitions

### `Scale`
```lean
abbrev Scale := ℤ
```

Scales are indexed by the integers, so the formal scale parameter has no
minimum element.

### `BreathingCycleAt`
```lean
structure BreathingCycleAt (s : Scale) where
  positions : Fin UFRF.Foundation.derived_cycle_length
```

At each indexed scale, the local cycle still has exactly 13 positions.

### `accumulatedDepth`
```lean
def accumulatedDepth (n : ℕ) : ℕ := 15 ^ n
```

This records the visible depth count across `n` nested levels.

---

## Proven Theorems

### **Theorem: No First Step**
```lean
theorem no_first_step (s : Scale) : ∃ s' : Scale, s' < s
```

**Proof**: choose `s - 1`.

**Significance**: there is no smallest indexed scale.

---

### **Theorem: Two- and Three-Scale Depth**
```lean
theorem two_scale_depth : accumulatedDepth 2 = 225
theorem three_scale_depth : accumulatedDepth 3 = 3375
```

**Proof**: simplification of `15 ^ n`.

**Significance**: these are the explicit depth counts currently exposed by the
module.

---

### **Theorem: Bridge to Seed**
```lean
theorem bridge_to_seed (k : Fin 3) :
    ((10 + k.val + 3) % UFRF.Foundation.derived_cycle_length : ℕ) = k.val
```

**Proof**: finite case split on the three bridge/seed indices.

**Significance**: the terminal bridge strip is explicitly re-read as the
next-scale seed strip.

---

### **Theorem: Terminal Chart Matches Seed Strip**
```lean
theorem bridge_to_seed_matches_terminal_chart (k : Fin 3) :
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition 10)
        (BreathingCycle.labeledPosition (11 + k.val)) =
      (k.val + 1 : BreathingCycle.CyclePos) ∧
    ((10 + k.val + 3) % UFRF.Foundation.derived_cycle_length : ℕ) = k.val
```

**Proof**: finite case split plus `bridge_to_seed`.

**Significance**: the local terminal chart is exactly “REST + next-scale seed
strip.”

---

### **Theorem: Scale-Invariant Terminal Chart**
```lean
theorem bridge_to_seed_matches_terminal_chart_at_scale (s : ℕ) (k : Fin 3) :
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * s))
        (BreathingCycle.labeledPosition (11 + k.val + BreathingCycle.cycle_len * s)) =
      (k.val + 1 : BreathingCycle.CyclePos) ∧
    ((10 + k.val + 3) % UFRF.Foundation.derived_cycle_length : ℕ) = k.val
```

**Proof**: transport the same terminal chart along whole-cycle translates.

**Significance**: the bridge/seed strip is stable at every indexed scale.

---

### **Theorem: No Terminal Scale Handoff**
```lean
theorem no_first_step_and_terminal_handoff_at_scale (s : Scale) (t : ℕ) :
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4
```

**Proof**: combine `no_first_step` with
`BreathingCycle.terminal_block_handoff_reindexes_at_scale`.

**Significance**: this is the repo’s honest packaged form of “the cycle never
just ends.” There is no bottom scale, and at every whole-cycle translate the
terminal handoff still exposes closure at `13` and re-entry at `14`.

---

### **Theorem: PRISM Walk and Terminal Handoff**
```lean
theorem prism_walk_and_terminal_handoff_at_scale (s : Scale) (t : ℕ) :
    BreathingCycle.neg (BreathingCycle.comp 0) = (1 : BreathingCycle.CyclePos) ∧
    (∀ x : BreathingCycle.CyclePos,
      ∃ n : ℕ, ((fun y : BreathingCycle.CyclePos => BreathingCycle.neg (BreathingCycle.comp y))^[n]) 0 = x) ∧
    ((13 : ℕ) : BreathingCycle.CyclePos) = 0 ∧
    (∃ s' : Scale, s' < s) ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (13 + BreathingCycle.cycle_len * t)) = 3 ∧
    BreathingCycle.localCoordinate
        (BreathingCycle.labeledPosition (10 + BreathingCycle.cycle_len * t))
        (BreathingCycle.labeledPosition (14 + BreathingCycle.cycle_len * t)) = 4 ∧
    BreathingCycle.sameStep (13 + BreathingCycle.cycle_len * t)
      (14 + BreathingCycle.cycle_len * t) 0 1
```

**Proof**: combine `BreathingCycle.prism_generates_from_zero`,
`BreathingCycle.prism_step_hits_every_position`,
`BreathingCycle.full_cycle_identity`,
`no_first_step_and_terminal_handoff_at_scale`, and
`BreathingCycle.fourteen_restarts_after_thirteen_at_scale`.

**Significance**: this is the lower-layer package for the current three-part
structural reading. The same cyclic object supports:
- the seed walk `0 -> 1 -> 2 -> ...`,
- the pure cycle identity `13 = 0`,
- the local terminal chart `13 ↦ 3`, `14 ↦ 4`,
- and the fact that this handoff persists with no bottom scale.

The middle bullets are coordinate-system views, not rival facts: `13` is seed
in the human-facing chart, local `3` in the REST-anchored chart, and `0` in
the pure cycle chart.

This is still a scale-indexed cycle/recursion statement, not a single
all-scales object and not an observer/projection claim.

---

## Safe Reading

The current formal recursion package supports the following claims:

- there is no bottom indexed scale,
- the bridge-to-seed strip is explicit,
- the universal PRISM walk from `0` reaches every cycle position,
- the pure cycle chart and the local terminal chart are both kept in play,
- the local closure/re-entry handoff repeats at every whole-cycle translate.

The current formal recursion package does **not** support the following stronger
claims:

- a single Lean object containing all scales simultaneously,
- automatic promotion from scale-indexed repetition to unrestricted physical
  universality across all scientific regimes.
