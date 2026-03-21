# Phenomena - Mapping Physical Constants

## Overview
This module records chart addresses for specific real-world phenomena in the
coordinate system `(depth : ℤ, phase : ZMod 13)`.

## Key Definitions

### Coordinate System
```lean
structure Coordinate where
  depth : ℤ
  phase : Phase  -- ZMod 13
```

The selected phenomena discussed here are assigned explicit chart addresses on
the manifold.

---

## Proven Theorems

### **Theorem: α⁻¹ Projects to Phase 7**
```lean
theorem alpha_inv_projects_to_phase_7 :
    (Int.floor ufrf_alpha_inv : ZMod 13) = (7 : ZMod 13)
```

**Proof Strategy**:
1. Use `alpha_inv_floor_137` from `FineStructure` to establish `⌊ufrf_alpha_inv⌋ = 137`
2. Compute `137 ≡ 7 (mod 13)` via `rfl`

**Significance**: The calculated value projects arithmetically to phase label `7`
in the 13-cycle chart. This is an address statement, not a standalone theorem
about a distinct physical sector.

**Red Team III Fix**: This theorem now uses the **direct projection** from the calculated polynomial, not a hardcoded integer.

---

### **Theorem: Prime 137 Phase is 7**
```lean
theorem prime_137_phase_is_7 :
    (nat_to_phase 137 : ZMod 13) = (7 : ZMod 13)
```
**Proof**: `rfl`

**Significance**: The integer `137` maps arithmetically to phase label `7`, and
the natural number `7` is prime. This is an arithmetic/chart fact only; it is
not a theorem that phase `7` carries a separate repo-level structural-prime
status.

---

### **Theorem: Refined Alpha Address Runs Into the Handoff**
```lean
theorem alpha_coordinate_refined_handoff_path :
    (alpha_coordinate_refined.advance 2).phase = restPhase ∧
    (alpha_coordinate_refined.advance 3).phase = (10 : Phase) ∧
    (alpha_coordinate_refined.advance 4).phase = (11 : Phase) ∧
    (alpha_coordinate_refined.advance 5).phase = (12 : Phase) ∧
    Coordinate.step (alpha_coordinate_refined.advance 5) = ⟨11, 0⟩
```
**Proof**: direct computation from `alpha_coordinate_refined = ⟨10, 7⟩`, `Coordinate.advance`, and `Coordinate.step`.

**Significance**: the refined alpha address is not just “at phase 7.” It sits a
fixed number of unit steps before the terminal handoff: two steps before REST,
then bridge, bridge, seed/closure, and then re-entry at the next depth.

---

## Addressing Principle

The module uses addresses `A(P) = (S, p)` for the phenomena it tracks, where:
- `S` is the scale depth (integer)
- `p` is the phase position (ZMod 13)

### Examples

**Fine Structure Constant**:
```lean
def alpha_coordinate : Coordinate :=
  { depth := 0, phase := 7 }
```

**Electron Mass** (Placeholder):
```lean
def electron_mass_address : Coordinate :=
  { depth := -1, phase := 0 }
```

---

## Prime Distribution Hypothesis

This section is contextual and not formalized by the theorems in this module.
The basic arithmetic mapping is:

$$p \mapsto (\text{depth}, p \bmod 13)$$

This records a charting heuristic only. It is not a proved general theorem
about prime distribution or structural phase roles.
