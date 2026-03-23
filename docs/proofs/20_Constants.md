# Constants - Fundamental Values

## Overview
The fundamental constants used throughout the UFRF formalization.

## Key Definitions

### `phi` (Golden Ratio)
```lean
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2
```

**Value**: ~1.618

**Significance**: The Golden Ratio appears in:
- The Golden Angle (360°/φ²)
- The REST amplitude (√φ)
- Fibonacci sequences

---

### `tau` (Breathing Cycle Period)
```lean
def tau : ℕ := 13
```

**Value**: 13

**Significance**: The breathing cycle has exactly 13 positions.

---

### `golden_angle_degrees`
```lean
noncomputable def golden_angle_degrees : ℝ := 360 / (phi ^ 2)
```

**Value**: ~137.5°

**Significance**: The Golden Angle in degrees, which maps to Position 5 on the cycle.

---

### `ufrf_prime_number`
```lean
def ufrf_prime_number : ℕ := 137
```

**Value**: 137

**Significance**: The "UFRF Prime" is 137, which is:
- The floor of α⁻¹
- A prime number itself
- Has chart label 7 (mod 13)

---

## Proven Theorems

### **Theorem: Phi is Golden**
```lean
theorem phi_is_golden : 
    phi ^ 2 = phi + 1
```
**Proof**: Algebraic manipulation + `field_simp`.

**Significance**: The defining property of the Golden Ratio.

---

### **Theorem: Tau is Thirteen**
```lean
theorem tau_is_thirteen : 
    tau = 13
```
**Proof**: `rfl`

**Significance**: The breathing cycle period is exactly 13.

---

### **Theorem: Golden Angle Value**
```lean
theorem golden_angle_value : 
    137 < golden_angle_degrees ∧ golden_angle_degrees < 138
```
**Proof**: Bounds on φ.

**Significance**: The Golden Angle is approximately 137.5°, connecting to the fine structure constant.

---

## Derived Constants

### `ufrf_tensor_structure`
```lean
noncomputable def ufrf_tensor_structure : ℝ := 
    4 * Real.pi ^ 3 + Real.pi ^ 2 + Real.pi
```

**Value**: ~137.036

**Significance**: The polynomial that generates the fine structure constant inverse.

---

### `ufrf_alpha_inv`
```lean
noncomputable def ufrf_alpha_inv : ℝ := 
    ufrf_tensor_structure
```

**Value**: ~137.036

**Significance**: The UFRF prediction for α⁻¹, matching the empirical value to 99.9998% accuracy.
