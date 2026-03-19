# Allen Embedding: Proof Inventory

## Relationship

Allen's QUART hex transport and UFRF's 13-position breathing cycle describe
**complementary levels** of the same structure:
- **UFRF**: dynamics at each vertex (the 13-cycle)
- **Allen**: spatial organization of vertices (the hex lattice)

Neither is "above" or "below" the other.

---

## Proven (zero `sorry`, compiled by Lean 4)

### AllenEmbedding.lean — Arithmetic & Group Theory

| Theorem | Statement | Tactic |
|---------|-----------|--------|
| `allen_transport_space_mod13` | (144 : ZMod 13) = 1 | decide |
| `allen_symmetry_quotient_mod13` | (7 : ZMod 13) = 7 | decide |
| `allen_alpha_floor_mod13` | (137 : ZMod 13) = 7 | decide |
| `allen_boundary_mod13` | (42 : ZMod 13) = 3 | decide |
| `allen_phase_states_mod13` | (24 : ZMod 13) = 11 | decide |
| `allen_closure_mod13` | (96 : ZMod 13) = 5 | decide |
| `transport_space_is_identity` | (12 * 12 : ZMod 13) = 1 | decide |
| `alpha_floor_decomposition` | 137 = 12² - 7 | norm_num |
| `boundary_factored` | (6 * 7 : ZMod 13) = 3 | decide |
| `closure_factored` | (24 * 4 : ZMod 13) = 5 | decide |
| `both_frameworks_137` | 144 - 7 = 137 | norm_num |
| `symmetry_is_contraction_start` | (7 : ZMod 13) = (137 : ZMod 13) | decide |
| `six_divides_twelve` | 6 ∣ 12 | norm_num |
| `Z12_projects_to_Z6` | ∃ ring hom Z₁₂ →+* Z₆ | castHom |
| `six_not_divides_thirteen` | ¬(6 ∣ 13) | norm_num |
| `twelve_intervals` | 13 - 1 = 12 | norm_num |
| `intervals_per_face` | 12 / 6 = 2 | norm_num |
| `CRT_Z78` | Z₇₈ ≅ Z₆ × Z₁₃ | chineseRemainder |
| `CRT_Z24` | Z₂₄ ≅ Z₈ × Z₃ | chineseRemainder |
| `two_twelve_not_coprime` | ¬Coprime(2, 12) | decide |
| `Z3_is_trinity` | 3 = trinity_dimension | simp |
| `CRT_Z156` | Z₁₅₆ ≅ Z₁₂ × Z₁₃ | chineseRemainder |

### QUART.lean — Allen's Transport System

| Theorem | Statement | Tactic |
|---------|-----------|--------|
| `opposite_involution` | opposite(opposite(f)) = f | fin_cases |
| `sectors_eq_faces` | 24 / 4 = 6 | simp |
| `symmetry_count` | globalSymmetryModes = 7 | simp |
| `raw_state_count` | 24 * 6 = 144 | norm_num |
| `independent_modes` | 144 - 7 = 137 | simp |
| `ring7_boundary` | 6 * 7 = 42 | norm_num |
| `closure_length` | 24 * 4 = 96 | norm_num |
| `circuit_structure` | 4 * 6 = 24 ∧ 24 * 4 = 96 | simp |
| `steps_per_circuit` | 24 / 4 = 6 | simp |
| `total_transport_steps` | 96 / 4 = 24 | simp |

### AllenBridge.lean — Cross-Framework Connections

| Theorem | Statement | Tactic |
|---------|-----------|--------|
| `scale_gap` | 13² - 12² = 25 | norm_num |
| `scale_gap_is_square` | 13² - 12² = 5² | norm_num |
| `allen_144_is_interior` | 12² = 144 | norm_num |
| `ufrf_scale2` | 13² = 169 | norm_num |
| `bridge_plus_one` | 13 = 12 + 1 | norm_num |
| `curvature_denom` | 252 = 12 × 21 | norm_num |
| `twenty_one_factors` | 21 = 3 × 7 | norm_num |
| `curvature_full_factorization` | 252 = 12 × 3 × 7 | norm_num |
| `multi_scale_positions` | 24 × 13 = 312 | norm_num |
| `multi_scale_closure` | 96 × 13 = 1248 | norm_num |
| `closure_factorization` | 1248 = 13 × 8 × 12 | norm_num |
| `phases_are_parity_times_intervals` | 24 = 2 × 12 | norm_num |
| `face_interval_correspondence` | 12 / 6 = 2 | norm_num |
| `phase_advance_decomposition` | 4 = 2 × 2 | norm_num |
| `combined_state_count` | 144 × 13 = 1872 | norm_num |
| `z24_trinity_connection` | 3 = trinity_dim ∧ 8 = 13-5 | simp/norm_num |

---

## Conjectured (`sorry` — genuine open work)

| Theorem | File | What's Needed |
|---------|------|---------------|
| `full_state_closure` | QUART.lean | Determining Allen's exact parity-weighted turning rule. Simulation of all simple parity-offset rules (exit = opposite ± k) shows spatial closure at 6-12 steps, not 96. Either the turning rule is more complex, or "96" counts phase ticks (24 × 4) rather than transport steps. This is a genuine hex geometry challenge. |
| `formula_comparison` | AllenBridge.lean | Proving |Allen's α⁻¹ - UFRF's α⁻¹| < δ for some small δ. Requires Lean interval arithmetic with π bounds. Both formulas give values near 137.036 but from different structures. Whether they are algebraically related or coincidentally close is the central open question. |

---

## Open (cannot even state the theorem yet)

1. **Multi-scale coupling dynamics**: How does a breathing cycle at one hex vertex couple to the cycle at an adjacent vertex through a shared face? The `TiledState` structure is defined but no coupling step function exists.

2. **Curvature derivation**: Can Allen's δ₀ = 5π/(252√3) be derived from UFRF's scale-boundary arithmetic (5 = √(13² - 12²), 252 = 12 × 3 × 7)?

3. **Why both formulas agree**: Is there a deeper algebraic identity connecting 4π³ + π² + π to 137 + 5π/(252√3)(1 + ε₁ + ε₂)? Or is the agreement numerical coincidence?
