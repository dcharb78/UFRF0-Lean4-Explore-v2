# UFRF Structural Index — Context Anchor

**Purpose:** Complete map of every constant, scale, concurrent dimension, and
cross-scale bridge in the repo. Use this to maintain context across agents/sessions.

---

## A. The Number Map

Every significant number, every context it appears in, and how they connect.

### Core Constants

| Number | Primary Role | Appearances |
|--------|-------------|-------------|
| **1** | Unity, observer, identity | `system_unity`, U(1) dim, `closure_cost`, `overlap_retention` target |
| **2** | Parity, polarity | `polarity_count`, Fin 2 in ConcurrentState, Cayley-Dickson factor, excluded from UFRF primes |
| **3** | THE generator | Trinity dimension, LOG grades, `uniqueness_of_three`, Cayley-Dickson doublings, SU(2) dim, F(4)=3 |
| **4** | Simplex faces | C(4,3)=4, `structural_overhead`, Log3 duality_factor, `phaseAdvance`, Fin 4 in ConcurrentState |
| **5** | Scale boundary | √(13²−12²)=5, K(2)−1=5, F(5)=5, delta0 numerator coefficient, golden angle position |
| **6** | 2D kissing | K(2)=6, hex faces, T(3)=6, gauge rank sum 1+2+3=6, K(3)/2=6 |
| **7** | 2D flip threshold | K(2)+1=7, `globalSymmetryModes`, 137 mod 13=7, tower start, F(7)=13 |
| **8** | Octonion dim | dim(O)=2³=8, SU(3) dim=8, 13−5=8, Z8 factor of Z24 |
| **9** | Interior modes | 3×3=9, 13−4=9, rest index position |
| **12** | 3D kissing | K(3)=12, gauge bosons 1+3+8=12, visible−Trinity=15−3=12, F(12)=144=K(3)², Fin 12 in ConcurrentState |
| **13** | Cycle length | 3²+3+1=13, K(3)+1=13, F(7)=13, ZMod 13 ring, gauge+observer=13 |
| **15** | Visible dims | 1+2+4+8=15, K(3)+3=15 |

### Allen/Derived Constants

| Number | Formula | Role |
|--------|---------|------|
| **24** | 2×K(3) | Phase states, Fin 2 × Fin 12, twin sum 11+13, Allen phases |
| **42** | K(2)×(K(2)+1) | Coherence boundary d=2, ring-7 boundary |
| **96** | 2×K(3)×C(4,3) | Transport closure, \|ConcurrentState\|, 96 mod 13 = 5 |
| **137** | K(3)²−(K(2)+1) | Fine structure floor, ⌊4π³+π²+π⌋, 144−7 |
| **144** | K(3)² = F(K(3)) | Full 3D phase space, 144 mod 13 = 1 |
| **233** | F(K(3)+1) = F(13) | Next scale cycle length, Fibonacci prime |
| **252** | K(3)×3×(K(2)+1) | Curvature denominator, 12×3×7 |

### Mod 13 Residue Map (Allen → Cycle Position)

| Allen Constant | mod 13 | Cycle Meaning |
|---------------|--------|---------------|
| 144 (raw states) | 1 | Identity |
| 7 (symmetry) | 7 | Contraction start |
| 137 (α floor) | 7 | Contraction start |
| 42 (boundary) | 3 | Trinity |
| 24 (phases) | 11 | Bridge start |
| 96 (closure) | 5 | Golden angle |

---

## B. The Scale Ladder

### Scale 0: Trinity (Pre-Geometric)
- **Structure:** {−½, 0, +½} in ℚ
- **Content:** Conservation, polarity, mediation. No cycle yet.
- **Output:** generator a = 3

### Scale 1: The 13-Cycle
- **Structure:** ZMod 13
- **Derivation:** projective_order(3) = 13, also K(3)+1 = 13
- **Interior:** 9 positions (3 grades × 3 modes) + 4 structural = 13
- **Phases:** Log1(1–3), Log2(4–6), flip@6.5, Log3(7–9), REST(10), Bridge(11–12), Seed(13=0)
- **Gauge:** 12 bosons (1+3+8) + 1 observer = 13
- **Output:** F(13) = 233 seeds Scale 2

### Scale 2: The 233-Cycle
- **Structure:** ZMod 233 (conjectural)
- **Derivation:** F(13) = 233, prime
- **Interior:** 232
- **Address space:** 13² = 169; scale gap = 169−144 = 25 = 5²
- **Output:** F(233) = ? seeds Scale 3

### Allen 2D Scale (Parallel, not below/above Scale 1)
- **Structure:** Hex lattice, K(2) = 6 neighbors
- **Cycle:** K(2)+1 = 7
- **Boundary:** K(2)×(K(2)+1) = 42
- **Relation:** Complementary to Scale 1. Allen = spatial tiling, UFRF = dynamics at each node.

---

## C. Concurrent Dimensions at Scale 1

These coexist simultaneously — orthogonal aspects, not sequential stages.

| Dimension | Structure | Value | Key Theorem |
|-----------|-----------|-------|-------------|
| Cycle | ZMod 13 | 13 positions | `cycle_has_13_positions` |
| Kissing | K(3) | 12 neighbors | `kissing_number_3d` |
| Simplex | C(4,3) | 4 faces | `simplex3_face_count` |
| Parity | Fin 2 | 2 states | `polarity_count` |
| Gauge U(1) | lieDim(1) | 1 boson | `gaugeLieDim_log1` |
| Gauge SU(2) | lieDim(2) | 3 bosons | `gaugeLieDim_log2` |
| Gauge SU(3) | lieDim(3) | 8 bosons | `gaugeLieDim_log3` |
| Division alg | Cayley-Dickson | dims 1,2,4,8 (=15) | `visible_dimension_count` |
| LOG phase | 3 grades | Log1, Log2, Log3 | `LogPhase` |

### Proven Products of Concurrent Dimensions

| Product | Formula | Value | Theorem |
|---------|---------|-------|---------|
| Concurrent state | Parity × Kissing × Simplex | 2×12×4 = **96** | `concurrent_state_count` |
| Phase states | Parity × Kissing | 2×12 = **24** | `allen_phases_from_kissing` |
| Full phase space | K(3)² | 12² = **144** | `allen_states_from_kissing` |
| Coherence boundary | K(3) × (K(3)+1) | 12×13 = **156** | `ufrf_boundary_from_kissing` |
| Multi-scale positions | Phase × Cycle | 24×13 = **312** | `multi_scale_positions` |
| Multi-scale closure | Concurrent × Cycle | 96×13 = **1248** | `multi_scale_closure` |
| Combined states | Full × Cycle | 144×13 = **1872** | `combined_state_count` |

---

## D. Cross-Scale Bridges

### Type 1: Fibonacci Escalation (scale → next scale)

| Theorem | Bridge | File |
|---------|--------|------|
| `fibonacci_kissing_bridge` | F(K(2)+1) = F(7) = 13 = K(3)+1 | FibonacciKissing |
| `chain_7_to_13` | nextScale(7) = 13 | FibonacciPrimeChain |
| `chain_13_to_233` | nextScale(13) = 233 | FibonacciPrimeChain |
| `allen_transport_is_fibonacci` | F(K(3)) = 144 = K(3)² | FibonacciKissing |

### Type 2: Kissing Dimensional Projection (2D ↔ 3D)

| Theorem | Bridge | File |
|---------|--------|------|
| `kissing_2d_half_3d` | K(2)×2 = K(3) | KissingEigen |
| `twin_sum_K2_is_K3` | (K(2)−1)+(K(2)+1) = K(3) | FibonacciKissing |
| `alpha_floor_from_kissing` | K(3)²−(K(2)+1) = 137 | KissingHierarchy |

### Type 3: CRT Decompositions

| Theorem | Isomorphism | Significance |
|---------|-------------|--------------|
| `CRT_Z78` | ℤ/78 ≃ ℤ/6 × ℤ/13 | Allen ⊥ UFRF |
| `CRT_Z24` | ℤ/24 ≃ ℤ/8 × ℤ/3 | Phase = (13−5) × Trinity |
| `CRT_Z156` | ℤ/156 ≃ ℤ/12 × ℤ/13 | Intervals × Cycle |

### Type 4: p-adic Conservation (fine → coarse)

| Theorem | Bridge | File |
|---------|--------|------|
| `conservation_at_every_depth` | ℤ/13² → ℤ/13 preserves sum=0 | Noether |
| `conservation_from_infinite_depth` | ℤ_[13] → ℤ/13ⁿ preserves sum=0 | Noether |
| `conservation_universal_prime` | Same for ANY prime p | Noether |

### Type 5: Gauge-Geometry-Packing Convergences

| Theorem | What Converges |
|---------|---------------|
| `kissing_equals_gauge` | K(3) = 1+3+8 = 12 |
| `kissing_from_hurwitz` | K(3) = 15−3 |
| `both_integer_parts_137` | Allen 144−7 = UFRF 12²−7 = 137 |
| `five_convergence` | F(5)=5, K(2)−1=5, √(13²−12²)=5 |

### Type 6: Group Embedding (structural impossibility)

| Theorem | Statement |
|---------|-----------|
| `six_divides_twelve` | Z6 embeds in Z12 (intervals) |
| `six_not_divides_thirteen` | Z6 CANNOT embed in Z13 (positions) |

Allen's hex is a substructure of INTERVALS (Z12), not POSITIONS (Z13).

---

## E. Master Derivation Flow

```
Trinity {-½, 0, +½}
  │
  ├── 3 (generator)
  │     ├── 13 = 3²+3+1 (cycle)
  │     ├── 9 = 3×3 (interior)
  │     ├── 4 = C(4,3) (simplex)
  │     └── 6 = T(3) (gauge sum)
  │
  ├── 2 (polarity)
  │     ├── 1,2,4,8 (Cayley-Dickson)
  │     ├── 15 = 1+2+4+8 (visible)
  │     ├── 12 = 15-3 = K(3)
  │     └── 6 = 12/2 = K(2)
  │
  ├── 1,2,3 (tensor powers)
  │     ├── 1,3,8 (gauge dims)
  │     ├── 12 = 1+3+8 (bosons)
  │     └── 1,1,4 (duality → α)
  │
  └── Fibonacci layer (cross-scale)
        F(7)=13, F(12)=144, F(13)=233
```
