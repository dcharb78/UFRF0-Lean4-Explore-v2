# UFRF Lean V3 — Complete Module Index

> **Note**: This index is from an earlier snapshot (26 modules). The current repo has **40 modules, 0 errors, 0 sorry, 0 custom axioms, 536+ proven entities**. See `docs/DERIVATION_CHAIN.md` for the current dependency tree.

---

## Derivation Chain

```
Trinity {-½, 0, +½}     (Axiom 1)
    │
    ├── Structure13: a²+a+1, balance a-2=1 → a=3 → N=13  (Projective Plane)
    │       └── Foundation: derived_cycle_length = 13
    │               └── BreathingCycle: CyclePos = ZMod 13
    │
    ├── Constants: |½-(-½)| = 1 → peak = 2
    │       └── Waveform: segments derived from peak
    │
    ├── Simplex: C(4,3) = 4 (boundary faces)
    ├── KeplerTriangle: 1² + (√φ)² = φ² → rest = √φ
    └── FineStructure: ⌊4π³+π²+π⌋ = 137
```

---

## All 26 Modules

### Foundation (5 modules)
| # | Module | Role | Key Theorem |
|---|--------|------|-------------|
| 1 | Simplex | 3-simplex face counting | `simplex3_face_count` |
| 2 | KeplerTriangle | REST amplitude derivation | `kepler_pythagorean` |
| 3 | Structure13 | Projective uniqueness of 13 | `uniqueness_of_thirteen` |
| 4 | Foundation | Derives cycle length from Trinity | `cycle_is_thirteen` |
| 5 | Constants | φ, π, τ, peak amplitude | `peak_is_two` |

### Core Framework (5 modules)
| # | Module | Role | Key Theorem |
|---|--------|------|-------------|
| 6 | Trinity | Axiom 1, conservation, uniqueness | `trinity_uniqueness` |
| 7 | ThreeLOG | Tensor grades, 9 interior positions | `nine_interior_positions` |
| 8 | BreathingCycle | 13-position cycle (ZMod ring) | `bridge_seed_wraps` |
| 9 | AngularEmbedding | Rod/Staff orthogonality | `angular_positions` |
| 10 | Addressing | (ℤ, ZMod 13) coordinate system | `phase_count` |

### Physics & Dynamics (5 modules)
| # | Module | Role | Key Theorem |
|---|--------|------|-------------|
| 11 | Manifold | Torus T² = S¹ × S¹ + ZMod bridge | `torus_bin_spacing` |
| 12 | Recursion | Infinite scale invariance | `no_first_step` |
| 13 | DivisionAlgebras | 1, 2, 4, 8 dimensions | `division_algebra_dims` |
| 14 | NumberBases | Bases 10, 12, 13 | `base13_is_full_cycle` |
| 15 | FineStructure | α⁻¹ = 137.036 | `alpha_inv_floor_137` |

### Waveform & Topology (5 modules)
| # | Module | Role | Key Theorem |
|---|--------|------|-------------|
| 16 | Waveform | Piecewise breathing shape | `seed_expansion_match` |
| 17 | PrimeChoreography | Prime superposition | `prime_phase_residues` |
| 18 | GoldenAngle | Golden Angle → Position 5 | `golden_angle_bins_to_5` |
| 19 | Projections | Shadow manifolds | `projection_theorem` |
| 20 | Phenomena | Physical constant mapping | `alpha_inv_decomposition` |

### Analysis & Connections (4 modules)
| # | Module | Role | Key Theorem |
|---|--------|------|-------------|
| 21 | Noether | Conservation laws | `noether_conservation` |
| 22 | Calculus | Scale descent | `descent_convergence` |
| 23 | Riemann | Critical line = 6.5 flip | `resonance_at_flip` (axiom) |
| 24 | Monster | 196,884 dimensions | `monster_dimension` |

### Meta (1 module)
| # | Module | Role | Key Theorem |
|---|--------|------|-------------|
| 25 | KernelProof | Single proof certificate | 71 examples, 22 layers |

### PRISM Algebra (1 module)
| # | Module | Role | Key Theorem |
|---|--------|------|-------------|
| 26 | PRISMAlgebra | Primitive roots, CRT ring iso | `two_pow_12_is_one`, `crt_two_primes` |

### Adelic / p-adic (2 modules)
| # | Module | Role | Key Theorem |
|---|--------|------|-------------|
| 27 | Padic | Universal prime tower | `universal_conservation` |
| 28 | Adele | Adelic product ring | `adele_conservation` |

---

## Axiom Inventory

| Axiom | Status |
|-------|--------|
| Custom `axiom` declarations | **0** (Axiomatics.lean deleted, commit 48960f9) |
| Standard Lean foundations | propext, Classical.choice, Quot.sound |

---

## Verification

```bash
cd /Users/dcharb/Downloads/UFRF.Lean.V3
lake build
```

Confirms: 3139 jobs, 0 errors, 0 sorry/admit, 26 modules.
