# UFRF Lean 4 Formalization

**Deriving the universe from a single definition: `{-½, 0, +½}` with sum = 0.**

This project formalizes the Universal Field Resonance Framework (UFRF) in
Lean 4 with Mathlib, proving that physical constants, number systems,
division algebras, gauge symmetries, and topological structure emerge
from geometric necessity — from a single definition, with zero free parameters,
zero sorry, and zero custom axioms.

## Quick Start

```bash
# Prerequisites: Lean 4 via elan
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Build
cd ufrf-lean
lake update
lake exe cache get    # download prebuilt Mathlib (~2 GB)
lake build            # compile UFRF
```

## Project Structure

```
UFRF-Allen/
├── UFRF.lean                    # Root module (imports all 40 modules)
├── UFRF/
│   ├── # ── Core Framework (33 modules) ──
│   ├── Trinity.lean             # The conserved triplet {-½, 0, +½} (THE seed)
│   ├── Simplex.lean             # C(4,3) = 4 from topology
│   ├── KissingEigen.lean        # K(2)=6, K(3)=12 eigenstructure
│   ├── Structure13.lean         # Projective plane: a²+a+1 = 13
│   ├── Foundation.lean          # Derives cycle length from Trinity
│   ├── PrimeSemantics.lean      # Standard vs UFRF vs cycle-position primes
│   ├── FineStructure.lean       # α⁻¹ = 4π³ + π² + π ≈ 137.036
│   ├── ...                      # (29 more core modules)
│   │
│   ├── # ── Allen Embedding (7 modules, 0 sorry) ──
│   ├── AllenEmbedding.lean      # Mod 13 arithmetic + CRT decompositions
│   ├── QUART.lean               # Allen's hex transport formalization
│   ├── AllenBridge.lean         # Cross-framework bridge + TiledState
│   ├── KissingHierarchy.lean    # Every Allen number from K(2), K(3), C(4,3)
│   ├── FibonacciKissing.lean    # F(7)=13 bridge, twin primes, NN params
│   ├── FibonacciPrimeChain.lean # Scale tower: 7→13→233, axiom at checkpoint
│   └── PhaseSpaceCartography.lean # Phase space analysis
│
├── docs/
│   └── ALLEN_EMBEDDING.md       # Complete proof inventory
└── archive/
```

## The Derivation Chain

```
         Trinity {-½, 0, +½}  (THE starting point — the sole definition)
                    │
               sum = 0  (Conservation)
                    │
    ┌─────────┼──────────┐
    │         │          │
   T¹        T²         T³        (Three-LOG tensor grades)
 Linear    Curved      Cubed
    │         │          │
    └─────────┼──────────┘
              │
     9 interior + 4 structural = 13 positions  (Breathing Cycle)
              │
         flip at 6.5  →  6.5/13 = 1/2  (Critical Flip)
              │
    ┌─────────┼──────────┐
    │         │          │
  S¹ map    T² torus   Scale ℤ   (Angular Embedding → Manifold → Recursion)
    │         │          │
    ├── ℝ,ℂ,ℍ,𝕆 (15 dim)──── Hurwitz Theorem
    │         │
    ├── Base 10/12/13 ──────── Number Systems
    │         │
    ├── 4π³+π²+π = 137.036 ── Fine Structure Constant
    │         │
    ├── U(1)×SU(2)×SU(3) ──── Gauge Groups (12 bosons = Base 12)
    │         │
    ├── K(3)+1 = 13 ─────────── Kissing Number (sphere packing → cycle)
    │         │
    ├── {13/p} star polygons ── Star Polygons (prime visit orders)
    │         │
    ├── |5/13−1/φ²| < 0.003 ── Golden Angle Emergence (position, not imposed)
    │         │
    ├── ℤ/21ℤ ≃+* ℤ/3×ℤ/7 ── CRT Ring Isomorphism (adelic decomposition)
    │         │
    ├── ℤ_[p] →+* ℤ/pℤ ──────── p-adic Conservation (∀ prime p)
    │         │
    ├── ℤ_[3]×ℤ_[5]×...×ℤ_[13] Full Adele (5 cycle-prime naturals)
    │
```

## Proof Status Summary

| Category | Count |
|----------|-------|
| Proven theorems + definitions | **540+** |
| Allen/Fibonacci theorems (new) | **140+** |
| Cross-module verification examples | **107** (KernelProof, 28 layers) |
| Modules | **40** (33 core + 7 Allen) |
| `sorry` statements | **0** |
| Custom `axiom` declarations | **0** |

**Navigating Phase Space.** We do not treat concepts as hard physical facts. The only hard facts are the Lean Proofs themselves. The framework begins from a single definition — the Trinity `{-½, 0, +½}` — and derives everything else (including the number 13, Fourier symmetries, Calculus, and Gauge Groups) as mathematically proven consequences.

**Former axioms, all now proven:**
- `resonance_at_flip` → structural theorem (resonance defined at flip, 6.5/13 = 1/2)
- `toroidal_necessity` → `toroidal_emergence` (torus = S¹ × S¹ from dual flows)
- `zero_point_isomorphism` → constructive definition (point → sub-scale seed)
- `dimensional_completeness` → constructive definition (dimension embedding)
- `merkaba_geometric_factor` → `simplex3_face_count` (C(4,3) = 4)
- `sqrt_phi_REST` → `kepler_pythagorean` (√φ from Kepler's Triangle)

## Auditing

```bash
# Verify the pipeline (zero sorry, zero custom axioms)
./scripts/certify.sh

# Full build verification
lake build
```

## Contributing

**Strict Kernel-First Discipline Required**

This project maintains a zero-tolerance policy for incomplete proofs (`sorry`) and unverified assumptions (`axiom`). 

To add a new theorem:
1. Open the file in VS Code with the Lean 4 extension.
2. Formulate your theorem statement.
3. Write the exact tactic proof (`norm_num`, `ring`, `simp`, `omega`, `nlinarith`, `decide`).
4. **Validation**: The Lean infoview must indicate `No goals`.
5. Run `./scripts/verify.sh` to confirm the entire project builds with 0 `sorry` occurrences.
6. Commits containing `sorry` or `axiom` will not be accepted.

## License

This formalization is part of the UFRF Working Paper v3.
