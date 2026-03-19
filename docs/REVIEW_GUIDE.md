# UFRF Review Guide

**How to audit this repository in 5 minutes, 30 minutes, or 3 hours.**

---

## 5-Minute Audit (Trust Nothing)

```bash
git clone https://github.com/dcharb78/UFRF0-Lean4-Explore-v2.git
cd UFRF0-Lean4-Explore-v2
lake update
lake exe cache get
lake build
```

Build succeeds → every theorem is verified. Now check for gaps:

```bash
# Zero sorry (should return nothing, or only in comments)
grep -Prn "(:=|by|=>).*sorry|^\s+sorry\s*$" UFRF/ --include="*.lean"

# Zero custom axioms (should return nothing)
grep -rn "^axiom " UFRF/ --include="*.lean"
```

**Build passes + zero sorry + zero axioms = mathematics verified.**

---

## 30-Minute Audit

Read these files in order:

### Step 1: The Starting Point (2 min)
**`UFRF/Trinity.lean`** — Three rationals: -½, 0, +½. Sum = 0. Key: `trinity.conservation`, `trinity_symmetry`, `trinity_uniqueness`, `trinity_is_minimal_two`.

### Step 2: Why 3, Why 13 (3 min)
**`UFRF/Structure13.lean`** — `uniqueness_of_three`: a = 3 forced. `uniqueness_of_thirteen`: 3²+3+1 = 13. Pure arithmetic.

### Step 3: The Breathing Cycle (5 min)
**`UFRF/BreathingCycle.lean`** — 13 positions. `flip_at_half`: 6.5/13=1/2. `prism_identity`: neg(comp(x))=x+1. Time from symmetry.
Check the contextual chart theorems too: `terminal_block_reindexes_as_zero_to_three` formalizes `10,11,12,13 ↦ 0,1,2,3`, and `thirteen_closes_current_cycle_and_opens_next` states that 13 is both the closure of the current cycle and the seed-opening of the next.

### Step 4: Where 137 Comes From (5 min)
**`UFRF/Simplex.lean`** → **`UFRF/ThreeLOG.lean`** → **`UFRF/FineStructure.lean`**
Chain: `simplex3_face_count` (C(4,3)=4) → `log3_geometric_factor_is_four` → `alpha_inv_floor_137` (⌊4π³+π²+π⌋=137).

### Step 5: The Allen Embedding (10 min)
**`UFRF/KissingHierarchy.lean`** → **`UFRF/FibonacciKissing.lean`**
`allen_numbers_are_theorems`: all 8 Allen constants from Trinity. `fibonacci_kissing_bridge`: F(7)=13. Check these are pure arithmetic.

### Step 6: The Inverse Limit (5 min)
**`UFRF/InverseLimit.lean`** — `padic_is_inverse_limit`: both directions of projection law via Mathlib's PadicInt API.

---

## 3-Hour Audit

### Hour 1: Read Every Module

40 modules. Read theorem STATEMENTS (compiler verified proofs).

```
Core (33 modules):
□ Trinity          □ Structure13      □ Simplex
□ ThreeLOG         □ KeplerTriangle   □ Foundation
□ BreathingCycle   □ Constants        □ PrimeSemantics
□ AngularEmbedding
□ Addressing       □ Manifold         □ Recursion
□ DivisionAlgebras □ NumberBases      □ FineStructure
□ Waveform         □ PrimeChoreography □ GoldenAngle
□ Projections      □ Noether          □ Calculus
□ Phenomena        □ PRISMAlgebra     □ Padic
□ InverseLimit     □ Adele            □ StarPolygon
□ PositionalPhase  □ KissingEigen     □ Fourier
□ AxiomAudit       □ KernelProof

Allen (7 modules):
□ KissingHierarchy    □ AllenEmbedding
□ QUART               □ AllenBridge
□ FibonacciKissing    □ FibonacciPrimeChain
□ PhaseSpaceCartography
```

### Hour 2: Trace the Chain

Open `docs/DERIVATION_CHAIN.md`. Follow any path from `trinity.conservation` to a leaf. For each arrow, verify the import exists.

### Hour 3: Adversarial Testing

1. Change `trinity.neg` to `-1/3`. Rebuild. Should fail.
2. Change `uniqueness_of_thirteen` to claim 12. `norm_num` rejects it.
3. Add `theorem test : False := by sorry`. Verify warning. Remove.
4. Run `#print axioms allen_numbers_are_theorems`. Only propext, choice, Quot.sound.
5. `grep -rn "^axiom " UFRF/` returns nothing.

---

## Repo Statistics

| Metric | Value |
|---|---|
| Modules | 40 (33 core + 7 Allen) |
| Theorems + lemmas | 396 |
| Definitions | 140 |
| Total proven entities | 536+ |
| `sorry` in code | 0 |
| Custom axioms | 0 |
| `native_decide` (all decidable) | 31 |
| Cross-module verifications | 107 (KernelProof) |
| Standard foundations | propext, Classical.choice, Quot.sound only |
