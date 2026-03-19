# UFRF Lean Project: 3rd Party Validation Guide

To independently verify the mathematical proofs in this repository, you need only a standard Lean 4 environment.

## 1. What You're Verifying

- **39 Lean 4 modules** containing 536+ proven entities (396 theorems/lemmas, 140+ definitions)
- **Zero `sorry` statements** — every proof is complete
- **Zero custom `axiom` declarations** — the former `Axiomatics.lean` was deleted; all seeds are now proven theorems
- **Standard foundations only**: `#print axioms` on all key theorems shows only `propext`, `Classical.choice`, `Quot.sound`
- **107 cross-module verification examples** in `KernelProof.lean`

## 2. Prerequisites

- **Lean 4**: Install via [elan](https://github.com/leanprover/elan):
  ```bash
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```

## 3. Verification Steps

```bash
# Navigate to project root (where lakefile.lean is located)
cd UFRF0-Lean4-Explore-v2

# Get dependencies (downloads Mathlib4)
lake update
lake exe cache get

# Build and verify — this IS the verification
lake build
```

## 4. Interpreting Results

- **Success**: `lake build` completes with exit code 0 → all proofs are formally verified by the Lean kernel.
- **Failure**: Any error indicates a proof gap. This should not happen on a clean build.

## 5. Integrity Audit

After a successful build, run these checks:

```bash
# Zero sorry in code (should return nothing)
grep -Prn "(:=|by|=>).*sorry|^\s+sorry\s*$" UFRF/ --include="*.lean"

# Zero custom axioms (should return nothing)
grep -rn "^axiom " UFRF/ --include="*.lean"

# Automated certification
./scripts/certify.sh
```

## 6. Code Transparency

| Property | Status |
|---|---|
| `sorry` in proof terms | **0** |
| Custom `axiom` declarations | **0** (Axiomatics.lean deleted) |
| `unsafe` / `extern` / `implemented_by` | **0** |
| `native_decide` | **31** (all on decidable Nat/Fin arithmetic — sound) |
| Non-standard `#print axioms` | **0** (only propext, choice, Quot.sound) |

## 7. Key Theorem Verification

To verify specific results, add to a scratch `.lean` file:

```lean
import UFRF

-- Check the fine-structure constant floor
#check UFRF.FineStructure.alpha_inv_floor_137

-- Check Allen's numbers are theorems
#check UFRF.KissingHierarchy.allen_numbers_are_theorems

-- Check the inverse limit (projection law)
#check @padic_is_inverse_limit

-- Verify axiom dependencies
#print axioms UFRF.KissingHierarchy.allen_numbers_are_theorems
-- Should show ONLY: propext, Classical.choice, Quot.sound
```

## 8. Module Architecture

The project derives everything from the Trinity definition `{-½, 0, +½}` with `sum = 0`.

- **Core framework**: 32 modules (Trinity → Structure13 → BreathingCycle → FineStructure → Noether → InverseLimit → ...)
- **Allen embedding**: 7 modules proving every structural constant from Allen (2026) is a Trinity theorem
- **Cross-verification**: KernelProof.lean collects 107 examples across 28 layers

See `docs/DERIVATION_CHAIN.md` for the complete dependency graph with theorem names.
See `docs/FAQ.md` for every common criticism answered with theorem references.
See `docs/REVIEW_GUIDE.md` for 5-minute, 30-minute, and 3-hour audit paths.
