# UFRF Proof Documentation - Index

## Overview

This directory contains selected human-readable proof notes for the current
Lean 4 formalization.

It is not a complete one-to-one index of every current Lean module. Some notes
were written against earlier snapshots and are best used as orientation rather
than as a full theorem inventory.

When there is any mismatch:

- the Lean source is canonical,
- [`docs/README.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/README.md),
  [`docs/REVIEW_GUIDE.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/REVIEW_GUIDE.md),
  and [`docs/FAQ.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/FAQ.md) are the
  current reviewer-facing entry points.

## Current High-Signal Note

- [`25_ResidueContourSlice.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/25_ResidueContourSlice.md):
  exact proved surface for `ResidueDefinition` and
  `CircleIntegralBreathing`, including the current proof boundary for the
  specific contour package around `1 / (z^13 - 1)`.

## Selected Note Index

### Foundations

- [`01_Trinity.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/01_Trinity.md)
- [`02_ThreeLOG.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/02_ThreeLOG.md)
- [`03_BreathingCycle.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/03_BreathingCycle.md)
- [`20_Constants.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/20_Constants.md)
- [`21_Simplex.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/21_Simplex.md)
- [`22_KeplerTriangle.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/22_KeplerTriangle.md)
- [`23_Structure13.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/23_Structure13.md)
- [`24_Foundation.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/24_Foundation.md)

### Geometry, Dynamics, And Arithmetic

- [`05_GoldenAngle.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/05_GoldenAngle.md)
- [`06_Manifold.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/06_Manifold.md)
- [`09_AngularEmbedding.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/09_AngularEmbedding.md)
- [`10_Recursion.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/10_Recursion.md)
- [`11_DivisionAlgebras.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/11_DivisionAlgebras.md)
- [`12_NumberBases.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/12_NumberBases.md)
- [`14_Noether.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/14_Noether.md)
- [`15_Calculus.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/15_Calculus.md)
- [`16_Projections.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/16_Projections.md)
- [`17_Waveform.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/17_Waveform.md)
- [`18_PrimeChoreography.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/18_PrimeChoreography.md)
- [`19_Addressing.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/19_Addressing.md)
- [`27_NumerizationSeeds.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/27_NumerizationSeeds.md)

### Interpretation-Heavy Historical Notes

- [`04_FineStructure.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/04_FineStructure.md)
- [`07_Phenomena.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/07_Phenomena.md)
- [`08_Riemann.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/08_Riemann.md)
- [`13_Monster.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/13_Monster.md)

These are useful for context, but they should be read with the Phase 4 fence in
mind: explanatory language in these notes is not automatically a proved theorem
claim.

## How To Use This Folder

1. Start with [`docs/REVIEW_GUIDE.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/REVIEW_GUIDE.md)
   for an audit path.
2. Use [`docs/FAQ.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/FAQ.md) for the
   `definition` / `theorem` / `interpretation` / `open` fence.
3. Use the files in this folder for focused module notes or theorem inventories.

## Verification

To verify the current repo state:

```bash
cd /Users/dcharb/Documents/UFRF-Lean-V2
lake build
./scripts/verify.sh
./scripts/certify.sh
```

These checks confirm the current Lean source, not the historical wording of any
individual proof note.
