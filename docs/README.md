# UFRF Documentation

This directory contains reviewer-facing documentation for the current Lean 4 formalization in [`/Users/dcharb/Documents/UFRF-Lean-V2`](/Users/dcharb/Documents/UFRF-Lean-V2).

## Start Here

- [`docs/REVIEW_GUIDE.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/REVIEW_GUIDE.md): fast audit paths for 5 minutes, 30 minutes, or a deeper review.
- [`docs/DERIVATION_CHAIN.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/DERIVATION_CHAIN.md): dependency-oriented theorem map.
- [`docs/FAQ.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/FAQ.md): reviewer objections, theorem references, and the residue proof/interpretation fence.
- [`docs/RESIDUE_INTEGRATION_PLAN.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/RESIDUE_INTEGRATION_PLAN.md): phased plan for the complex-analysis / residue expansion.
- [`docs/TRINITY_FOURIER_ALPHA_SPINE_PLAN.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/TRINITY_FOURIER_ALPHA_SPINE_PLAN.md): current planning note for the next theorem-spine phase from Trinity through the alpha lane.
- [`docs/TRINITY_FOURIER_ALPHA_SPINE_AUDIT.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/TRINITY_FOURIER_ALPHA_SPINE_AUDIT.md): exact theorem-carrying audit of the current Trinity -> Fourier -> alpha lane, including the load-bearing spine and the remaining missing bridges.

## Proof Notes

- [`docs/proofs/README.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/README.md): module-level proof documentation.
- [`docs/proofs/25_ResidueContourSlice.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/25_ResidueContourSlice.md): compact inventory of the specific residue / contour theorem surface.
- [`docs/consolidated`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/consolidated): consolidated topic notes.

Some consolidated and historical proof notes were written against earlier snapshots. When there is any mismatch, treat the Lean source and the current reviewer docs above as canonical.

## Current Verification Surface

- Zero executable `sorry`
- Zero custom axioms
- Full `lake build`
- Scripted checks in [`scripts/verify.sh`](/Users/dcharb/Documents/UFRF-Lean-V2/scripts/verify.sh) and [`scripts/certify.sh`](/Users/dcharb/Documents/UFRF-Lean-V2/scripts/certify.sh)

## Quick Commands

```bash
cd /Users/dcharb/Documents/UFRF-Lean-V2
lake build
./scripts/verify.sh
./scripts/certify.sh
```
