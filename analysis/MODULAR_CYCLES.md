# Modular Cycles: All Artifacts, All Expanding

## Finding

At each scale mod 2^k, the Syracuse map has:
- ONE fixed point: r=1 (at every scale k=2..13)
- Non-trivial modular cycles appearing at k ≥ 10

## The Cycles (All Artifacts)

| Scale | Cycle Length | Seed | Avg v₂ | Drift | Integer Orbit |
|-------|-------------|------|--------|-------|---------------|
| mod 2^10 | 26 | r=47 | 1.423 | EXPANDING | Shrinks at step 34 |
| mod 2^11 | 25 | r=91 | 1.480 | EXPANDING | Shrinks at step 28 |
| mod 2^12 | 7 | r=703 | 1.286 | EXPANDING | Shrinks at step 51 |
| mod 2^12 | 6 | r=871 | 1.167 | EXPANDING | Shrinks at step 22 |

All cycles are:
- **EXPANDING** (avg v₂ < log₂3 ≈ 1.585)
- **ARTIFACTS** (integer orbits do NOT cycle — they escape and shrink)
- **Analogous to** the period-14 cycle at k=13 in the 13·2^k tower

## "Only 0-9 Exist"

At each scale: finitely many patterns, one fixed point, a few artifact cycles.
The artifact cycles resolve at finer scales (obstruction killing).
The carry automaton composes the finite patterns across scales.
The composition across ALL scales IS the Collatz conjecture.
