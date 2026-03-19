# UFRF Proofs: Dynamics & Waveform

This document consolidates the dynamics-related modules.

---

## 1. Waveform - The Universal Breathing Shape

### Overview
The waveform W(t) describes the "breathing" of the system, derived rigorously from ThreeLOG axioms.

### Segments
- **[0, 3)**: Seed/Log1 (Linear) — `t/3`
- **[3, 6)**: Expansion/Log2 (Quadratic) — `1 + (1/9)(t-3)²`
- **[6, 6.5)**: Peak — `peak_amplitude` (= 2, derived from Trinity)
- **[6.5, 9)**: Contraction/Log3 (Cubic) — `2 - (8/125)(t-6.5)³`
- **[9, 10.5)**: REST — `√φ` (derived from Kepler)
- **[10.5, 12)**: Bridge — Linear decay
- **[12, 13)**: Seed/Return

### Boundary Matching (NEW — Phase 21)
All LOG transitions are value-continuous:
- `seed_expansion_match` : seed(3) = expansion(3) = 1
- `expansion_peak_match` : expansion(6) = peak = 2
- `peak_contraction_match` : contraction(6.5) = peak = 2

### Derivations
- `unique_expansion_parabola`: Only one parabola satisfies f(3)=1, f(6)=2
- `unique_contraction_cubic`: Only one cubic satisfies f(6.5)=2, f(9)=1

### Calculus
- `expansion_deriv_at_3 = 0` (stationary start of parabola)
- `log1_log2_impulse`: Derivative discontinuity at t=3 (phase transition)

---

## 2. PrimeChoreography - Prime Superposition Dynamics

### Overview
The "choreography" of primes on the breathing cycle.

### Key Definitions
- **UFRF Prime Set**: `{1} ∪ {p | prime(p), p ≠ 2}`
- **prime_phase(p)**: `p mod 13` (ZMod 13 residue)

### Proven Theorems
- `one_is_ufrf_prime`, `two_is_not_ufrf_prime`
- Every standard prime other than `2` is UFRF-prime
- The terminal block `10,11,12,13` reindexes contextually as `0,1,2,3`

---

## Summary

- **Waveform**: Rigorously derived from LOG grades with 3 boundary matching proofs
- **Phase transitions**: Discontinuous derivatives at LOG boundaries are features
- **Prime Choreography**: Primes distributed across ZMod 13 phases
