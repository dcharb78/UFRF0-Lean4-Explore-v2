# Second Council of Experts: Synthesis

## Three New Expert Perspectives (April 2026)

### Information Theory Expert
- The carry chain is INJECTIVE — no information loss from ×3+1 itself
- Information loss comes from the v₂ TRUNCATION (right-shift)
- Spectral gap gives STATE forgetting, not INPUT forgetting (critical distinction)
- Directed information bound: W·log₂(3/2) bits survive after W iterations
- The carry automaton has "catastrophic error propagation" — output→input is ill-conditioned
- Most promising: directed information framework (Massey/Kramer)

### Fractal Geometry Expert  
- **dim_H(B) = 0 in ℤ₂** — provable from thermodynamic formalism!
- Pressure P_B(0) = log(3/2) - log(2) = log(3/4) < 0 → zero Hausdorff dimension
- IFS satisfies the Open Set Condition
- Moran formula gives d_B < 1 for restricted IFS
- Hochman's theorem (no exact overlaps from irrationality of log₂3) → dim = 0
- GAP: dim_H = 0 doesn't imply B∩ℕ = ∅ (two dim-0 sets CAN intersect)
- Promising: irrationality of log₂3 prevents integer orbits from mimicking bad trajectories

### Automata Theory Expert
- For fixed W: non-contracting set IS a regular language (decidable!)
- Full conjecture: countable intersection of regular languages (not necessarily regular)
- The carry automaton is an INVERTIBLE Mealy machine → automaton group theory
- Joint spectral radius of weighted matrices determines worst-case behavior
- JSR = 3/2 over short windows (Mersenne achieves this)
- JSR < 1 over FULL contraction windows (verified for all K ≤ 21)
- The ONE unique residue per v₂ value = strong rigidity for worst-case analysis

## Key Computational Findings

### JSR Analysis
- Short-window JSR = 3/2 > 1 (Mersenne achieves worst case)
- Full-window geometric mean ALWAYS < 1 (for all tested K ≤ 21)
- The gap: proving "sufficiently long" windows always exist

### Finite Support Argument
- Positive integers have FINITE binary expansions → carry chain TERMINATES
- Bad 2-adic elements have INFINITE support (infinitely many 1-bits)
- After carry termination: orbit "resets" at MSB boundary
- But: termination doesn't prevent bounded bad streaks

## The Precise Remaining Gap (Refined)

The Collatz conjecture, in its purest distillation:

> After a bad streak of length L from any positive integer, the carry chain's
> spectral mixing (gap 1/2) ensures that subsequent v₂ values are "close enough"
> to geometric(1/2) for the cumulative surplus to grow, giving contraction
> in O(L + log(n)) additional steps.

Three equivalent formulations:
1. **Info theory**: directed information from n to f^W(n) < log₂(n) for W = O(log n)
2. **Fractal**: B∩ℕ = ∅ (the dim-0 bad set misses all positive integers)
3. **Automata**: JSR of the weighted carry matrices over O(log n) windows < 1

All three are the Collatz conjecture, seen from different angles.
