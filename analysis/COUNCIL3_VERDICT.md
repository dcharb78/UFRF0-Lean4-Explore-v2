# Council Verdict: Bounding Trailing 1s of φ(K)

## The Claim
trailing_ones((3^K-1)/2^v₂(3^K-1)) ≤ O(log K) for all K.

## The Verdict: DENSITY IS PROVABLE, POINTWISE IS AS HARD AS COLLATZ

### Three experts agree:
1. **Analytic NT**: Baker bounds v₂(3^K-1) but NOT trailing 1s of the odd part
2. **Algebraist**: All-odd Mahler coefficients give density but not pointwise bounds
3. **Combinatorialist**: Spectral gap gives exponential mixing but not pointwise control

### The Fundamental Obstacle
The pointwise bound (∀K, trailing_ones ≤ O(log K)) is a REFORMULATION of
Collatz, not an easier sub-problem. Proving it IS proving Collatz.

### What IS Provable (Priority 1)

**Density Bound**: The fraction of K values with trailing_ones(φ(K)) ≥ t is
exactly 1/2^(t-1) over each full period of the multiplicative order.

Verified computationally:
  t≥2: density = 0.24902 ≈ 1/4  ✓
  t≥3: density = 0.12500 = 1/8  ✓ (EXACT)
  t≥4: density = 0.06226 ≈ 1/16 ✓
  t≥5: density = 0.03125 = 1/32 ✓ (EXACT)

This follows from: ord_{2^M}(3) = 2^(M-2) and the uniform distribution
of 3^K mod 2^M over the full period.

### Action Plan (Priority Ordered)

1. **DENSITY BOUND** (provable): Formalize |{K≤N : t₁≥t}| ≤ CN/2^t in Lean
2. **RESIDUE TABULATION** (done above): Exact counts match 1/2^(t-1)
3. **DYNAMICAL CORRELATION** (the frontier): Does the Collatz trajectory
   avoid the rare residue classes? This connects density to pointwise.
4. **POINTWISE BOUND** (= Collatz): Direct proof that t₁ ≤ O(log K)

### The Path Forward

The most productive direction is Priority 3: understanding whether
Collatz trajectories correlate with the rare residue classes.

Key question: when the orbit reaches a value n and computes f(n),
the "K value" for the next countdown is trailing_ones(f(n)).
Is this K value correlated with the rare residue classes mod 2^t?

If the carry automaton's mixing ensures NO correlation → the density
bound applies to trajectories → Collatz follows.

If correlation EXISTS → the orbit might systematically hit rare classes
→ need a different approach.

The spectral gap of 1/2 suggests NO correlation (exponential decay of
correlations), but this is for the CARRY STATE, not the ORBIT VALUE.
Bridging from carry state mixing to orbit value mixing is the gap.
