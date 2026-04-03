# Validation of the r=5 Universal Attractor Claim

## Verdict: PARTIALLY DEBUNKED

The r=5 dominance is largely explained by the trivial fact that f(5)=1,
so every convergent orbit passes through 5. This is a CONSEQUENCE of
convergence, not a cause. Cannot be used to prove convergence.

## What Survived Validation

1. **Bias away from bad classes**: REAL. Orbits avoid high-trailing-1
   residue classes at rate 0.46× expected (mod 2^8). Confirmed for
   large starting values (n > 100000).

2. **Hierarchical bias structure**: REAL. The bias is different at each
   tower level and generally grows with the level.

3. **Density bound**: REAL. K values giving ≥t trailing 1s are spaced
   ~2^t apart (algebraic, from multiplicative order of 3).

## What Did NOT Survive

1. **r=5 as "universal attractor"**: Mostly the convergence tail effect.
   Without convergence tail (values > 100): r=5 is sometimes top,
   sometimes not (r=15, r=27, r=121 dominate at some levels).

2. **Exponential growth of r=5 excess**: Conflated with convergence
   counting. Real growth exists but is less dramatic than +2768%.

3. **"Proof path via attractor"**: Circular — the attractor structure
   assumes convergence, which is what we're trying to prove.

## Lessons

- Always validate exciting discoveries against trivial explanations
- "Orbits pass through 5" is trivially true IF convergence holds
- The REAL structural result is the carry automaton spectral gap (1/2)
  and the density bound (spacing ~2^t), not the attractor structure
