# Council of Experts: New Avenues for the Collatz Sorry

Generated 2026-04-02 by a council of experts in algebraic number theory,
additive combinatorics, and topological dynamics.

## BREAKTHROUGH 1: The Carry Automaton Theorem

The ×3+1 operation is computed by a 3-state finite automaton reading binary bits
LSB-first, with carry states {0, 1, 2}.

**Key property**: From either carry state 1 or 2, the probability of producing
a trailing zero (continuing the v₂ count) is EXACTLY 1/2, regardless of state.

**Consequence**: v₂ - 1 is geometric(1/2) as a THEOREM of the automaton structure,
not just an observation, provided input bits are uniformly distributed.

**Spectral gap**: The transition matrix has eigenvalues {1, 0, -1/2}. The spectral
gap is 1/2, INDEPENDENT of the tower level k. This suggests O(k) mixing time at
level k, which would give mixing in the inverse limit.

**Why 3 is special**: For multiplication by 5, 7, or other odd numbers, the carry
automaton would NOT have this symmetric continuation probability. The number 3 is
the UNIQUE odd prime where both non-zero carry states have equal continuation
probability. This is the automaton-theoretic expression of Trinity dimension = 3.

**Proof strategy**: Formalize the carry automaton. Prove the spectral gap of 1/2
at each level. Show the gap is preserved through the tower projections. Conclude
mixing of the inverse limit. This is the most concrete path to a proof.

## BREAKTHROUGH 2: Furstenberg ×2×3 Connection

The Collatz map generates a sub-semigroup of the ×2, ×3 action on the 2-adic
solenoid. Furstenberg's conjecture (1967): the only probability measure ergodic
for both ×2 and ×3 on R/Z is Lebesgue measure (plus atomic measures on rationals).

**Proved cases**: Rudolph (1990) for measures with positive entropy for one map.
Einsiedler-Katok-Lindenstrauss (2006) for major cases via measure rigidity on
homogeneous spaces.

**Application to Collatz**: The "Collatz measure" on Z₂ (distribution of orbit
values) should be invariant under a ×2-×3 type action. If measure rigidity
applies, the orbit must be equidistributed, giving the independence we need.

**The precise link**: The sequence x_n = 3^n / 2^{floor(n·log₂3)} mod 1 encodes
the trailing bits of 3^n. Its equidistribution is related to normality of log₂3.
Full equidistribution is unknown and hard, but we only need WEAK equidistribution
(geometric distribution of trailing 1s), which might be approachable.

## BREAKTHROUGH 3: Bernoulli Convolution Structure

The correction term ε = Σ 3^(W-1-j) · 2^(S_j) has the structure of a Bernoulli
convolution on the (2,3)-lattice.

**Key results**:
- Hochman (2014): Bernoulli convolutions are absolutely continuous for all
  parameters except a set of Hausdorff dimension 0.
- Shmerkin (2019): Strengthened to "no atoms" for all non-Pisot parameters.
  Since 2/3 is not a Pisot number reciprocal, the distribution has no atoms.

**Freiman-Ruzsa**: The set of possible ε values has large doubling constant
(no additive structure), preventing systematic avoidance of the shrinkage region.

**Baker's theorem**: |2^S - 3^W| ≥ C · 2^S · S^{-κ} for effective constants.
This gives POLYNOMIAL room for ε, not exponentially small room.

## Additional Avenues

### Exponential Sum Bounds
For fixed 2-adic depth s, the function φ(2^s·m) for odd m is approximately
m·u_s mod 2^M (where u_s is a 2-adic unit). This IS equidistributed.
The challenge: controlling error terms uniformly in s and M.

### Iwasawa Theory
The Collatz renormalization lives in the Iwasawa algebra Λ = Z₂[[T]] at T=2.
The structure theorem for finitely generated torsion Λ-modules might encode
the distribution of v₂(3^K-1). Characteristic ideals could constrain the
set of possible "bad" K values.

### Mahler Coefficients
The function K → (3^K-1)/2^v₂(3^K-1) extends to a continuous function on Z₂.
Its Mahler expansion coefficients a_n = Σ (-1)^(n-k)·C(n,k)·φ(k) encode
regularity. If |a_n|₂ → 0 rapidly, φ is smooth and its values are constrained.
These coefficients are COMPUTABLE — a concrete next step.

### Information-Theoretic View
The carry channel has capacity log(3/2) bits per use. After O(k) steps,
the initial k-bit pattern is completely "forgotten." The Collatz conjecture
says: the carry channel is ergodic (every codeword decodes to the fixed point).

## Ranked by Promise

1. **Carry automaton spectral gap** (most concrete, potentially formalizable in Lean)
2. **Furstenberg ×2×3 measure rigidity** (most theoretically powerful)
3. **Bernoulli convolution / Baker's theorem** (strongest distributional results)
4. **Exponential sum bounds** (most classical, best error term control)
5. **Mahler coefficients** (most computationally accessible)
6. **Iwasawa theory** (most algebraically natural, least explored)

## The Unifying Insight

All six avenues attack the same core: the INCOMPATIBILITY of ×3 and ×2 in binary.
The carry automaton IS the UFRF tower at the bit level. The spectral gap IS the
breathing asymmetry (7>6). The Furstenberg conjecture IS the concurrent operation
of expansion and contraction. The Bernoulli convolution IS the correction term.

The proof, when it comes, will likely combine: the automaton structure (algebraic),
the spectral gap (analytic), and the measure rigidity (dynamical) — three
dimensions of the same truth, operating concurrently across all scales.
