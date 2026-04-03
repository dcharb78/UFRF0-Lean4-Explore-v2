# Next Steps: Closing the Collatz Gap

## The Precise Gap

The Collatz conjecture reduces to ONE claim:

> **The trailing 1s of (3^K − 1)/2^v₂(3^K−1) are bounded by O(log K).**

Equivalently: after the first Mersenne countdown (K-1 steps), subsequent
countdowns are short — bounded by the trailing-1 count of the recovery value.

## What's Proved

1. **The Countdown**: f^j(2^K-1) = 3^j·2^(K-j)-1 with K-j trailing 1s (algebraic)
2. **The Recovery**: v₂ ≥ 2 always after countdown (trailing_ones=1 → n≡1 mod 4)
3. **The Ratchet**: v₂ surplus never decreases (v2SumExact_ge_W)
4. **The Threshold**: surplus > 0.585W → contraction (orbit_shrinks_from_v2_surplus)
5. **Sparsity**: K values giving ≥t trailing 1s spaced ~2^t apart (mult order)
6. **Carry Automaton**: spectral gap 1/2, geometric v₂, scale-invariant 1/2 mixing
7. **Correction Bound**: ε·2^W ≤ (3^W-2^W)·2^S (tight, proved via zify)

## Potential Attack Vectors

### A. Baker's Theorem on Linear Forms in Logarithms
Baker (1966): |b₁·log α₁ + b₂·log α₂| > exp(-C·log(max|bᵢ|))
Applied: |K·log 3 - S·log 2| ≥ effective lower bound.
This constrains how close 3^K can be to 2^S, which constrains trailing 1s.
**Concreteness: HIGH. Existing Mathlib support: PARTIAL.**

### B. Multiplicative Order + Counting
ord_{2^M}(3) = 2^(M-2). K values with trailing_ones ≥ t form a coset
mod 2^t. An orbit of length W visits ≤ W/2^t such values.
For t > log₂W: at most 1. Gives max subsequent streak ≤ log₂W ≈ log₂log₂n.
**Concreteness: HIGH. Almost a proof — needs orbit equidistribution.**

### C. Thermodynamic Formalism (Fractal)
Pressure P_B(0) = log(3/4) < 0 → dim_H(bad set) = 0 in ℤ₂.
Combined with arithmetic: irrationality of log₂3 prevents ℕ from hitting B.
**Concreteness: MEDIUM. Theoretical depth: DEEP.**

### D. Convolutional Code / Information Theory
The carry automaton as a convolutional encoder with catastrophic error
propagation. Channel capacity log₂(3/2) < 1 → information loss per step.
Directed information bound: W·log₂(3/2) bits survive after W steps.
**Concreteness: MEDIUM. Novel angle.**

### E. Direct Algebraic Attack on Trailing 1s
Prove: trailing_ones((3^K-1)/2^v₂(3^K-1)) ≤ C·log₂K for all K.
Via: 3^K-1 = (3-1)·Σ 3^j = 2·Σ 3^j. Factor structure of Σ 3^j mod 2^M.
LTE gives v₂(3^K-1) exactly. The remaining odd part's trailing bits
depend on 3^K mod 2^(v₂+t+1).
**Concreteness: HIGH. Most direct path.**

### F. Automaton Group / Decidability
The carry automaton is an invertible Mealy machine. Its group structure
might make the orbit problem decidable for this specific system.
**Concreteness: LOW. Theoretical interest: HIGH.**

## Recommended Priority

1. **E (Direct Algebraic)** — most concrete, closest to closing
2. **A (Baker's Theorem)** — gives explicit bounds, formalizable
3. **B (Multiplicative Order)** — almost proved, needs one more step
4. **C (Thermodynamic)** — deepest structural result
5. **D (Info Theory)** — novel, might yield new bounds
6. **F (Automaton Group)** — long-term research direction
