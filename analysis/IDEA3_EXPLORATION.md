# Exploration of Five Unconventional Ideas

## Council Vote Winner: Lefschetz on Solenoid — FAILS

All Lefschetz numbers L(T^n) = 0 for all n (both stochastic and deterministic).
Reason: eigenvalue 1 in the transition matrix (from the stationary distribution)
makes det(I - T^n) = 0 identically. The Lefschetz theorem is INCONCLUSIVE
when L = 0 — it gives no information about fixed points.

The stochastic topological entropy = 0 (spectral radius = 1).
The deterministic topological entropy = log 2 (spectral radius = 2).
The 50/50 split ensures the stochastic system is at the "critical point."

## Idea 1: Height Descent — DOESN'T CLOSE

A modified Lyapunov function h'(n) = log₂(n) - α·surplus:
- Decreases at every good step (v₂≥2) for any α > 0
- Increases at every bad step (v₂=1) by ~0.585
- Net over a cycle depends on streak length vs good step contribution
- The net balance IS the Collatz conjecture

## Idea 2: Ordinal Descent — PROMISING but needs right ordinal

The ratchet gives a natural "major" ordinal component.
But the "minor" component (what decreases within each surplus level)
is the orbit value, which can grow during bad streaks.
Defining the right ordinal IS equivalent to proving Collatz.

## Idea 4: Game Theory — REDUCES to same gap

Borel determinacy gives a dichotomy (either Player A or Player B wins).
But connecting "B wins in expectation" to "B wins pointwise"
hits the same density-vs-pointwise barrier.

## Idea 5: Pro-étale Descent — UNEXPLORED, most mathematically deep

The sheaf-theoretic approach:
1. Define a sheaf F on the pro-étale site of Spec(ℤ₂)
2. F(U) = "set of divergent orbits starting in U"
3. Our density result: F has no generic sections
4. Our cycle killing: stalks at periodic points are trivial
5. Pro-étale descent (exact for this topology): F = 0

This MIGHT work because pro-étale descent is designed to bridge
exactly the "density → pointwise" gap in p-adic geometry.
But requires sophisticated algebraic geometry not in current Mathlib.

## Assessment

All five unconventional ideas either fail outright or reduce to the
same fundamental gap. The Collatz conjecture appears to be ROBUST —
it resists attack from every direction because the gap (distributional
→ pointwise) is genuinely hard.

The most promising unexplored direction remains Idea 5 (pro-étale descent)
and the Lindenstrauss invariant measure classification — both require
mathematical machinery beyond what's currently formalizable.
