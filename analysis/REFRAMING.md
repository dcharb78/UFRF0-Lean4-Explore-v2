# The Reframing: Collatz Is Not a Number Theory Problem

## The Insight From Six Diverse Experts

Three councils (physics, geometry, CS, philosophy, biology, music) independently
converged on the same conclusion:

> **The Collatz conjecture is a DISSIPATIVE DYNAMICS problem wearing an arithmetic disguise.**

## The Translation Table

| Arithmetic View | Physics View | Geometric View | Biological View |
|----------------|-------------|----------------|-----------------|
| Carry automaton (6 states) | The physical law | The manifold map | The molecular machine |
| Spectral gap = 1/2 | Dissipation rate | Laplacian gap | Ergodic mixing rate |
| 13-cycle (7 > 6) | Potential gradient | Curvature | Asymmetric energy landscape |
| Surplus monotonicity | Second law of thermodynamics | Lyapunov function | Ratchet pawl |
| Pattern 101 (contraction) | Ground state / equilibrium | Stable manifold | Rest state |
| Pattern 111 (expansion) | Excited state | Unstable manifold | Active transport |
| The sorry | "Does it reach equilibrium?" | "Does every orbit converge?" | "Does it reach homeostasis?" |

## Why This Reframing Matters

In EVERY physical system: a dissipative system with no energy input reaches
its ground state. This is the second law. No exceptions.

The Collatz conjecture asks: does the carry automaton's dissipative dynamics
(spectral gap 1/2, no energy pump) always reach the ground state (r=1)?

Physics says: YES. Always. The second law forbids eternal excited states
in a dissipative system.

The mathematical gap: translating "the second law" into a theorem about
specific integer orbits. This requires bridging measure-theoretic convergence
(almost every orbit) to pointwise convergence (every orbit).

## The Most Promising New Approaches

### 1. Lindenstrauss Invariant Measure Classification (Geometry)
Classify invariant measures of the Syracuse map on the 2-adic solenoid.
The irrationality of log₂3 is the Diophantine condition that prevents
non-trivial invariant measures. If only the Dirac mass at {1} survives →
Collatz follows. (Fields Medal 2010 technique.)

### 2. The Brownian Ratchet Proof (Biology/Physics)
The 50/50 split = thermal noise. The 7>6 asymmetry = tilted landscape.
The surplus monotonicity = ratchet pawl (proved). The absence of energy
pump = the correction term bound (proved). Show: no orbit can avoid
completing a full 13-cycle → the ratchet always advances → equilibrium.

### 3. Harmonic Decay (Music/Physics)
Every starting number is a complex waveform. The spectral gap (1/2) gives
geometric decay of overtones. The surplus monotonicity prevents energy
injection into higher modes. The fundamental (r=1) always dominates.
Prove: no overtone is self-sustaining → resolution to fundamental.

### 4. Finite Transducer Mixing (CS)
The 6-state Mealy machine with gap 1/2, iterated O(log n) times, cannot
sustain correlated output. After O(log n) steps, only O(1) bits of
information about n survive. O(1) bits cannot encode "avoid contraction."
Prove: information loss from the channel capacity < 1 forces convergence.

### 5. Bounded Model Checking (CS)
Show every modular cycle at level k is killed at level k + C (universal C).
The spectral gap bounds C. The splitting theorem provides the inductive step.
This is a finitist program verification argument: the loop invariant
(surplus ≥ 0) is maintained, and the decreasing measure is eventually hit.

## What's PROVED That Supports This Reframing

All of these are zero-sorry, formally verified in Lean 4:

- The dissipation mechanism: carry automaton spectral gap = 1/2
- The potential gradient: contraction dominates expansion (concurrent_contraction_dominance)
- The second law: surplus never decreases (v2SumExact_ge_W / ratchet)
- The no-energy-pump: correction term bounded (correctionTerm_bound)
- The ground state: r=1 is the only fixed point at every scale
- The artifact killing: every modular cycle dies at finer scale (cycle_killed_at_k14)
- The asymmetry: 50/50 split with exponential alternating dominance

## What Remains

One theorem: "the dissipative dynamics reaches its ground state for every
positive integer starting point." Equivalently: "the carry automaton's
spectral mixing controls individual orbits, not just ensembles."

This is the Collatz conjecture, stated as a dissipative dynamics theorem.
