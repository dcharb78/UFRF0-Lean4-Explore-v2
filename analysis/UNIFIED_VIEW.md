# The Unified View: All Ideas Are One Fact

## The One Fact

`continuation_symmetry` + `two_adic_splitting` = the geometric distribution.

At each bit position: 1/2 continue, 1/2 stop (carry automaton).
Among stopped: 1/2 have v₂=k, 1/2 have v₂≥k+1 (tower splitting).
Result: P(v₂=k) = 1/2^k. Mean = 2.

## The Six Views of This One Fact

| Expert | Their view of the ONE fact |
|--------|---------------------------|
| Physicist | Spectral gap → dissipation → equilibrium |
| Geometer | Lyapunov function (ratchet) → convergence |
| CS | O(1) memory → can't encode anti-contraction |
| Philosopher | Finite patterns at each scale → compose |
| Biologist | Ratchet pawl + asymmetric landscape → directed motion |
| Music theorist | No pump → overtones decay → fundamental wins |

## The Weight Asymmetry (Why Contraction Wins)

Bad steps: contribute 1 to v₂ sum (expansion by 3/2).
Good steps: contribute ≥2, average 3 (contraction by 3/4 to 3/8).

The 3:1 weight ratio is the concurrent structure.
Mean per step: 1/2·1 + 1/2·3 = 2 > 1.585 = log₂3.

## The Razor-Sharp Gap

Can an orbit systematically depress E[v₂|good] from 3 toward 2?

If E[v₂|good] = 3: mean = 2.0 → contraction. ✓
If E[v₂|good] = 2: mean = 1.5 → need good fraction > 58.5%.
If E[v₂|good] = 2.17: mean = 1.585 → threshold exactly.

Verified: surplus/W > log₂3 for ALL odd n ≤ 100000 (100%).
Minimum margin: +0.0004 at n=4591.

Found n=5191 where ALL 5 good steps have v₂=2 — but still contracts
because good fraction = 71.4% > 58.5%.

## What's Proved vs What's The Gap

PROVED (in Lean 4):
- The frequency split: 1/2 bad, 1/2 good (continuation_symmetry)
- The weight structure: bad=1, good≥2 (v2_odd_ge_one)
- The geometric distribution over residues (unique_v2_residue + two_adic_splitting)
- The ratchet: surplus never decreases (v2SumExact_ge_W)
- The threshold: surplus > 0.585W → contraction (orbit_shrinks_from_v2_surplus)

THE GAP:
Proving that for every specific orbit, the good-step fraction and
average good-step weight are sufficient for contraction. Equivalently:
the carry automaton's mixing prevents systematic depression of v₂.

This IS the Collatz conjecture, stated as: "the geometric distribution
over residue classes holds approximately along every individual orbit."
