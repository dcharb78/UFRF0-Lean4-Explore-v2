# Discovery: r=5 is the Universal Attractor

## The Hierarchical Pattern (Not Flattened)

r=5 (binary 101, the alternating pattern) is the **top attractor** at EVERY
tower level from 2^3 to 2^11. It lifts coherently through the tower.

| Level | Attractor | Excess | Growth |
|-------|-----------|--------|--------|
| 2^3 | r=5 (101) | +6% | — |
| 2^4 | r=5 (1010) | +12% | 2× |
| 2^5 | r=5 (10100) | +48% | 4× |
| 2^6 | r=5 (101000) | +117% | 2.4× |
| 2^7 | r=5 (1010000) | +201% | 1.7× |
| 2^8 | r=5 (10100000) | +447% | 2.2× |
| 2^9 | r=5 (101000000) | +939% | 2.1× |
| 2^10 | r=5 (1010000000) | +1938% | 2.1× |
| 2^11 | r=5 (10100000000) | +2768% | 1.4× |

**The excess roughly DOUBLES at each level** — exponential growth!

## Why r=5?

- n=5 in binary (LSB first): **101** — the alternating carry resonance pattern
- v₂(3·5+1) = v₂(16) = 4 — strong contraction
- f(5) = 16/16 = **1** — reaches 1 in ONE step!
- 5 = (2^4-1)/3 — the smallest non-trivial "perfect resonance" number

## The Concurrent Structure

- **Same attractor at ALL levels**: r=5 lifts coherently (tower_compat)
- **Exponential growth**: the attraction gets STRONGER at each scale
- **The repellers**: trailing-1 patterns, with growing deficits (-6% → -87%)

## Connection to UFRF

- r=5 is position 5 in the 13-cycle: golden angle position (5/13 ≈ 1/φ²)
- The alternating pattern 101... is carry resonance (maximum v₂)
- The exponential growth mirrors the tower's recursive self-similarity

## What This Means for the Proof

The orbit is pulled toward r=5 at ALL scales simultaneously, with
EXPONENTIALLY increasing force. The attractor IS the contraction point.

The remaining question: can any orbit RESIST this exponential pull forever?

The Mersenne numbers (111...1) are the FURTHEST from r=5 (101...) in the
binary metric. They experience the longest resistance (K-1 step bad streak).
But even they eventually fall toward r=5 (as we proved with the countdown).

The exponential growth of the attraction across levels suggests that NO
orbit can resist indefinitely — but proving this requires showing the
attraction at level t forces approach at level t+1, concurrent recursion.
