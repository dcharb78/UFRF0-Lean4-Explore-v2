# Collatz Exploration Findings — collatz-explore branch

Three questions. All answered. Two negative, one mixed. Each answer clarifies the structure.

---

## Question 1: Does the 3-adic Factor Fix the v₂ Discrepancy?

**Answer: NO.**

### Data

| M    | k | j | #unsafe | max_disc | W   | margin |
|------|---|---|---------|----------|-----|--------|
| 104  | 3 | 0 | 13      | 5        | 10  | 150    |
| 312  | 3 | 1 | 39      | **5**    | N/A | N/A    |
| 936  | 3 | 2 | 117     | **7**    | N/A | N/A    |
| 208  | 4 | 0 | 13      | 4        | 22  | 130    |
| 624  | 4 | 1 | 39      | **6**    | N/A | N/A    |
| 416  | 5 | 0 | 13      | 5        | 26  | 790    |
| 1248 | 5 | 1 | 39      | 5        | 43  | 845    |

### Why it fails

The discrepancy formula is:
```
For n = r + 13·2^k·m:  3n+1 = 2^k · (2^(v-k)·q + 39m)
```
where 3r+1 = 2^v·q (q odd) and 39 = 3 × 13.

Adding 3-adic depth to the modulus triples the residue count (13 → 39) but cannot resolve
the parity of the inner term `2^(v-k)·q + 39m`, because 39 is ODD when m is odd regardless
of the 3-adic structure. The 3 in 39 = 3×13 means: adding more 3-adic information doesn't
change which values of m cause the parity flip.

### Critical side-effect: spurious modular cycles

At M=312 (k=3, j=1), the transition graph has **2 cycles** instead of 1:
- Fixed point: r=1, v₂/step = 2.0 (contractive)
- **14-cycle**: [47, 71, 107, 161, 121, 91, 137, 103, 155, 233, 175, 263, 83, 125]
  - v₂ values per step: [1,1,1,2,2,1,2,1,1,2,1,1,1,3] — sum = 20
  - v₂/step = 20/14 ≈ **1.4286 < log₂(3) ≈ 1.585**
  - This cycle is a **modular artifact** — n=47 reaches 1 in the actual integers

The 14-cycle's v₂/step is BELOW the convergence threshold. This is why the window DP
returns N/A for most mixed moduli — the certificate can never fire because residues on the
14-cycle path never accumulate enough v₂. At k=5, j=1 (M=1248), this artifact is absent
and W=43 with improved margin 845 > 790. The exception doesn't save the approach.

### Conclusion

The 3-adic factor is a dead end. The discrepancy is intrinsically 2-adic (caused by carries
in 3n+1 that depend on bits above position k). Multiplying the modulus by powers of 3
makes the modular dynamics worse (more unsafe residues, spurious cycles).

---

## Question 2: What Does the Inverse Collatz Tree Look Like?

**Answer: Dense, nearly uniform mod 13, high-discrepancy residues appear EARLY (not late).**

### Finding 1: Density does approach 1

Forward Collatz stopping times (odd-step depth to reach 1) for all odd n ≤ 10,000:

| Depth ≤ | Coverage ≤ 1000 | Coverage ≤ 10000 |
|--------:|----------------:|-----------------:|
| 10      | 32.0%           | 13.0%            |
| 20      | 58.8%           | 39.0%            |
| 50      | 96.2%           | 83.0%            |
| 96      | **100%**        | **100%**         |

Every odd integer ≤ 10,000 reaches 1. Max odd-step depth observed: 96. No counterexamples.

The inverse tree is extremely sparse as a tree (branching factor ≈ 20, so depth-30 BFS
would need ~10^39 nodes), but the density result holds: every tested integer IS in the tree.

### Finding 2: Mod-13 distribution is nearly uniform

At depth ≥ 4 in the full BFS (5M nodes, depth ≤ 8), the distribution mod 13 is nearly
uniform, with a weak persistent elevation of r=4. The chi-squared test at depth 6 shows
max/min count ratio ~1.01 — essentially flat.

The UFRF breathing cycle is NOT strongly visible in absolute node counts. The tree expands
without a clear 13-fold contraction pattern. This is consistent with the mod-13 graph having
a single connected component with 2 as a primitive root — the tree "visits" all residues
quickly and then becomes uniform.

### Finding 3: High-discrepancy unsafe residues appear EARLIER, not later

First depth at which each unsafe residue mod 104 appears in the inverse tree (BFS, depth ≤ 8):

| Residue | First depth | Discrepancy | Category |
|--------:|------------:|------------:|:---------|
| 85      | 1           | 5           | HIGH     |
| 21      | 1           | 3           | HIGH     |
| 53      | 1           | 2           | HIGH     |
| 13      | 1           | 0           | LOW      |
| 29      | 1           | 0           | LOW      |
| 45      | 2           | 0           | LOW      |
| 61      | 2           | 0           | LOW      |
| 77      | 2           | 0           | LOW      |
| 93      | 2           | 0           | LOW      |

Average first depth: HIGH-DISC = 1.00, LOW-DISC = 1.67.

**The hypothesis that high-discrepancy residues are "hard to reach" is refuted.** They appear
earlier in the inverse tree, meaning they have MORE predecessors, not fewer. The discrepancy
in the FORWARD direction (v₂ overcounting) does not translate to a bottleneck in the BACKWARD
direction (tree reachability).

Forward stopping times do show a marginal difference: HIGH-DISC averages 26.56 odd steps to
reach 1, LOW-DISC averages 25.61 — a difference of ~1 step, not statistically decisive.

### Finding 4: Tower compatibility for the inverse map has 7 exceptions

At depth ≤ 8, the mod-208 inverse tree has 7 residues whose reduction mod 104 is missing or
later in the mod-104 tree. This means the INVERSE map does not satisfy tower compatibility
as cleanly as the forward map. The forward map has tower compatibility proven (theorem
`tower_compat_k3_k4` in CollatzSolenoid.lean); the inverse map does not.

### Finding 5: Multiples of 3 are the true leaves

n ≡ 0 (mod 3) have NO odd predecessors (since 3 ∤ (n·2^j − 1) for any j). They enter the
inverse tree only via even predecessors (2n, 4n, ...). In any Collatz orbit, multiples of 3
are always preceded by an even number — they are never the output of an odd step.

This 3-adic divisibility constraint is the cleanest structural fact about the inverse tree.
It is closely related to the failed Q1 attempt: the coefficient 3 creates a divisibility
barrier that neither the forward modular analysis (Q1) nor the coset structure (Q3) can escape.

---

## Question 3: Do Unsafe Residues Cluster in Cosets?

**Answer: At k=3,4 yes (Coset D), but the pattern rotates. No persistent algebraic culprit.**

### Data

| k | M    | Worst coset | A   | B   | C   | D   | 0   |
|---|------|-------------|-----|-----|-----|-----|-----|
| 3 | 104  | **D** (5)   | 2   | 1   | 1   | 5   | 0   |
| 4 | 208  | **D** (4)   | 1   | 2   | 1   | 4   | 1   |
| 5 | 416  | **A** (5)   | 5   | 2   | 1   | 3   | 0   |
| 6 | 832  | **A** (4)   | 4   | 1   | 2   | 2   | 0   |
| 7 | 1664 | **0** (5)   | 3   | 0   | 1   | 2   | 5   |

Cosets: A={1,3,9}, B={2,6,5}, C={4,12,10}, D={8,11,7}, 0={multiples of 13}

### Why the rotation happens

The worst offender at each k is the residue r where v₂(3r+1) is largest (a high power of 2).
As k increases, which residue in ZMod(13·2^k) achieves the largest v₂ depends on which
"near-power-of-2" falls where. The rotation D→D→A→A→0 reflects which coset contains
2^(largest power below 13·2^k) — this shifts systematically as k grows.

There is no single algebraic culprit. The obstruction is purely 2-adic.

---

## Summary: What These Three Questions Settled

| Question | Signal | Key Finding |
|----------|--------|-------------|
| Q1: 3-adic factor | NEGATIVE | Discrepancy unchanged; introduces spurious cycles |
| Q2: Inverse tree | MIXED | Density → 1 confirmed; high-disc residues appear early, not late |
| Q3: Coset clustering | NEGATIVE | Worst coset rotates; no algebraic culprit |

### What Q2 gives us that Q1 and Q3 don't

The inverse tree result is the most structurally interesting. The key facts:
1. Every odd n ≤ 10,000 is in the tree (depth ≤ 96)
2. High-discrepancy residues appear EARLY in the inverse tree
3. Multiples of 3 are the true leaves (3-divisibility barrier)

Combined with the Phase 4 result (CollatzNoCycles.lean: 3^L ≠ 2^S, gcd(2,3)=1),
this suggests the correct framing for the next phase: the 3-divisibility barrier for
the inverse tree is the SAME algebraic fact as the power-coprimality theorem.
The tree's structure is governed by gcd(2,3)=1 at every level.

---

---

## Question 4: Harmonic Structure, Cover Time, and Inverse Tree Synthesis

**Answer: Cover time is near-random, not a convergence bound. Mod-3 classes are
indistinguishable in forward length. The 3-divisibility barrier is exactly 1 step thin.**

### Part A: Cover Time on Forward Trajectory

For all odd n in [3, 9999], recording the number of odd Syracuse steps until all
12 nonzero residues mod 13 have been visited:

| Metric | Value |
|--------|-------|
| Max cover_time | 78 |
| Mean cover_time | 33.68 |
| Theoretical random-walk cover (12·H₁₂) | 37.24 |
| Fraction achieving full cover | 40.2% |
| Mean steps after cover (to reach 1) | 16.05 |

**The Collatz cover time (33.68) is BELOW the random-walk theory (37.24).** Trajectories
explore mod-13 residues slightly faster than a random walk on a 12-element group, consistent
with the known primitive-root structure (2 is a primitive root mod 13).

Only 40.2% of trajectories achieve full cover — most reach 1 before visiting all 12 classes.
Cover time is bounded (max 78), but is NOT a useful upper bound on forward_length: the ratio
forward_length / cover_time has max 4.29 and mean 1.50, making it only a 23%-tight lower bound.

### Part B: Comma Accumulation Curves

The "comma" at step t: `comma(t) = t·1585 − cumulative_v₂·1000` (integer millibits).
This measures the running excess of expansion over contraction (positive = net expansion so far).

| Metric | Value |
|--------|-------|
| Mean max_comma | 868 mb |
| Max max_comma | 9870 mb (n=9663) |
| Min max_comma | −10830 mb |
| log(n) vs max_comma Pearson r | −0.069 |
| Fraction starting with comma > 0 | 50.0% |

**The comma is essentially uncorrelated with log(n)** (r = −0.069). This means the
Pythagorean comma is not a useful predictor of convergence speed for a given n. The comma
accumulation is driven by the specific v₂ sequence, not the magnitude of n.

The n=341 case is notable: max_comma = −6830 mb (negative from step 1). This means (3·341+1)
= 1024 = 2^10 — a large power of 2 that immediately contracts far below the expansion rate.

### Part C: Depth vs Forward Trajectory Length

Using forward stopping times for all odd n ≤ 9,999:

| Metric | Value |
|--------|-------|
| Mean forward_length | 30.67 |
| Max forward_length | 96 |
| log(n) vs forward_length Pearson r | 0.198 |

Comparing HIGH-DISC residues mod 104 {85, 21, 53} vs LOW-DISC {13, 29, 45, 61, 77, 93}:

| Class | Mean forward_length |
|-------|---------------------|
| HIGH-DISC | 26.56 |
| LOW-DISC | 25.61 |

**Difference is only ~1 step** — confirming Q2's finding that high-discrepancy residues
do not cause harder trajectories. Per-n inverse tree depths are not directly available
from q2_results.json (aggregate only), but the aggregate BFS result (depth ≤ 96 suffices)
matches the forward stopping time maximum exactly.

### Part D: The 3-Divisibility Barrier

Forward stopping times by mod-3 class, all odd n in [3, 9999]:

| Class | Count | Mean fwd_length | Std |
|-------|-------|-----------------|-----|
| 0 (mult of 3) | 1667 | 30.39 | 18.17 |
| 1 | 1666 | 30.79 | 18.21 |
| 2 (Trinity +1/2) | 1666 | 30.85 | 18.00 |

**No class converges faster than any other** — all three mod-3 classes have essentially
identical forward lengths (within 0.5 steps). The Trinity mapping {-1/2, 0, +1/2} → {2, 0, 1}
mod 3 does NOT predict convergence speed.

The barrier thickness for class 0: **exactly 1 step** (confirmed for all 1667 odd multiples
of 3 up to 9999). Since 3n+1 ≡ 1 (mod 3), the very first forward step always escapes the
barrier. The barrier is real but thin — multiples of 3 cannot be reached by odd predecessors
(Lean-proven), but they escape in one step.

### Lean Theorem: multiples_of_3_are_leaves (PROVEN)

The 3-divisibility barrier theorem was formalized and verified in
`UFRF/CollatzNoCycles.lean` (Section 4, line 158):

```lean
theorem multiples_of_3_are_leaves (n m v : ℕ) (h3 : 3 ∣ n) :
    3 * m + 1 ≠ n * 2 ^ v := by
  intro heq
  have hdvd : 3 ∣ n * 2 ^ v := h3.mul_right _
  rw [← heq] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  omega
```

Build result: `✔ [3273/3273] Built UFRF.CollatzNoCycles (5.3s)` on branch `collatz-explore`.

### Synthesis

The synthesis hypothesis was: if cover_time bounds forward_length, and inverse tree depth
bounds cover_time, then convergence follows by group theory alone.

**Result: The hypothesis is FALSE.** Cover time is not a tight bound (max ratio 4.29).
The correct framing is:

1. Forward length is empirically bounded (max 96 for n ≤ 10,000) but with no tight
   cover_time relationship.
2. The near-random residue distribution (r = −0.069 for log(n) vs max_comma) means
   convergence is driven by v₂ accumulation, not by visiting residues.
3. The mod-3 class structure (Trinity) does not predict convergence — all classes converge
   identically.
4. The cleanest structural theorem remains: **multiples of 3 are leaves** in the inverse
   tree — a divisibility barrier that is both Lean-proven and computationally confirmed
   (barrier thickness = 1, algebraically guaranteed).

---

---

## Question 4A: Multi-Scale Bad Streak Analysis

**Answer: NO. Coarse-scale phase is uniformly distributed for long-streak numbers.
The multi-scale concurrent compensation hypothesis is refuted.**

### Background

The k=3 modular bound says max bad streak = 4 in ZMod(104). But n=77671 has a
streak of 16 in actual integers. This is NOT a contradiction — n=77671 has 17 bits,
so it lives at native resolution k≈17, where the bound is k+1=18. Streak 16 < 18:
consistent.

The hypothesis: when a number has a long bad streak at fine scale, it should be in
CONTRACTION at coarser scales (mod 169, mod 2197) — the scales "compensate".

### Step 1: Top Streaks (odd n ≤ 100,000)

| n | streak | bits |
|---|--------|------|
| 77671 | 16 | 17 |
| 65535 | 15 | 16 |
| 32767 | 14 | 15 |
| 43689 | 14 | 16 |
| 69039 | 14 | 17 |

Pattern: the longest-streak numbers are predominantly near powers of 2 (2^k − 1).
This is structurally expected: if n ≈ 2^k, then 3n+1 ≈ 3·2^k, which has v₂ = 1.

### Step 2: Multi-scale positions for top-streak numbers

n=77671: phase_13=contraction, phase_169=contraction, phase_2197=**expansion**.
n=65535: phase_13=expansion, phase_169=contraction, phase_2197=contraction.
n=32767: contraction at ALL three scales.

No consistent pattern: the top-streak numbers fall on both sides of each scale's
midpoint without systematic clustering.

### Step 3: Coarse-scale phase for streak ≥ 10 (516 numbers)

| Scale | % in contraction | Baseline |
|-------|-----------------|---------|
| Scale-2 (mod 169) | 48.1% | ~50% |
| Scale-3 (mod 2197) | 52.3% | ~50% |
| Both contraction | 26.6% | ~25% |

**Essentially 50/50.** Long-streak numbers are uniformly distributed across
contraction/expansion phases at coarser scales. No compensation effect.

### Step 4: n=77671 in detail

- mod 13: 9, mod 169: 100, mod 2197: 776 (mod 104: 87, mod 208: 87)
- Streak of 16 runs from step 4 to step 19
- After the streak: v₂ = 2, 2, 2 — mild recovery, not a large-v₂ payoff
- Total forward stopping time: 83 steps

The streak is structurally caused by n ≈ 2^17/√2 — n's binary structure, not its
multi-scale phase.

### Step 5: 2D histogram — streak length vs scale-2 phase

| Streak | %_contraction (mod 169) |
|--------|------------------------|
| 0–9 | 45–51% (≈ uniform) |
| 10–13 | 42–67% (small samples) |
| 14–16 | 100% (n=6, n=1) — sample too small |

The 100% contraction at streak≥14 is based on 6 numbers. Not statistically
significant.

### Step 6: Breathing Score

The breathing score `s₁/13 + s₂/169 + s₃/2197` (where sᵢ = n%13^i − half-range)
measures net multi-scale phase:

| Metric | Value |
|--------|-------|
| Min | −1.500 |
| Max | +1.417 |
| Mean | −0.045 |
| Stdev | 0.525 |
| r(score, forward_length) | 0.0076 |
| r(score, max_streak) | 0.0062 |

The breathing score is bounded by ±1.5 (=sum of ±0.5 across 3 scales), as expected.
But it is **essentially uncorrelated** with both forward trajectory length and bad
streak length. Bottom-25% vs top-25% breathing score: mean fwd_len 37.80 vs 38.05
— a difference of 0.25 steps, negligible.

### Synthesis

The concurrent-scale compensation hypothesis is **FALSE**:

1. Coarse-scale phase is uniformly distributed for long-streak numbers (≈50% at all thresholds).
2. The breathing score, despite being a bounded function on a compact domain, has
   r≈0.007 with forward length — no predictive power.
3. Long bad streaks are caused by n's binary structure (proximity to 2^k), not by
   multi-scale phase alignment.
4. The observed streak lengths satisfy streak < k+1 where k≈bit_length(n): the
   UFRF bound is correct, but it comes from the native resolution, not from
   coarse-scale compensation.

**The multi-scale concurrent structure does not create a compensation mechanism.**
The v₂ accumulation argument remains the only viable path, but the unsafe residue
gap still blocks it.

---

---

## Question 5: Self-Similar Tower Structure

**Primary finding: k=13 (meta_pos=0) has NO convergence window. The DP diverges at the meta-cycle completion. W(k) slope changes at k=7 (meta-flip). Base-13 digits have no predictive power.**

### Part A: W(k) Extended to k=15

Full table (integer millibit DP, max_window=500):

| k | modulus | max_streak | W(k) | W/k | meta_pos |
|---|---------|-----------|------|-----|----------|
| 3 | 104 | 4 | 10 | 3.33 | 3 |
| 4 | 208 | 5 | 22 | 5.50 | 4 |
| 5 | 416 | 6 | 26 | 5.20 | 5 |
| 6 | 832 | 7 | 42 | 7.00 | 6 |
| 7 | 1664 | 8 | 52 | 7.43 | 7 |
| 8 | 3328 | 9 | 54 | 6.75 | 8 |
| 9 | 6656 | 10 | 59 | 6.56 | 9 |
| 10 | 13312 | 11 | 78 | 7.80 | 10 |
| 11 | 26624 | 12 | 84 | 7.64 | 11 |
| 12 | 53248 | 13 | 80 | 6.67 | 12 |
| **13** | **106496** | **14** | **NONE** | **—** | **0** |
| 14 | 212992 | 15 | 90 | 6.43 | 1 |
| 15 | 425984 | 16 | 108 | 7.20 | 2 |

**k=13 (meta_pos=0) has no convergence window up to W=500.** The max_drift grows linearly (≈+3850 per 10 steps) with no sign of turning negative. k=14 and k=15 bounce back to normal convergence.

This is a structural discontinuity at the meta-cycle completion point. The ZMod(13 × 2^13) transition graph contains a path (or near-cycle) where the contraction certificates never fire. The meta-position 0 (the "source/return" phase of the 13-cycle) is where the DP breaks.

### W(k) slope change at k=7 (the meta-flip)

Linear fit: W(k) ≈ 7.66k − 7.62

| Phase | k range | W(k) slope |
|-------|---------|-----------|
| Before meta-flip | k=3..7 | 10.5 |
| After meta-flip | k=8..13 | 6.5 |
| Second meta-cycle | k=14+ | 18.0 (2 pts) |

The slope decreases by 4.0 at k=7 — the predicted meta-flip. Mean W/k before k=7: 5.26; after k=7: 7.06.

### Part B/C: Base-13 Digit Combinations

2×2 table (d₀ phase, d₁ phase) vs mean bad streak (odd n ≤ 100,000):

| (d₀,d₁) | mean_streak | max_streak | mean_fwd |
|---------|------------|------------|----------|
| (E,E) | 4.1475 | 13 | 37.95 |
| (E,C) | 4.1473 | 15 | 38.04 |
| (C,E) | 4.1446 | 14 | 38.06 |
| (C,C) | 4.1504 | 16 | 37.88 |

**Max delta: 0.0058** — completely flat. Base-13 digit combinations have zero predictive power for bad streaks or convergence speed. The recursive digit structure is NOT the signal.

### Part D: W(k) Sequence Meta-Analysis

W(k) sequence: [10, 22, 26, 42, 52, 54, 59, 78, 84, 80, -, 90, 108]

W(k) mod 13: [10, 9, 0, 3, 0, 2, 7, 0, 6, 2, -, 12, 4]

Three values of W(k) are ≡ 0 (mod 13): at k=5 (W=26), k=7 (W=52), k=10 (W=78). Spacing: 2, 3. No clean period-13 pattern.

### Part E: Fibonacci Primes in the Tower

| F_idx | p | p mod 13 | fwd_len | max_streak |
|-------|---|---------|--------|------------|
| 5 | 5 | 5 | 1 | 0 |
| 7 | 13 | **0** | 2 | 0 |
| 11 | 89 | 11 | 9 | 1 |
| 13 | 233 | **12** | 29 | 5 |
| 17 | 1597 | 11 | 43 | 5 |
| 23 | 28657 | 5 | 34 | 7 |
| 29 | 514229 | 1 | 32 | 2 |

F(13)=233 has high forward_length (29) and max_streak=5. Its index 13 is the same k where W(k)=None. F(7)=13 maps to p mod 13=0 (source/return) — same as meta_pos of k=13. The alignment is suggestive but the sample is too small for a statistical claim.

### Part F: Self-Similar Check

W(k) grouped by meta_pos (k mod 13): each meta_pos has at most one data point (we only computed k=3..15, covering each meta_pos once). No repetition yet to test period-13 in W(k). Only by extending to k=16..26 would the second meta-cycle be visible.

---

## Question 6: Log-Mod Recursive Structure

**Primary findings: Cumulative log correction is bounded ([-15, +12]). v₂ ≡ 1 (mod 3) dominance creates weak resonance between 2^S and 3^L. End states are uniformly distributed across all 36 (S mod 12, L mod 3) states — no preferred trajectory end.**

### Part A: (S mod 12, L mod 3) End States

For all odd n in [3, 999]: all 36 states are visited, approximately uniformly. No fixed end state. Most common state for any given n₀ mod 13: at most 10.5% — essentially 1/36 = 2.8% in expectation for random. Most are 7.9–10.5%, so slightly non-uniform but far from deterministic.

The convergence resonance condition 2^S ≡ n₀·3^L (mod 13) generates no clustering — the trajectories explore all (S mod 12, L mod 3) pairs.

### Part B: S(t) mod 13 Walk

| Metric | Value |
|--------|-------|
| Fraction reaching S≡0 (mod 13) | 81.8% |
| Mean steps to S≡0 | 10.72 |
| Max steps to S≡0 | 39 |
| Mean v₂ when S≡0 | 2.027 |
| Mean v₂ when S≢0 | 1.978 |

**v₂ is slightly higher (by 0.049) when S≡0 (mod 13)** — a weak resonance between the cumulative halving count and the next step's yield. When the halvings complete a full "breathing cycle" (S ≡ 0 mod 13), the trajectory tends to halve more. Signal is statistically present but small.

### Part C: 36-State Path Structure

All 36 states (S mod 12, L mod 3) are visited. Dominant transition: (0,0)→(1,1) at 51.4%, driven by v₂=1 dominance. End states approximately uniform — no "attractor" state in this 36-element space.

### Part D: Log Correction — **Cumulative Bound Found**

Log correction per step = actual v₂ − modular v₂(mod 104, k=3):

| Correction | Fraction |
|-----------|---------|
| 0 | 87.8% |
| ±1 | 7.7% |
| ≥±2 | 4.5% |
| Max positive | +12 |
| Max negative | −5 |

Mean correction: −0.0087 (slight systematic overcounting, as expected from unsafe residues).

**Cumulative correction over full trajectories: min=−15, max=+12.**
No trajectory (odd n ≤ 9999) has |cumulative_correction| > 20.

This is structurally significant: the modular certificates overshoot by at most 15 v₂-units total. However, 15 v₂-units = 15,000 millibits, while the certificate margin at k=3 is only 150 millibits. The cumulative correction is bounded but larger than the margin — **this does not close the gap at k=3**, but at higher k (where margins are larger), the constraint may be satisfiable.

### Part E: v₂ mod 3 Resonance

| v₂ mod 3 | Observed | Theoretical | Ratio |
|---------|---------|------------|------|
| 0 | 0.1357 | 0.1429 | 0.950 |
| 1 | 0.5954 | 0.5714 | 1.042 |
| 2 | 0.2689 | 0.2857 | 0.941 |

v₂ ≡ 1 (mod 3) is slightly overrepresented (5.4%). The theoretical prediction (1/7, 4/7, 2/7 from geometric distribution) holds to ~4% accuracy.

S mod 3 ↔ L mod 3 coupling: P(S≡L mod 3) = 0.342 vs expected 1/3 = 0.333. **Only 1.027× random — essentially no coupling.** The 2^S ↔ 3^L resonance hypothesis is NOT confirmed: S mod 3 tracks L mod 3 only marginally better than random.

**The v₂ ≡ 1 (mod 3) dominance is real (0.595 vs theory 0.571), but it doesn't create measurable resonance in (S mod 3, L mod 3). The coupling is too weak to exploit.**

---

## Dead Ends Closed

- ✗ Adding 3-adic precision to the modulus (Q1)
- ✗ Coset structure of (Z/13Z)* as the algebraic culprit (Q3)
- ✗ High-discrepancy residues as tree bottlenecks (Q2)
- ✗ Cover time as a convergence bound via group theory (Q4)
- ✗ Trinity mod-3 class as a convergence predictor (Q4)
- ✗ Pythagorean comma (log(n)) as a convergence predictor (Q4)
- ✗ Multi-scale coarse-scale compensation for fine-scale bad streaks (Q4A)
- ✗ Breathing score as a convergence or streak predictor (Q4A)
- ✗ Base-13 digit combinations (d₀,d₁) as streak predictors (Q5)
- ✗ Period-13 structure in W(k) sequence (Q5 — only one cycle computed)
- ✗ 2^S ↔ 3^L resonance via v₂ mod 3 (Q6 — coupling only 1.027×)

## Open Paths

1. **Uniform W(k)/2^k → 0 bound**: W(k) grows linearly in k while the modulus grows
   exponentially. A formal proof of this ratio going to 0 would close the gap via a
   solenoid compactness argument.

2. **Actual v₂ at unsafe residues**: Show that for any unsafe residue r at level k,
   the actual v₂ of (3n+1) for n ≡ r (mod 13·2^k) is at least k. This is equivalent
   to saying the true minimum v₂ for those classes is exactly k (not the modular value v).

3. **Inverse tree + forward contraction**: Every integer is in the inverse tree (by
   density → 1) AND every trajectory contracts (by the contraction certificates).
   If both facts can be made rigorous simultaneously, convergence follows.
   The gap: "density → 1" is computational for n ≤ 10,000; the contraction certificates
   have the unsafe residue gap. Neither is complete without the other.

4. **Bad streak scope clarification**: The Lean theorem `max_bad_streak_k3` proves no
   5 consecutive v₂=1 steps in ZMod(104). For actual integers ≤ 100,000, max streak
   is 16 (n=77671). The formal certificate covers only the modular domain — extending
   to actual integers requires the unsafe residue gap to be closed.

5. **k=13 structural discontinuity (Q5)**: The convergence window DP diverges at k=13
   (meta_pos=0, the meta-cycle completion). k=14 and k=15 bounce back. This is the
   clearest evidence yet that the tower has structure at k=13. Understanding WHY the
   DP fails at this level could reveal the algebraic obstruction. One approach: find the
   specific path or near-cycle in ZMod(13×2^13) that prevents certificates from firing,
   and characterize it arithmetically.

6. **Cumulative log correction is bounded (Q6)**: For n ≤ 9999, the cumulative
   correction (actual v₂ − modular v₂, summed over trajectory) lies in [−15, +12].
   At higher k, the certificate margin grows (W(15)=108, margin=2820 millibits) while
   the correction per unsafe step is bounded by the discrepancy. If the cumulative
   correction scales sublinearly with trajectory length, high-k certificates might
   survive the correction. This requires verifying the correction bound at k=14, 15.
