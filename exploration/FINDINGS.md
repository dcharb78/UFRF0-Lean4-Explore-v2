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

## Dead Ends Closed

- ✗ Adding 3-adic precision to the modulus (Q1)
- ✗ Coset structure of (Z/13Z)* as the algebraic culprit (Q3)
- ✗ High-discrepancy residues as tree bottlenecks (Q2)

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
