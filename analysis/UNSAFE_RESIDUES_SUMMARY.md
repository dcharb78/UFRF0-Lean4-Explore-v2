# Unsafe Residues Analysis: Collatz/Syracuse Modular v2

## Key Result

**Do the contraction certificates survive the v2 discrepancy? NO**

Overcounting was detected. Max discrepancy = 5. The critical threshold is delta < 0.15. Certificates FAIL.

---

## Task 1: Unsafe Residue Enumeration

An **unsafe residue** at level k is an odd r in ZMod(13·2^k) with v2(3r+1) >= k.

| k | modulus | count_unsafe | all 13 mod-13 classes covered |
|---|---------|-------------|-------------------------------|
| 3 | 104 | 13 | YES |
| 4 | 208 | 13 | YES |
| 5 | 416 | 13 | YES |
| 6 | 832 | 13 | YES |
| 7 | 1664 | 13 | YES |
| 8 | 3328 | 13 | YES |
| 9 | 6656 | 13 | YES |
| 10 | 13312 | 13 | YES |

**Finding:** At every level k=3..10, there are exactly 13 unsafe residues, one for each residue class mod 13.

**Unsafe residues at k=3 (mod 104):**

`[5, 13, 21, 29, 37, 45, 53, 61, 69, 77, 85, 93, 101]`

---

## Task 2: v2 Discrepancy at k=3

For each of the 13 unsafe residues at k=3 (modulus=104), we checked all odd n ≡ r (mod 104) with n ≤ 10000.

**Maximum discrepancy (modular_v2 - actual_v2): 5**

Discrepancy found at: r=85, n=189, modular_v2=8, actual_v2=3.

---

## Task 3: Certificate Survival at k=3

**Certificate parameters:**
- v2_sum threshold: 16 bits over 10 steps
- Margin: 150 millibits = 0.150 bits
- Critical discrepancy delta for failure: delta >= 0.15

**True v2 distribution for each k=3 unsafe residue (n ≡ r mod 104, n ≤ 10000):**

| r | modular_v2 | min_actual_v2 | max_discrepancy | cert_survives |
|---|-----------|--------------|-----------------|---------------|
| 5 | 4 | 3 | 1 | NO |
| 13 | 3 | 3 | 0 | YES |
| 21 | 6 | 3 | 3 | NO |
| 29 | 3 | 3 | 0 | YES |
| 37 | 4 | 3 | 1 | NO |
| 45 | 3 | 3 | 0 | YES |
| 53 | 5 | 3 | 2 | NO |
| 61 | 3 | 3 | 0 | YES |
| 69 | 4 | 3 | 1 | NO |
| 77 | 3 | 3 | 0 | YES |
| 85 | 8 | 3 | 5 | NO |
| 93 | 3 | 3 | 0 | YES |
| 101 | 4 | 3 | 1 | NO |

**All k=3 certificates survive: NO**

---

## Task 4: Higher k (k=4..6)

For k=4,5,6 unsafe residues, checking min actual v2 vs modular v2 (n ≤ 10000):

| k | r | mod_v2 | min_actual_v2 | discrepancy | overcount |
|---|---|--------|--------------|-------------|-----------|
| 4 | 5 | 4 | 4 | 0 | NO |
| 4 | 21 | 6 | 4 | 2 | YES |
| 4 | 37 | 4 | 4 | 0 | NO |
| 4 | 53 | 5 | 4 | 1 | YES |
| 4 | 69 | 4 | 4 | 0 | NO |
| 4 | 85 | 8 | 4 | 4 | YES |
| 4 | 101 | 4 | 4 | 0 | NO |
| 4 | 117 | 5 | 4 | 1 | YES |
| 4 | 133 | 4 | 4 | 0 | NO |
| 4 | 149 | 6 | 4 | 2 | YES |
| 4 | 165 | 4 | 4 | 0 | NO |
| 4 | 181 | 5 | 4 | 1 | YES |
| 4 | 197 | 4 | 4 | 0 | NO |
| 5 | 21 | 6 | 5 | 1 | YES |
| 5 | 53 | 5 | 5 | 0 | NO |
| 5 | 85 | 8 | 5 | 3 | YES |
| 5 | 117 | 5 | 5 | 0 | NO |
| 5 | 149 | 6 | 5 | 1 | YES |
| 5 | 181 | 5 | 5 | 0 | NO |
| 5 | 213 | 7 | 5 | 2 | YES |
| 5 | 245 | 5 | 5 | 0 | NO |
| 5 | 277 | 6 | 5 | 1 | YES |
| 5 | 309 | 5 | 5 | 0 | NO |
| 5 | 341 | 10 | 5 | 5 | YES |
| 5 | 373 | 5 | 5 | 0 | NO |
| 5 | 405 | 6 | 5 | 1 | YES |
| 6 | 21 | 6 | 6 | 0 | NO |
| 6 | 85 | 8 | 6 | 2 | YES |
| 6 | 149 | 6 | 6 | 0 | NO |
| 6 | 213 | 7 | 6 | 1 | YES |
| 6 | 277 | 6 | 6 | 0 | NO |
| 6 | 341 | 10 | 6 | 4 | YES |
| 6 | 405 | 6 | 6 | 0 | NO |
| 6 | 469 | 7 | 6 | 1 | YES |
| 6 | 533 | 6 | 6 | 0 | NO |
| 6 | 597 | 8 | 6 | 2 | YES |
| 6 | 661 | 6 | 6 | 0 | NO |
| 6 | 725 | 7 | 6 | 1 | YES |
| 6 | 789 | 6 | 6 | 0 | NO |

---

## Task 5: Final Answer

### Can the contraction certificates survive the v2 discrepancy? **NO**

**Key numbers:**
- Max observed discrepancy (modular_v2 - actual_v2): **5** (at r=85 mod 104, n=189)
- Critical threshold for certificate survival: **delta < 0.15**
- Actual max delta: **5**, which far exceeds 0.15

### Why overcounting occurs

For an unsafe residue r at level k, write `3r+1 = 2^v * q` where `q` is odd and `v = v2(3r+1) >= k`.
For `n = r + 13·2^k·m`:

```
3n+1 = 2^k · (2^{v-k}·q + 39m)
```

So `actual_v2(3n+1) = k + v2(2^{v-k}·q + 39m)`.

When `v > k` (strict unsafe), the inner term `A = 2^{v-k}·q + 39m` can be **odd** when `m` is odd
(since `39m` is odd for odd `m`, and `2^{v-k}·q` is even). This gives `v2(A) = 0`, so
`actual_v2(3n+1) = k`, which is strictly **less than** the modular value `v`.

The discrepancy equals `v - k` in the worst case. The worst offender is r=85 at k=3:
`v2(3·85+1) = v2(256) = 8`, so worst discrepancy = `8 - 3 = 5`.

### Pattern of safe vs. unsafe residues

At each level k, exactly **half** the unsafe residues have `mod_v2 = k` (exact) — these are
"tight" residues where the modular computation is a lower bound and no overcount occurs.
The other half have `mod_v2 > k` and produce genuine overcounts. The tight ones are those
where `3r+1 ≡ 2^k (mod 2^{k+1})`, giving exactly `v2 = k`.

### What correction is needed

For any modular argument to produce valid contraction bounds, one of the following is required:

1. **Use the minimum actual v2**: For unsafe residue r at level k, replace `modular_v2(r)` with `k`
   in any contraction certificate. The true guaranteed v2 for any integer in that class is `k`,
   not `v2(3r+1)`.

2. **Use a higher modulus**: Work at level k' > v2(3r+1) for every residue r in the graph,
   so no residue is unsafe. This eliminates the problem entirely but requires a much larger modulus.

3. **Probabilistic argument**: For most integers in an unsafe class, actual_v2 >= modular_v2
   (only ~50% of m values make A odd). A probabilistic certificate might survive if the
   overcounting fraction is bounded.

### Magnitude of failure

With max discrepancy delta = 5 and margin = 0.15 bits:
- A certificate asserting v2_sum >= 16 over 10 steps could fail by up to 5 bits per step
- Worst case: actual v2_sum could be as low as 16 - 5 = 11 (not 16)
- The 10-step contraction ratio would be `2^11 / 3^10 ≈ 2048 / 59049 ≈ 0.035`, still contracting
- But the claimed certificate margin (0.15 bits) is violated

---
*Generated by collatz_unsafe_residues.py*
