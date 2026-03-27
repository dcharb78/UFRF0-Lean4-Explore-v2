"""
Q5: The Index of the Index — Self-Similar Tower Structure

Tests whether W(k) and the tower structure show self-similar or periodic
behavior when k is treated as a position in a 13-cycle rather than a flat integer.
"""

import json
import math
import statistics
from collections import defaultdict

# ---------------------------------------------------------------------------
# Core helpers
# ---------------------------------------------------------------------------

def v2(n):
    if n == 0:
        return -1
    return (n & -n).bit_length() - 1

def syracuse_step(n):
    val = 3 * n + 1
    vv = v2(val)
    return val >> vv, vv

def forward_stopping_time(n, max_steps=5000):
    cur = n
    count = 0
    while cur > 1 and count < max_steps:
        cur, _ = syracuse_step(cur)
        count += 1
    return count

def max_bad_streak_n(n, max_steps=5000):
    cur = n
    best = 0
    run = 0
    while cur > 1:
        nxt, vv = syracuse_step(cur)
        if vv == 1:
            run += 1
            if run > best:
                best = run
        else:
            run = 0
        cur = nxt
    return best

# ---------------------------------------------------------------------------
# Part A: Extend W(k) to k=15 using integer millibit DP
# ---------------------------------------------------------------------------
# drift(r) = 1585 - 1000 * v₂(r)  [millibit scale]
# Certificate fires when all W-length paths have sum < 0
# W(k) = smallest W such that max_drift_over_W_steps < 0

print("=" * 60)
print("Part A: DP Extension to k=15 (integer millibit DP)")
print("=" * 60)

def build_transition_graph(k):
    """Build Syracuse transition graph on ZMod(13 * 2^k). Returns dict r -> (vv, image)."""
    M = 13 * (1 << k)
    transitions = {}
    for r in range(1, M, 2):
        val = 3 * r + 1
        vv = v2(val)
        image = (val >> vv) % M
        # Ensure image is odd (always true for Syracuse map)
        transitions[r] = (vv, image)
    return M, transitions

def window_dp_integer(transitions, max_window=250):
    """
    Integer millibit DP. drift(r) = 1585 - 1000*v₂(r).
    dp[r] = max millibit sum over W steps starting at r.
    Returns (W_cert, max_streak, margin_at_W_cert)
    W_cert = smallest W where max(dp.values()) < 0.
    """
    odd_residues = list(transitions.keys())
    dp = {r: 0 for r in odd_residues}

    max_streak = 0
    for r in odd_residues:
        run = 0
        cur = r
        visited = set()
        while cur in transitions:
            vv, nxt = transitions[cur]
            if vv == 1:
                run += 1
            else:
                run = 0
            if run > max_streak:
                max_streak = run
            if nxt in visited:
                break
            visited.add(cur)
            cur = nxt

    W_cert = None
    margin_at_cert = None

    for w in range(1, max_window + 1):
        dp_next = {}
        for r in odd_residues:
            vv, image = transitions[r]
            drift = 1585 - 1000 * vv
            dp_next[r] = drift + dp[image]
        dp = dp_next
        max_val = max(dp.values())
        if w % 10 == 0:
            print(f"  k={current_k}, W={w}: max_drift={max_val}")
        if max_val < 0 and W_cert is None:
            W_cert = w
            margin_at_cert = -max_val
            break

    return W_cert, max_streak, margin_at_cert

results_A = []

for k in range(3, 16):
    current_k = k
    M = 13 * (1 << k)
    n_odd = M // 2
    print(f"\nk={k}: modulus={M}, odd residues={n_odd}")
    M, transitions = build_transition_graph(k)
    W_cert, ms, margin = window_dp_integer(transitions, max_window=500)
    w_over_k = W_cert / k if W_cert else None
    w_over_k1 = W_cert / (k + 1) if W_cert else None
    meta_pos = k % 13
    print(f"  max_bad_streak={ms}, W(k)={W_cert}, margin={margin}, meta_pos={meta_pos}")
    if W_cert:
        print(f"  W/k={w_over_k:.3f}, W/(k+1)={w_over_k1:.3f}")
    results_A.append({
        "k": k,
        "modulus": M,
        "n_odd_residues": n_odd,
        "max_bad_streak": ms,
        "W_k": W_cert,
        "margin": margin,
        "W_over_k": round(w_over_k, 4) if w_over_k else None,
        "W_over_k1": round(w_over_k1, 4) if w_over_k1 else None,
        "meta_position_k_mod13": meta_pos,
    })

print("\nSummary table:")
print(f"{'k':>3s} | {'M':>8s} | {'max_streak':>10s} | {'W(k)':>5s} | {'W/k':>6s} | {'meta_pos':>8s}")
print("-" * 55)
for row in results_A:
    print(f"{row['k']:>3d} | {row['modulus']:>8d} | {row['max_bad_streak']:>10d} | "
          f"{str(row['W_k']):>5s} | {str(row['W_over_k']):>6s} | {row['meta_position_k_mod13']:>8d}")

# ---------------------------------------------------------------------------
# Part B & C: Base-13 digit (d₀, d₁) vs bad streak — 2×2 table
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Parts B & C: Base-13 digit combinations vs bad streak")
print("=" * 60)

# Base-13 digits of n: d₀ = n%13, d₁ = (n//13)%13, d₂ = (n//169)%13
# Phase: 'E' if digit < 7 (expansion), 'C' if digit >= 7 (contraction)

table_streak = defaultdict(list)   # (ph0, ph1) -> list of max_bad_streak
table_fwd    = defaultdict(list)   # (ph0, ph1) -> list of fwd_len

for n in range(1, 100001, 2):
    d0 = n % 13
    d1 = (n // 13) % 13
    ph0 = 'E' if d0 < 7 else 'C'
    ph1 = 'E' if d1 < 7 else 'C'
    key = (ph0, ph1)
    ms = max_bad_streak_n(n)
    fl = forward_stopping_time(n)
    table_streak[key].append(ms)
    table_fwd[key].append(fl)

print("\n2×2 table: mean bad streak by (d₀ phase, d₁ phase)")
print(f"{'(d₀,d₁)':>10s} | {'count':>6s} | {'mean_streak':>11s} | {'max_streak':>10s} | {'mean_fwd':>9s}")
print("-" * 58)
for ph0 in ['E', 'C']:
    for ph1 in ['E', 'C']:
        key = (ph0, ph1)
        vals = table_streak[key]
        fwds = table_fwd[key]
        if not vals:
            continue
        print(f"({ph0},{ph1}):      | {len(vals):>6d} | {statistics.mean(vals):>11.4f} | "
              f"{max(vals):>10d} | {statistics.mean(fwds):>9.4f}")

# Also test individual d₂ (meta-meta position)
print("\nBase-13 digit summary (d₀ alone):")
for d0_phase in ['E', 'C']:
    combined_streak = []
    combined_fwd = []
    for ph1 in ['E', 'C']:
        key = (d0_phase, ph1)
        combined_streak.extend(table_streak[key])
        combined_fwd.extend(table_fwd[key])
    print(f"  d₀={d0_phase}: mean_streak={statistics.mean(combined_streak):.4f}, "
          f"mean_fwd={statistics.mean(combined_fwd):.4f}, n={len(combined_streak)}")

# Compute max delta between 2×2 cells
means = {k: statistics.mean(v) for k, v in table_streak.items()}
max_mean = max(means.values())
min_mean = min(means.values())
print(f"\nMax delta in mean_streak across 2×2 cells: {max_mean - min_mean:.4f}")
print(f"  Best (longest streak):  {max(means, key=means.get)} = {max_mean:.4f}")
print(f"  Best (shortest streak): {min(means, key=means.get)} = {min_mean:.4f}")

# ---------------------------------------------------------------------------
# Part D: W(k) sequence meta-analysis
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Part D: W(k) sequence meta-analysis")
print("=" * 60)

W_vals = [row['W_k'] for row in results_A if row['W_k'] is not None]
k_vals = [row['k'] for row in results_A if row['W_k'] is not None]

increments = [W_vals[i+1] - W_vals[i] for i in range(len(W_vals)-1)]
W_mod13 = [w % 13 for w in W_vals]

print(f"\nW(k) sequence: {W_vals}")
print(f"Increments W(k+1)-W(k): {increments}")
print(f"W(k) mod 13: {W_mod13}")

# Linear fit: W ≈ a*k + b
if len(k_vals) >= 2:
    k_mean = statistics.mean(k_vals)
    W_mean = statistics.mean(W_vals)
    slope_num = sum((k - k_mean)*(w - W_mean) for k,w in zip(k_vals, W_vals))
    slope_den = sum((k - k_mean)**2 for k in k_vals)
    slope = slope_num / slope_den
    intercept = W_mean - slope * k_mean
    print(f"\nLinear fit W(k) ≈ {slope:.4f}·k + {intercept:.4f}")

    # Residuals
    residuals = [w - (slope*k + intercept) for k,w in zip(k_vals, W_vals)]
    print(f"Residuals: {[round(r, 2) for r in residuals]}")

    # Does the residual pattern look periodic?
    # Check if odd/even k matters
    odd_k_resid = [r for i,r in enumerate(residuals) if k_vals[i] % 2 == 1]
    even_k_resid = [r for i,r in enumerate(residuals) if k_vals[i] % 2 == 0]
    print(f"Mean residual (odd k):  {statistics.mean(odd_k_resid):.3f}" if odd_k_resid else "")
    print(f"Mean residual (even k): {statistics.mean(even_k_resid):.3f}" if even_k_resid else "")

# Check for "flip" around k=7 or k=13
# Split into k=3..7 (seed-to-flip) vs k=8..13 (flip-to-return)
if len(results_A) >= 8:
    phase1 = [row for row in results_A if 3 <= row['k'] <= 7 and row['W_k']]
    phase2 = [row for row in results_A if 8 <= row['k'] <= 13 and row['W_k']]
    phase3 = [row for row in results_A if row['k'] > 13 and row['W_k']]
    if phase1 and phase2:
        slope1 = (phase1[-1]['W_k'] - phase1[0]['W_k']) / (phase1[-1]['k'] - phase1[0]['k'])
        slope2 = (phase2[-1]['W_k'] - phase2[0]['W_k']) / (phase2[-1]['k'] - phase2[0]['k'])
        print(f"\nW(k) slope k=3..7: {slope1:.4f}")
        print(f"W(k) slope k=8..13: {slope2:.4f}")
        if phase3:
            slope3 = (phase3[-1]['W_k'] - phase3[0]['W_k']) / max(1, phase3[-1]['k'] - phase3[0]['k'])
            print(f"W(k) slope k=14+: {slope3:.4f}")

# ---------------------------------------------------------------------------
# Part E: Fibonacci prime positions
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Part E: Fibonacci prime positions in the tower")
print("=" * 60)

# Fibonacci primes and their indices
FIB_PRIMES = [
    (3,  2),
    (4,  3),
    (5,  5),
    (7,  13),
    (11, 89),
    (13, 233),
    (17, 1597),
    (23, 28657),
    (29, 514229),
    (43, 433494437),
    (47, 2971215073),
]

print(f"\n{'F_idx':>6s} | {'Fib prime p':>12s} | {'p mod 13':>8s} | {'fwd_stop':>8s} | "
      f"{'max_streak':>10s} | {'W(k) at idx':>11s}")
print("-" * 75)

for idx, p in FIB_PRIMES:
    p_mod13 = p % 13
    phase = 'expansion' if p_mod13 < 7 else ('contraction' if p_mod13 > 0 else 'source/return')
    if p <= 1000000:
        fl = forward_stopping_time(p)
        ms = max_bad_streak_n(p)
    else:
        fl = "N/A (too large)"
        ms = "N/A"
    # W(k) at k=idx if computed
    w_at_idx = next((row['W_k'] for row in results_A if row['k'] == idx), None)
    print(f"{idx:>6d} | {p:>12d} | {p_mod13:>8d} | {str(fl):>8s} | {str(ms):>10s} | "
          f"{str(w_at_idx):>11s}")

# What are the mod-13 values of Fibonacci prime indices?
print(f"\nFibonacci prime indices mod 13: {[idx % 13 for idx, p in FIB_PRIMES]}")
print(f"Fibonacci primes mod 13:        {[p % 13 for idx, p in FIB_PRIMES]}")

# ---------------------------------------------------------------------------
# Part F: Period-13 check in W(k)
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Part F: Period-13 / self-similar check in W(k)")
print("=" * 60)

W_sequence = [(row['k'], row['W_k'], row['W_over_k']) for row in results_A if row['W_k']]

# Group by meta_position (k mod 13)
by_meta = defaultdict(list)
for k, w, wk in W_sequence:
    by_meta[k % 13].append((k, w, wk))

print("\nW(k) grouped by meta-position (k mod 13):")
for meta in sorted(by_meta.keys()):
    entries = by_meta[meta]
    print(f"  meta_pos={meta}: {[(k, w) for k,w,_ in entries]}")

# Check if W/k is approximately constant across meta-positions
all_wk = [wk for _, _, wk in W_sequence if wk is not None]
if len(all_wk) > 2:
    print(f"\nW/k values: {[round(x, 3) for x in all_wk]}")
    print(f"Mean W/k: {statistics.mean(all_wk):.4f}")
    print(f"Stdev W/k: {statistics.stdev(all_wk):.4f}" if len(all_wk) > 1 else "")
    print(f"W/k range: [{min(all_wk):.4f}, {max(all_wk):.4f}]")

# Is there a visible break at k=7 (meta-flip) in W/k?
wk_before7 = [wk for k, _, wk in W_sequence if k < 7 and wk]
wk_after7  = [wk for k, _, wk in W_sequence if k >= 7 and wk]
if wk_before7 and wk_after7:
    print(f"\nMean W/k for k<7:  {statistics.mean(wk_before7):.4f}")
    print(f"Mean W/k for k>=7: {statistics.mean(wk_after7):.4f}")

# ---------------------------------------------------------------------------
# Save results
# ---------------------------------------------------------------------------

table_streak_save = {}
table_fwd_save = {}
for key in [('E','E'), ('E','C'), ('C','E'), ('C','C')]:
    k_str = f"{key[0]}_{key[1]}"
    vals = table_streak[key]
    fwds = table_fwd[key]
    table_streak_save[k_str] = {
        "count": len(vals),
        "mean_streak": round(statistics.mean(vals), 4) if vals else None,
        "max_streak": max(vals) if vals else None,
        "mean_fwd": round(statistics.mean(fwds), 4) if fwds else None,
    }

results = {
    "part_A_W_k_table": results_A,
    "part_A_linear_fit": {
        "slope": round(slope, 6) if len(k_vals) >= 2 else None,
        "intercept": round(intercept, 6) if len(k_vals) >= 2 else None,
    },
    "parts_BC_digit_table": table_streak_save,
    "parts_BC_max_delta_mean_streak": round(max_mean - min_mean, 4),
    "part_E_fibonacci_primes": [
        {
            "index": idx,
            "prime": p,
            "p_mod13": p % 13,
            "fwd_stopping_time": forward_stopping_time(p) if p <= 1000000 else None,
            "max_bad_streak": max_bad_streak_n(p) if p <= 1000000 else None,
            "W_k_at_idx": next((row['W_k'] for row in results_A if row['k'] == idx), None),
        }
        for idx, p in FIB_PRIMES
    ],
    "part_F_W_over_k": {
        "values": [{"k": k, "W_over_k": wk} for k,_,wk in W_sequence],
        "mean": round(statistics.mean(all_wk), 4) if all_wk else None,
        "stdev": round(statistics.stdev(all_wk), 4) if len(all_wk) > 1 else None,
        "mean_k_lt7": round(statistics.mean(wk_before7), 4) if wk_before7 else None,
        "mean_k_ge7": round(statistics.mean(wk_after7), 4) if wk_after7 else None,
    }
}

with open('exploration/q5_results.json', 'w') as f:
    json.dump(results, f, indent=2)

print("\nResults saved to exploration/q5_results.json")
