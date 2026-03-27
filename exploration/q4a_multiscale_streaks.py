"""
Q4A: Multi-Scale Bad Streak Analysis

Tests whether long bad streaks (v₂=1 runs) at fine resolution are
compensated by contraction at coarser scales (mod 169, mod 2197).

The bound max_bad_streak = k+1 applies at resolution k.
n=77671 (17 bits, streak=16) sits at k≈17, so streak < k+1 — consistent.
The question: is coarse-scale contraction "paying for" fine-scale bad streaks?
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


def max_bad_streak(n, max_steps=5000):
    """Longest consecutive run of v₂=1 steps in the Syracuse trajectory of n."""
    cur = n
    best = 0
    run = 0
    streak_start = None
    best_start = None
    step = 0
    while cur > 1 and step < max_steps:
        nxt, vv = syracuse_step(cur)
        step += 1
        if vv == 1:
            if run == 0:
                streak_start = step
            run += 1
            if run > best:
                best = run
                best_start = streak_start
        else:
            run = 0
            streak_start = None
        cur = nxt
    return best, best_start


def forward_stopping_time(n, max_steps=5000):
    cur = n
    count = 0
    while cur > 1 and count < max_steps:
        cur, _ = syracuse_step(cur)
        count += 1
    return count


def multi_scale_position(n):
    m13   = n % 13
    m169  = n % 169
    m2197 = n % 2197
    return {
        'mod_13':    m13,
        'mod_169':   m169,
        'mod_2197':  m2197,
        'phase_13':  'expansion'   if m13   < 7    else 'contraction',
        'phase_169': 'expansion'   if m169  < 85   else 'contraction',
        'phase_2197':'expansion'   if m2197 < 1099 else 'contraction',
        'flip_dist_13':  abs(m13   - 6.5),
        'flip_dist_169': abs(m169  - 84.5),
    }


def breathing_score(n):
    """Net breathing across concurrent scales.
    Positive = net expansion, Negative = net contraction."""
    s1 = (n % 13)   - 6.5
    s2 = (n % 169)  - 84.5
    s3 = (n % 2197) - 1098.5
    return s1/13 + s2/169 + s3/2197


# ---------------------------------------------------------------------------
# Step 1: Find all long bad streaks for odd n in [1, 100000]
# ---------------------------------------------------------------------------

print("=" * 60)
print("Step 1: Finding longest bad streaks (odd n ≤ 100,000)")
print("=" * 60)

streak_data = []   # (n, max_streak, bit_length)

for n in range(1, 100001, 2):
    ms, _ = max_bad_streak(n)
    streak_data.append((n, ms, n.bit_length()))

streak_data.sort(key=lambda x: -x[1])
top20 = streak_data[:20]

print(f"\nTop 20 longest bad streaks:")
print(f"{'n':>8s}  {'streak':>6s}  {'bits':>5s}")
print("-" * 25)
for n, ms, bl in top20:
    print(f"{n:>8d}  {ms:>6d}  {bl:>5d}")

max_streak_val = streak_data[0][1]
print(f"\nGlobal max streak: {max_streak_val}")
print(f"At n={streak_data[0][0]} (bits={streak_data[0][2]})")


# ---------------------------------------------------------------------------
# Step 2: Multi-scale position for top-streak numbers
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Step 2: Multi-scale position for top-streak numbers")
print("=" * 60)

print(f"\n{'n':>8s}  {'streak':>6s}  {'bits':>5s}  {'mod13':>5s}  {'mod169':>6s}  "
      f"{'mod2197':>7s}  {'ph13':>11s}  {'ph169':>11s}  {'ph2197':>12s}")
print("-" * 95)
for n, ms, bl in top20:
    pos = multi_scale_position(n)
    print(f"{n:>8d}  {ms:>6d}  {bl:>5d}  {pos['mod_13']:>5d}  {pos['mod_169']:>6d}  "
          f"{pos['mod_2197']:>7d}  {pos['phase_13']:>11s}  {pos['phase_169']:>11s}  "
          f"{pos['phase_2197']:>12s}")


# ---------------------------------------------------------------------------
# Step 3: For streak ≥ 10, what fraction are in coarse contraction?
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Step 3: Coarse-scale phase for long-streak numbers")
print("=" * 60)

long_streak_threshold = 10
long_streak_ns = [(n, ms, bl) for (n, ms, bl) in streak_data if ms >= long_streak_threshold]
print(f"\nNumbers with bad streak ≥ {long_streak_threshold}: {len(long_streak_ns)}")

if long_streak_ns:
    contr_169  = sum(1 for (n, ms, bl) in long_streak_ns
                     if multi_scale_position(n)['phase_169'] == 'contraction')
    contr_2197 = sum(1 for (n, ms, bl) in long_streak_ns
                     if multi_scale_position(n)['phase_2197'] == 'contraction')
    contr_both = sum(1 for (n, ms, bl) in long_streak_ns
                     if multi_scale_position(n)['phase_169'] == 'contraction'
                     and multi_scale_position(n)['phase_2197'] == 'contraction')
    total_long = len(long_streak_ns)
    print(f"  In contraction at scale-2 (mod 169):   {contr_169}/{total_long} = "
          f"{100*contr_169/total_long:.1f}%")
    print(f"  In contraction at scale-3 (mod 2197):  {contr_2197}/{total_long} = "
          f"{100*contr_2197/total_long:.1f}%")
    print(f"  In contraction at BOTH scales:          {contr_both}/{total_long} = "
          f"{100*contr_both/total_long:.1f}%")

    # Baseline: all odd n ≤ 100000
    total_odd = 50000
    # About half should be in contraction at each scale by symmetry
    print(f"\n  Baseline (random expectation): ~50% contraction at each scale")


# ---------------------------------------------------------------------------
# Step 4: Verify n=77671 specifically
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Step 4: Detailed analysis of n=77671")
print("=" * 60)

n77 = 77671
ms77, streak_start77 = max_bad_streak(n77)
pos77 = multi_scale_position(n77)
fwd77 = forward_stopping_time(n77)

print(f"\nn = {n77}")
print(f"Bits: {n77.bit_length()}")
print(f"mod 13:   {n77 % 13}  (flip at 6.5, phase: {pos77['phase_13']})")
print(f"mod 169:  {n77 % 169}  (flip at 84.5, phase: {pos77['phase_169']})")
print(f"mod 2197: {n77 % 2197}  (flip at 1098.5, phase: {pos77['phase_2197']})")
print(f"mod 104:  {n77 % 104}  (ZMod 13×8)")
print(f"mod 208:  {n77 % 208}")
print(f"Max bad streak: {ms77} (starts at step {streak_start77})")
print(f"Forward stopping time: {fwd77}")

# Full trajectory showing bad streak context
print(f"\nFull trajectory of n=77671 (showing v₂ values):")
cur = n77
step = 0
v2_seq = []
while cur > 1 and step < 200:
    nxt, vv = syracuse_step(cur)
    v2_seq.append(vv)
    step += 1
    cur = nxt

# Find the streak
run = 0
best_run = 0
best_end = 0
streak_run = 0
streak_at = []
for i, vv in enumerate(v2_seq):
    if vv == 1:
        streak_run += 1
        if streak_run > best_run:
            best_run = streak_run
            best_end = i
    else:
        streak_run = 0

best_start_idx = best_end - best_run + 1

print(f"\nv₂ sequence (steps {best_start_idx-3}..{best_end+5}):")
window = v2_seq[max(0, best_start_idx-3):best_end+6]
labels = list(range(max(0, best_start_idx-3), min(len(v2_seq), best_end+6)))
for lab, vv in zip(labels, window):
    marker = " ← STREAK" if best_start_idx <= lab <= best_end else ""
    print(f"  step {lab+1:3d}: v₂={vv}{marker}")

# What happens right after the streak?
if best_end + 1 < len(v2_seq):
    post_streak = v2_seq[best_end+1:best_end+6]
    print(f"\nPost-streak v₂ values (up to 5 steps): {post_streak}")
    print(f"First post-streak v₂: {v2_seq[best_end+1] if best_end+1 < len(v2_seq) else 'N/A'}")


# ---------------------------------------------------------------------------
# Step 5: 2D histogram — max_bad_streak vs phase at scale 2 (mod 169)
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Step 5: 2D histogram — streak length vs scale-2 phase")
print("=" * 60)

# bucket streaks 0..20+
histogram = {}  # (streak_bucket, phase) -> count
for n, ms, bl in streak_data:
    bucket = min(ms, 20)
    phase = multi_scale_position(n)['phase_169']
    key = (bucket, phase)
    histogram[key] = histogram.get(key, 0) + 1

print(f"\n{'streak':>6s}  {'expansion':>10s}  {'contraction':>12s}  {'%_contr':>8s}")
print("-" * 42)
for bucket in range(0, 21):
    exp_cnt   = histogram.get((bucket, 'expansion'), 0)
    contr_cnt = histogram.get((bucket, 'contraction'), 0)
    total = exp_cnt + contr_cnt
    if total == 0:
        continue
    pct_contr = 100 * contr_cnt / total
    bucket_label = f"{bucket}+" if bucket == 20 else str(bucket)
    print(f"{bucket_label:>6s}  {exp_cnt:>10d}  {contr_cnt:>12d}  {pct_contr:>7.1f}%")

# Summary by streak >= threshold
print(f"\nBy streak threshold:")
print(f"{'streak_ge':>10s}  {'%_contr_169':>12s}  {'%_contr_2197':>13s}  count")
print("-" * 50)
for thresh in [0, 5, 8, 10, 12, 14, 16]:
    subset = [(n, ms, bl) for (n, ms, bl) in streak_data if ms >= thresh]
    if not subset:
        continue
    c169  = sum(1 for (n,ms,bl) in subset if multi_scale_position(n)['phase_169']  == 'contraction')
    c2197 = sum(1 for (n,ms,bl) in subset if multi_scale_position(n)['phase_2197'] == 'contraction')
    tot = len(subset)
    print(f"{thresh:>10d}  {100*c169/tot:>11.1f}%  {100*c2197/tot:>12.1f}%  {tot:>6d}")


# ---------------------------------------------------------------------------
# Step 6: Breathing score analysis
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Step 6: Breathing Score Analysis")
print("=" * 60)

# For ALL odd n ≤ 100,000
bs_data  = []   # (n, bs, max_streak, fwd_len)
bs_vals  = []
fwd_vals = []
streak_vals = []

for n, ms, bl in streak_data:  # streak_data is all odd n ≤ 100,000
    bs  = breathing_score(n)
    fl  = forward_stopping_time(n)
    bs_data.append((n, bs, ms, fl))
    bs_vals.append(bs)
    fwd_vals.append(fl)
    streak_vals.append(ms)

# Pearson correlation: breathing_score vs forward_length
def pearson_r(xs, ys):
    n = len(xs)
    mx = sum(xs) / n
    my = sum(ys) / n
    cov = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    sx = math.sqrt(sum((x - mx)**2 for x in xs))
    sy = math.sqrt(sum((y - my)**2 for y in ys))
    if sx == 0 or sy == 0:
        return 0.0
    return cov / (sx * sy)

r_bs_fwd    = pearson_r(bs_vals, fwd_vals)
r_bs_streak = pearson_r(bs_vals, streak_vals)

print(f"\nBreathing score stats (all odd n ≤ 100,000):")
print(f"  min:    {min(bs_vals):.6f}")
print(f"  max:    {max(bs_vals):.6f}")
print(f"  mean:   {statistics.mean(bs_vals):.6f}")
print(f"  stdev:  {statistics.stdev(bs_vals):.6f}")
print(f"\nPearson r(breathing_score, forward_length): {r_bs_fwd:.6f}")
print(f"Pearson r(breathing_score, max_bad_streak): {r_bs_streak:.6f}")

# Is breathing_score bounded?
bs_bound = max(abs(min(bs_vals)), abs(max(bs_vals)))
print(f"\nBreathing score bound (|max|): {bs_bound:.6f}")
theoretical_bound = 0.5/13 + 0.5/169 + 0.5/2197
print(f"Theoretical bound (sum of half-ranges): {theoretical_bound:.6f}")

# Quartile analysis: does high breathing_score predict long trajectory?
sorted_by_bs = sorted(bs_data, key=lambda x: x[1])
n_total = len(sorted_by_bs)
q1_fwd = statistics.mean([fl for (_, bs, ms, fl) in sorted_by_bs[:n_total//4]])
q4_fwd = statistics.mean([fl for (_, bs, ms, fl) in sorted_by_bs[3*n_total//4:]])
q1_streak = statistics.mean([ms for (_, bs, ms, fl) in sorted_by_bs[:n_total//4]])
q4_streak = statistics.mean([ms for (_, bs, ms, fl) in sorted_by_bs[3*n_total//4:]])

print(f"\nQuartile comparison (low vs high breathing_score):")
print(f"  Bottom 25% bs: mean fwd_len={q1_fwd:.3f}, mean streak={q1_streak:.3f}")
print(f"  Top 25% bs:    mean fwd_len={q4_fwd:.3f}, mean streak={q4_streak:.3f}")

# Phase correlation
n_both_contr = sum(1 for (n, bs, ms, fl) in bs_data
                   if multi_scale_position(n)['phase_169'] == 'contraction'
                   and multi_scale_position(n)['phase_2197'] == 'contraction'
                   and ms >= 10)
n_long = sum(1 for (n, bs, ms, fl) in bs_data if ms >= 10)
print(f"\nAmong streak ≥ 10: both-contraction = {n_both_contr}/{n_long}")


# ---------------------------------------------------------------------------
# Synthesis
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Synthesis: Does coarse contraction compensate fine-scale streaks?")
print("=" * 60)

long_data = [(n, ms, bl) for (n, ms, bl) in streak_data if ms >= 10]
if long_data:
    c169_long  = sum(1 for (n,ms,bl) in long_data if multi_scale_position(n)['phase_169']  == 'contraction')
    c2197_long = sum(1 for (n,ms,bl) in long_data if multi_scale_position(n)['phase_2197'] == 'contraction')
    tot_long = len(long_data)
    pct_169  = 100 * c169_long / tot_long
    pct_2197 = 100 * c2197_long / tot_long

    if pct_169 > 60 or pct_2197 > 60:
        verdict = "YES — long bad streaks are preferentially in coarse-scale contraction."
    elif pct_169 < 40 or pct_2197 < 40:
        verdict = "OPPOSITE — long bad streaks are preferentially in coarse-scale EXPANSION."
    else:
        verdict = "NO — coarse-scale phase is uniformly distributed for long-streak numbers."

    print(f"\nVerdict: {verdict}")
    print(f"  Scale-2 (mod 169) contraction for streak≥10:  {pct_169:.1f}%")
    print(f"  Scale-3 (mod 2197) contraction for streak≥10: {pct_2197:.1f}%")
    print(f"  Baseline expectation: ~50%")
    print(f"\n  breathing_score vs forward_length: r={r_bs_fwd:.4f}")
    print(f"  breathing_score vs max_streak:      r={r_bs_streak:.4f}")
else:
    verdict = "No numbers with streak >= 10 found."


# ---------------------------------------------------------------------------
# Save results
# ---------------------------------------------------------------------------

results = {
    "step1_top20_streaks": [
        {"n": n, "max_streak": ms, "bit_length": bl}
        for (n, ms, bl) in top20
    ],
    "global_max_streak": max_streak_val,
    "global_max_streak_n": streak_data[0][0],
    "step3_long_streak_phase": {
        "threshold": long_streak_threshold,
        "count": len(long_streak_ns) if long_streak_ns else 0,
        "pct_contraction_169":  round(100*contr_169/len(long_streak_ns), 2) if long_streak_ns else None,
        "pct_contraction_2197": round(100*contr_2197/len(long_streak_ns), 2) if long_streak_ns else None,
        "pct_both_contraction": round(100*contr_both/len(long_streak_ns), 2) if long_streak_ns else None,
    },
    "step4_n77671": {
        "max_streak": ms77,
        "streak_start_step": streak_start77,
        "forward_stopping_time": fwd77,
        "mod_13":   n77 % 13,
        "mod_169":  n77 % 169,
        "mod_2197": n77 % 2197,
        "mod_104":  n77 % 104,
        "mod_208":  n77 % 208,
        "phase_13":   pos77['phase_13'],
        "phase_169":  pos77['phase_169'],
        "phase_2197": pos77['phase_2197'],
        "post_streak_v2": v2_seq[best_end+1] if best_end+1 < len(v2_seq) else None,
    },
    "step5_histogram_summary": {
        str(thresh): {
            "count": len([(n,ms,bl) for (n,ms,bl) in streak_data if ms >= thresh]),
            "pct_contr_169":  round(100*sum(1 for (n,ms,bl) in streak_data
                                            if ms >= thresh and
                                            multi_scale_position(n)['phase_169'] == 'contraction') /
                                    max(1, len([(n,ms,bl) for (n,ms,bl) in streak_data if ms >= thresh])), 2),
        }
        for thresh in [0, 5, 8, 10, 12, 14, 16]
        if len([(n,ms,bl) for (n,ms,bl) in streak_data if ms >= thresh]) > 0
    },
    "step6_breathing_score": {
        "min":    round(min(bs_vals), 8),
        "max":    round(max(bs_vals), 8),
        "mean":   round(statistics.mean(bs_vals), 8),
        "stdev":  round(statistics.stdev(bs_vals), 8),
        "theoretical_bound": round(theoretical_bound, 8),
        "pearson_r_bs_fwd":    round(r_bs_fwd, 6),
        "pearson_r_bs_streak": round(r_bs_streak, 6),
        "q1_mean_fwd":    round(q1_fwd, 4),
        "q4_mean_fwd":    round(q4_fwd, 4),
        "q1_mean_streak": round(q1_streak, 4),
        "q4_mean_streak": round(q4_streak, 4),
    },
    "synthesis": {
        "verdict": verdict,
        "pct_contr_169_streak_ge10":  round(pct_169, 2) if long_data else None,
        "pct_contr_2197_streak_ge10": round(pct_2197, 2) if long_data else None,
    }
}

with open('exploration/q4a_results.json', 'w') as f:
    json.dump(results, f, indent=2)

print("\nResults saved to exploration/q4a_results.json")
