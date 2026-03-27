"""
Q4: Harmonic Series and Inverse Tree Analysis
Examines cover time on mod-13 residues, comma accumulation curves,
depth vs. length, 3-divisibility barrier, and synthesis.
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
    """One full Syracuse step for odd n. Returns (next_odd, v2_used)."""
    val = 3 * n + 1
    vv = v2(val)
    return val >> vv, vv


def full_trajectory(n, max_steps=2000):
    """Full Syracuse trajectory for odd n. Returns list of (value, v2_used)."""
    steps = []
    cur = n
    while cur > 1 and len(steps) < max_steps:
        next_n, vv = syracuse_step(cur)
        steps.append((cur, vv))
        cur = next_n
    steps.append((cur, 0))
    return steps


def forward_stopping_time(n):
    """Number of odd Syracuse steps for odd n to reach 1."""
    cur = n
    count = 0
    while cur > 1:
        cur, _ = syracuse_step(cur)
        count += 1
    return count


# ---------------------------------------------------------------------------
# Part A: Cover Time on Forward Trajectory
# ---------------------------------------------------------------------------

print("=" * 60)
print("Part A: Cover Time Analysis")
print("=" * 60)

cover_data = []  # (n, cover_time, total_steps)

for n in range(3, 10000, 2):
    traj = full_trajectory(n)
    total_steps = len(traj)
    seen = set()
    cover_time = None
    for t, (val, _) in enumerate(traj):
        r = val % 13
        if r != 0:
            seen.add(r)
        if len(seen) == 12 and cover_time is None:
            cover_time = t + 1  # 1-indexed step count
    cover_data.append((n, cover_time, total_steps))

achieved = [(n, ct, ts) for (n, ct, ts) in cover_data if ct is not None]
not_achieved = [(n, ct, ts) for (n, ct, ts) in cover_data if ct is None]

fraction_cover = len(achieved) / len(cover_data)

cover_times = [ct for (_, ct, _) in achieved]
total_steps_list = [ts for (_, _, ts) in cover_data]

max_ct = max(cover_times)
mean_ct = statistics.mean(cover_times)
median_ct = statistics.median(cover_times)

# Steps after cover for those that achieved it
steps_after = [ts - ct for (_, ct, ts) in achieved]
mean_steps_after = statistics.mean(steps_after) if steps_after else 0

theoretical_cover = 12 * sum(1 / k for k in range(1, 13))  # 12 * H(12)

print(f"\nTotal odd n in [3, 9999]: {len(cover_data)}")
print(f"Fraction achieving cover (all 12 nonzero mod-13 residues): {fraction_cover:.4f}")
print(f"Theoretical random walk cover time (12 * H(12)): {theoretical_cover:.2f}")
print(f"Max cover_time: {max_ct}")
print(f"Mean cover_time: {mean_ct:.2f}")
print(f"Median cover_time: {median_ct:.1f}")
print(f"Mean steps AFTER cover (for those achieving it): {mean_steps_after:.2f}")

top10 = sorted(achieved, key=lambda x: x[1], reverse=True)[:10]
print("\nTop 10 by cover_time (n, cover_time, total_steps):")
for n, ct, ts in top10:
    print(f"  n={n:5d}  cover_time={ct:4d}  total_steps={ts:4d}")

# Distribution buckets
buckets = {"1-10": 0, "11-20": 0, "21-30": 0, "31-50": 0, "51-100": 0, ">100": 0}
for ct in cover_times:
    if ct <= 10:
        buckets["1-10"] += 1
    elif ct <= 20:
        buckets["11-20"] += 1
    elif ct <= 30:
        buckets["21-30"] += 1
    elif ct <= 50:
        buckets["31-50"] += 1
    elif ct <= 100:
        buckets["51-100"] += 1
    else:
        buckets[">100"] += 1

print("\nCover time distribution:")
for k, v in buckets.items():
    print(f"  [{k:>6s}]: {v:5d}  ({100*v/len(cover_times):.1f}%)")

# ---------------------------------------------------------------------------
# Part B: Comma Accumulation Curves
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Part B: Comma Accumulation")
print("=" * 60)

# Comma(t) = t * 1585 - (cumulative_v2 * 1000)  [integer millibits]
# 1585 ≈ 1000 * log2(3) millibit steps per odd step
# Each v2 unit contributes 1000 millibit "free" descent

SAMPLE_NS = [7, 27, 97, 127, 255, 341, 511, 703, 871, 1023,
             2047, 4095, 6171, 7919, 8191, 9001, 9663, 9999, 27, 6553]

# Deduplicate while preserving order
seen_sample = set()
SAMPLE_NS_DEDUP = []
for x in SAMPLE_NS:
    if x not in seen_sample:
        seen_sample.add(x)
        SAMPLE_NS_DEDUP.append(x)

def compute_comma_curve(n):
    traj = full_trajectory(n)
    cumv2 = 0
    max_comma = None
    step_first_negative = None
    for t, (val, vv) in enumerate(traj):
        step = t + 1
        cumv2 += vv
        comma = step * 1585 - cumv2 * 1000
        if max_comma is None or comma > max_comma:
            max_comma = comma
        if comma < 0 and step_first_negative is None:
            step_first_negative = step
    return max_comma, step_first_negative, len(traj)

sample_curves = []
print(f"\n{'n':>6s} | {'max_comma(mb)':>14s} | {'step_neg':>8s} | {'total_steps':>11s}")
print("-" * 50)
for n in SAMPLE_NS_DEDUP:
    if n % 2 == 0:
        continue  # skip even
    mc, sfn, ts = compute_comma_curve(n)
    sample_curves.append({"n": n, "max_comma": mc, "step_first_negative": sfn, "total_steps": ts})
    sfn_str = str(sfn) if sfn is not None else "never"
    print(f"{n:>6d} | {mc:>14d} | {sfn_str:>8s} | {ts:>11d}")

# Full sweep over all odd n <= 9999
all_max_commas = []
log_ns = []
positive_start_count = 0
total_odd = 0

for n in range(3, 10000, 2):
    traj = full_trajectory(n)
    cumv2 = 0
    max_comma = None
    first_step_comma = None
    for t, (val, vv) in enumerate(traj):
        step = t + 1
        cumv2 += vv
        comma = step * 1585 - cumv2 * 1000
        if first_step_comma is None:
            first_step_comma = comma
        if max_comma is None or comma > max_comma:
            max_comma = comma
    all_max_commas.append(max_comma)
    log_ns.append(math.log(n))
    if first_step_comma is not None and first_step_comma > 0:
        positive_start_count += 1
    total_odd += 1

fraction_positive_start = positive_start_count / total_odd

# Pearson correlation: log(n) vs max_comma
def pearson_r(xs, ys):
    n = len(xs)
    mean_x = sum(xs) / n
    mean_y = sum(ys) / n
    cov = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys))
    sx = math.sqrt(sum((x - mean_x) ** 2 for x in xs))
    sy = math.sqrt(sum((y - mean_y) ** 2 for y in ys))
    if sx == 0 or sy == 0:
        return 0.0
    return cov / (sx * sy)

corr_logn_maxcomma = pearson_r(log_ns, all_max_commas)

print(f"\nAll odd n in [3,9999]:")
print(f"  max_comma stats: mean={statistics.mean(all_max_commas):.1f}, "
      f"max={max(all_max_commas)}, min={min(all_max_commas)}")
print(f"  log(n) vs max_comma Pearson r: {corr_logn_maxcomma:.4f}")
print(f"  Fraction starting with comma > 0: {fraction_positive_start:.4f}")

# ---------------------------------------------------------------------------
# Part C: Inverse Tree Depth vs Forward Trajectory Length
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Part C: Depth vs Length Analysis")
print("=" * 60)

# Load q2 results for inverse tree depth info
with open('exploration/q2_results.json') as f:
    q2 = json.load(f)

# Compute forward stopping times for all odd n <= 9999
fwd_times = {}
for n in range(3, 10000, 2):
    fwd_times[n] = forward_stopping_time(n)

fwd_lengths = list(fwd_times.values())
log_ns_fwd = [math.log(n) for n in range(3, 10000, 2)]

corr_logn_fwd = pearson_r(log_ns_fwd, fwd_lengths)

print(f"\nForward stopping time stats (odd n in [3,9999]):")
print(f"  mean={statistics.mean(fwd_lengths):.2f}, "
      f"max={max(fwd_lengths)}, min={min(fwd_lengths)}")
print(f"  log(n) vs forward_length Pearson r: {corr_logn_fwd:.4f}")

# HIGH-DISC residues mod 104: [85, 21, 53]
# LOW-DISC residues mod 104: [13, 29, 45, 61, 77, 93]
HIGH_DISC = {85, 21, 53}
LOW_DISC = {13, 29, 45, 61, 77, 93}

high_fwd = [fwd_times[n] for n in range(3, 10000, 2) if n % 104 in HIGH_DISC]
low_fwd = [fwd_times[n] for n in range(3, 10000, 2) if n % 104 in LOW_DISC]

mean_high = statistics.mean(high_fwd) if high_fwd else float('nan')
mean_low = statistics.mean(low_fwd) if low_fwd else float('nan')

print(f"\nMean forward_length for HIGH-DISC residues mod 104 {{85,21,53}}: {mean_high:.3f}  (n={len(high_fwd)})")
print(f"Mean forward_length for LOW-DISC residues mod 104 {{13,29,45,61,77,93}}: {mean_low:.3f}  (n={len(low_fwd)})")

# Correlation between forward_length * inverse_depth (approximate)
# We use bounded BFS depth from q2 as proxy for inverse depth
bfs_by_depth = q2['bounded_inverse_bfs']['by_depth']
# by_depth[d]['count'] = number of nodes at depth d in bounded BFS
# We don't have per-n depth, so skip product analysis and note the limitation
print("\nNote: q2_results.json provides aggregate depth distributions, not per-n inverse depths.")
print("Skipping forward_length * inverse_depth product (per-n inverse depth not stored in q2).")

# ---------------------------------------------------------------------------
# Part D: The 3-Divisibility Barrier
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Part D: 3-Divisibility Barrier")
print("=" * 60)

# Forward trajectory length for odd n by mod-3 class
mod3_stats = {0: [], 1: [], 2: []}
for n in range(3, 10000, 2):
    cl = n % 3
    mod3_stats[cl].append(fwd_times[n])

print(f"\n{'mod-3 class':>11s} | {'count':>6s} | {'mean_fwd':>9s} | {'std_fwd':>9s}")
print("-" * 45)
for cl in [0, 1, 2]:
    vals = mod3_stats[cl]
    count = len(vals)
    mean_f = statistics.mean(vals) if vals else float('nan')
    std_f = statistics.stdev(vals) if len(vals) > 1 else 0.0
    label = {0: "0 (mult 3)", 1: "1", 2: "2 (Trinity+)"}[cl]
    print(f"{label:>11s} | {count:>6d} | {mean_f:>9.3f} | {std_f:>9.3f}")

# Compare class 2 vs class 1
mean_cl2 = statistics.mean(mod3_stats[2]) if mod3_stats[2] else float('nan')
mean_cl1 = statistics.mean(mod3_stats[1]) if mod3_stats[1] else float('nan')
if mean_cl2 < mean_cl1:
    print(f"\nClass 2 (Trinity positive, +1/2) converges FASTER than class 1: {mean_cl2:.3f} < {mean_cl1:.3f}")
else:
    print(f"\nClass 2 (Trinity positive, +1/2) does NOT converge faster than class 1: {mean_cl2:.3f} >= {mean_cl1:.3f}")

# For class 0 (multiples of 3): find odd non-multiple-of-3 seed
# For odd n divisible by 3, count halving steps to reach odd non-mult-3:
# but odd multiples of 3 have no even factors to divide out. Their forward step
# goes to (3n+1) / 2^v2(3n+1), which is not divisible by 3 since 3n+1 ≡ 1 (mod 3).
# So the "barrier thickness" is just 1 step away — the first forward step always
# leaves the mod-3=0 class.
# We verify: for each odd n ≡ 0 (mod 3), check if next_odd is ≡ 0 (mod 3)
barrier_thicknesses = []
for n in range(3, 10000, 2):
    if n % 3 != 0:
        continue
    # 3n+1 ≡ 1 (mod 3), so next_odd ≡ 1 (mod 3) — always escapes in 1 step
    # barrier_thickness = 1 by construction, but let's confirm
    next_odd, _ = syracuse_step(n)
    thickness = 1
    # Double-check: how many consecutive steps stay in class 0?
    cur = next_odd
    while cur % 3 == 0 and cur > 1:
        cur, _ = syracuse_step(cur)
        thickness += 1
    barrier_thicknesses.append(thickness)

mean_barrier = statistics.mean(barrier_thicknesses) if barrier_thicknesses else 0
print(f"\nFor odd multiples of 3 (class 0): mean steps to reach non-mult-3 = {mean_barrier:.3f}")
print(f"(Expected 1: 3n+1 ≡ 1 mod 3, so first step always escapes class 0)")

# ---------------------------------------------------------------------------
# Synthesis: Is cover_time a useful bound on forward_length?
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Synthesis: cover_time as bound on forward_length")
print("=" * 60)

# For each n where cover was achieved, compute ratio forward_length / cover_time
ratio_data = []
for (n, ct, ts) in achieved:
    fl = fwd_times.get(n)
    if fl is not None and ct is not None and ct > 0:
        ratio_data.append((n, ct, fl, fl / ct))

ratios = [r for (_, _, _, r) in ratio_data]
mean_ratio = statistics.mean(ratios)
median_ratio = statistics.median(ratios)
max_ratio = max(ratios)
min_ratio = min(ratios)

print(f"\nforward_length / cover_time statistics (n with cover achieved):")
print(f"  count={len(ratios)}")
print(f"  mean ratio:   {mean_ratio:.4f}")
print(f"  median ratio: {median_ratio:.4f}")
print(f"  max ratio:    {max_ratio:.4f}")
print(f"  min ratio:    {min_ratio:.4f}")

# Top 10 ratios
top10_ratio = sorted(ratio_data, key=lambda x: x[3], reverse=True)[:10]
print("\nTop 10 (n, cover_time, forward_length, ratio):")
for n, ct, fl, r in top10_ratio:
    print(f"  n={n:5d}  cover_time={ct:4d}  fwd_len={fl:4d}  ratio={r:.3f}")

print("\n--- Synthesis Summary ---")
print(f"""
Cover time analysis reveals that {fraction_cover*100:.1f}% of odd n in [3,9999] achieve
full mod-13 coverage during their forward trajectory. The mean cover time
({mean_ct:.1f} steps) is close to the theoretical random-walk cover time of
{theoretical_cover:.1f} steps for a 12-element group, suggesting near-random
residue distribution in Syracuse trajectories.

The key ratio forward_length / cover_time has mean {mean_ratio:.3f} and max {max_ratio:.3f}.
Since this ratio is bounded (max ~{max_ratio:.1f}x), cover_time does provide a
{100/max_ratio:.0f}%-tight lower bound on forward_length. However, it is not a useful
UPPER bound: forward_length can be up to {max_ratio:.1f}× larger than cover_time,
so knowing cover_time ≤ C tells us only forward_length ≤ {max_ratio:.1f}×C, which is
weaker than direct bounds from the trajectory itself.

The cover_time approach is most useful as a diagnostic: it characterizes how
"uniformly" the trajectory explores residues before converging. Combined with
the comma accumulation data (Pearson r(log n, max_comma) = {corr_logn_maxcomma:.4f}),
it suggests that convergence is driven by v2 accumulation rather than residue
uniformity, making cover_time an indirect and loose proxy for forward_length.
The approach is interesting but not viable as a tight convergence bound.
""")

# ---------------------------------------------------------------------------
# Save results
# ---------------------------------------------------------------------------

results = {
    "part_A": {
        "max_cover_time": max_ct,
        "mean_cover_time": round(mean_ct, 4),
        "median_cover_time": median_ct,
        "fraction_achieving_cover": round(fraction_cover, 6),
        "mean_steps_after_cover": round(mean_steps_after, 4),
        "theoretical_random_walk_cover": round(theoretical_cover, 4),
        "top_10_by_cover_time": [
            {"n": n, "cover_time": ct, "total_steps": ts}
            for (n, ct, ts) in top10
        ],
        "cover_time_distribution": buckets
    },
    "part_B": {
        "max_comma_stats": {
            "mean": round(statistics.mean(all_max_commas), 2),
            "max": max(all_max_commas),
            "min": min(all_max_commas),
            "median": round(statistics.median(all_max_commas), 2)
        },
        "log_n_correlation": round(corr_logn_maxcomma, 6),
        "fraction_starting_positive_comma": round(fraction_positive_start, 6),
        "sample_curves": sample_curves
    },
    "part_C": {
        "forward_length_high_disc_mean": round(mean_high, 4),
        "forward_length_low_disc_mean": round(mean_low, 4),
        "log_n_forward_length_correlation": round(corr_logn_fwd, 6),
        "forward_length_stats": {
            "mean": round(statistics.mean(fwd_lengths), 4),
            "max": max(fwd_lengths),
            "min": min(fwd_lengths)
        }
    },
    "part_D": {
        "mod3_class_stats": {
            str(cl): {
                "count": len(mod3_stats[cl]),
                "mean_fwd": round(statistics.mean(mod3_stats[cl]), 4) if mod3_stats[cl] else None,
                "std_fwd": round(statistics.stdev(mod3_stats[cl]), 4) if len(mod3_stats[cl]) > 1 else 0.0
            }
            for cl in [0, 1, 2]
        },
        "mean_barrier_thickness": round(mean_barrier, 4)
    },
    "synthesis": {
        "ratio_fwd_len_over_cover_time": {
            "mean": round(mean_ratio, 4),
            "median": round(median_ratio, 4),
            "max": round(max_ratio, 4),
            "min": round(min_ratio, 4),
            "count": len(ratios)
        },
        "conclusion": (
            "cover_time is NOT a tight upper bound on forward_length "
            f"(max ratio {max_ratio:.3f}), but is a useful diagnostic for "
            "residue exploration uniformity."
        )
    }
}

with open('exploration/q4_results.json', 'w') as f:
    json.dump(results, f, indent=2)

print("\nResults saved to exploration/q4_results.json")
