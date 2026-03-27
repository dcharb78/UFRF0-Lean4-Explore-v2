"""
q4_harmonic_spiral.py
Collatz trajectories as walks on the spiral of fifths.

Each Syracuse step has ratio 3/2^v2(3n+1). These ratios have musical names:
- v2=1: ratio 3/2 = perfect fifth (expanding)
- v2=2: ratio 3/4 = contracting (fifth down an octave)
- v2=k: ratio 3/2^k = fifth transposed by (k-1) octaves

Uses exact arithmetic (fractions.Fraction) for all numerical work;
float only for display.
"""

import json
import random
import statistics
from collections import Counter, defaultdict
from fractions import Fraction

# ---------------------------------------------------------------------------
# Core arithmetic helpers
# ---------------------------------------------------------------------------

def v2(n):
    """2-adic valuation of n."""
    if n == 0:
        return -1
    return (n & -n).bit_length() - 1


def syracuse_step(n):
    """One full Syracuse step: odd n -> (3n+1)/2^v2(3n+1).
    Returns (next_n, v2_used)."""
    assert n % 2 == 1, f"n must be odd, got {n}"
    val = 3 * n + 1
    vv = v2(val)
    return val >> vv, vv


def trajectory(n, max_steps=2000):
    """Full Syracuse trajectory for odd n.
    Returns list of (value, v2_used) pairs."""
    steps = []
    while n > 1 and len(steps) < max_steps:
        n, vv = syracuse_step(n)
        steps.append((n, vv))
    return steps


def trajectory_pitch_classes(n, max_steps=500):
    """Returns list of (residue mod 13, v2 at this step) for each step."""
    pitches = []
    cur = n
    while cur > 1 and len(pitches) < max_steps:
        pitches.append((cur % 13, v2(3 * cur + 1)))
        cur, _ = syracuse_step(cur)
    pitches.append((cur % 13, 0))  # final value (1 mod 13 = 1)
    return pitches


# Exact log2(3) as Fraction for comma computation
# 3^(892254565955501) ≈ 2^(562949953421312) — use the given approximation
LOG2_3_NUM = 892254565955501
LOG2_3_DEN = 562949953421312
LOG2_3_FRAC = Fraction(LOG2_3_NUM, LOG2_3_DEN)
LOG2_3_FLOAT = float(LOG2_3_FRAC)

# ---------------------------------------------------------------------------
# Step 1: Pitch class mapping
# ---------------------------------------------------------------------------

def analyze_pitch_classes(odd_ns):
    """For each n, compute pitch-class sequence."""
    results = {}
    for n in odd_ns:
        results[n] = trajectory_pitch_classes(n)
    return results


# ---------------------------------------------------------------------------
# Step 2: Cover time analysis
# ---------------------------------------------------------------------------

NONZERO_RESIDUES_13 = set(range(1, 13))  # 1..12


def cover_time(pitch_seq):
    """Number of steps until all 12 nonzero residues mod 13 are visited.
    Returns None if not all visited within the trajectory."""
    visited = set()
    for i, (res, _) in enumerate(pitch_seq):
        if res != 0:
            visited.add(res)
        if visited == NONZERO_RESIDUES_13:
            return i + 1  # 1-indexed step count
    return None


def steps_after_cover_until_1(pitch_seq, ct):
    """How many steps after cover time until trajectory reaches 1."""
    if ct is None:
        return None
    # Find first index where value == 1 (residue 1, v2 == 0 marks final)
    for i, (res, vv) in enumerate(pitch_seq):
        if vv == 0 and res == 1:
            if i + 1 >= ct:
                return (i + 1) - ct
            else:
                return 0
    return None


def random_walk_cover_time_13(n_trials=10000, rng=None):
    """Empirical cover time for a uniform random walk on (Z/13Z)* (nonzero residues)."""
    if rng is None:
        rng = random.Random(42)
    elements = list(range(1, 13))
    cover_times = []
    for _ in range(n_trials):
        visited = set()
        steps = 0
        while visited != NONZERO_RESIDUES_13:
            visited.add(rng.choice(elements))
            steps += 1
        cover_times.append(steps)
    return cover_times


def analyze_cover_times(pitch_data):
    """Compute cover time statistics across all trajectories."""
    cts = []
    steps_after = []
    total_lengths = []

    for n, pitch_seq in pitch_data.items():
        ct = cover_time(pitch_seq)
        total_len = len(pitch_seq)
        total_lengths.append(total_len)
        if ct is not None:
            cts.append(ct)
            sa = steps_after_cover_until_1(pitch_seq, ct)
            if sa is not None:
                steps_after.append(sa)

    return {
        "cover_times": cts,
        "steps_after": steps_after,
        "total_lengths": total_lengths,
        "fraction_covered": len(cts) / len(pitch_data),
    }


# ---------------------------------------------------------------------------
# Step 3: Interval sequence analysis
# ---------------------------------------------------------------------------

def all_v2_sequences(odd_ns, max_n_for_streak=100000, max_steps=2000):
    """
    3a: Distribution of v2 values.
    3b: Bigrams.
    3c: Trigrams, look for forbidden patterns.
    3d: Max bad streak (v2=1 run) for n <= max_n_for_streak.
    """
    v2_counts = Counter()
    bigrams = Counter()
    trigrams = Counter()
    total_steps = 0

    # For 3d we need a separate pass over all odd n <= max_n_for_streak
    max_bad_streak = 0
    max_bad_streak_n = None

    # Detailed analysis for n <= 1001
    for n in odd_ns:
        traj = trajectory(n, max_steps=max_steps)
        vs = [vv for (_, vv) in traj]
        for vv in vs:
            v2_counts[vv] += 1
        total_steps += len(vs)
        for i in range(len(vs) - 1):
            bigrams[(vs[i], vs[i + 1])] += 1
        for i in range(len(vs) - 2):
            trigrams[(vs[i], vs[i + 1], vs[i + 2])] += 1

    # 3d: bad streak check for all n <= max_n_for_streak
    print(f"  Computing bad streaks for all odd n <= {max_n_for_streak}...")
    for n in range(1, max_n_for_streak + 1, 2):
        traj = trajectory(n, max_steps=max_steps)
        vs = [vv for (_, vv) in traj]
        # Find longest run of v2==1
        streak = 0
        for vv in vs:
            if vv == 1:
                streak += 1
                if streak > max_bad_streak:
                    max_bad_streak = streak
                    max_bad_streak_n = n
            else:
                streak = 0

    # Compute distribution
    v2_dist = {}
    for k in range(1, 10):
        v2_dist[k] = v2_counts.get(k, 0) / total_steps if total_steps > 0 else 0.0

    # Possible bigrams: all (a, b) with a,b >= 1
    all_possible_bigrams = {(a, b) for a in range(1, 8) for b in range(1, 8)}
    observed_bigrams = set(bigrams.keys())
    forbidden_bigrams = [pair for pair in sorted(all_possible_bigrams) if pair not in observed_bigrams]

    # Trigrams: look for (1,1,1) etc.
    all_possible_trigrams = {(a, b, c) for a in range(1, 6) for b in range(1, 6) for c in range(1, 6)}
    observed_trigrams = set(trigrams.keys())
    forbidden_trigrams = [t for t in sorted(all_possible_trigrams) if t not in observed_trigrams]

    # Specifically check if (1,1,1,1,1) 5-gram ever appears
    print("  Checking for 5-consecutive v2=1 in n<=100000...")
    fivegram_found = False
    fivegram_example = None
    for n in range(1, max_n_for_streak + 1, 2):
        traj = trajectory(n, max_steps=max_steps)
        vs = [vv for (_, vv) in traj]
        streak = 0
        for vv in vs:
            if vv == 1:
                streak += 1
                if streak >= 5:
                    fivegram_found = True
                    fivegram_example = n
                    break
            else:
                streak = 0
        if fivegram_found:
            break

    return {
        "v2_counts": dict(v2_counts),
        "v2_dist": v2_dist,
        "total_steps": total_steps,
        "bigrams": {str(k): v for k, v in bigrams.most_common()},
        "forbidden_bigrams": [list(p) for p in forbidden_bigrams],
        "forbidden_trigrams": [list(t) for t in forbidden_trigrams[:20]],  # first 20
        "max_bad_streak": max_bad_streak,
        "max_bad_streak_n": max_bad_streak_n,
        "fivegram_found": fivegram_found,
        "fivegram_example": fivegram_example,
    }


# ---------------------------------------------------------------------------
# Step 4: Comma accumulation curves
# ---------------------------------------------------------------------------

def comma_curve(n, max_steps=2000):
    """
    comma(t) = log2(3)*t - sum(v2_i for i in 1..t)
    Uses Fraction for exact accumulation, float for display.
    Returns list of (t, comma_float) and key stats.
    """
    traj = trajectory(n, max_steps=max_steps)
    curve = []
    acc_v2 = 0
    first_negative_t = None
    max_positive = Fraction(0)
    max_positive_t = 0

    for t, (val, vv) in enumerate(traj, 1):
        acc_v2 += vv
        comma_exact = LOG2_3_FRAC * t - acc_v2
        comma_float = float(comma_exact)
        curve.append((t, comma_float))
        if comma_exact > max_positive:
            max_positive = comma_exact
            max_positive_t = t
        if comma_exact < 0 and first_negative_t is None:
            first_negative_t = t

    steps_after_neg = None
    if first_negative_t is not None:
        total = len(traj)
        steps_after_neg = total - first_negative_t

    return {
        "curve": curve,
        "first_negative_t": first_negative_t,
        "max_positive": float(max_positive),
        "max_positive_t": max_positive_t,
        "steps_after_neg": steps_after_neg,
        "total_steps": len(traj),
    }


def analyze_comma_across_all(odd_ns, max_steps=2000):
    """Across all odd n in 1..1001: distribution of max_positive_comma, fraction starting positive."""
    max_positives = []
    start_positive_count = 0

    for n in odd_ns:
        traj = trajectory(n, max_steps=max_steps)
        if not traj:
            continue
        _, vv0 = traj[0]
        comma_1 = LOG2_3_FRAC * 1 - vv0
        if comma_1 > 0:
            start_positive_count += 1

        acc_v2 = 0
        max_pos = Fraction(0)
        for t, (val, vv) in enumerate(traj, 1):
            acc_v2 += vv
            comma = LOG2_3_FRAC * t - acc_v2
            if comma > max_pos:
                max_pos = comma
        max_positives.append(float(max_pos))

    return {
        "mean_max_positive": statistics.mean(max_positives) if max_positives else 0.0,
        "median_max_positive": statistics.median(max_positives) if max_positives else 0.0,
        "max_max_positive": max(max_positives) if max_positives else 0.0,
        "fraction_starting_positive": start_positive_count / len(odd_ns),
    }


# ---------------------------------------------------------------------------
# Step 5: Resonance at residue 0 mod 13
# ---------------------------------------------------------------------------

def analyze_residue_0(pitch_data):
    """Find gaps between successive visits to residue 0 mod 13."""
    all_gaps = []
    comma_at_zero = []

    for n, pitch_seq in pitch_data.items():
        last_zero_idx = None
        # Also track comma
        acc_v2 = 0
        for i, (res, vv) in enumerate(pitch_seq):
            acc_v2 += vv
            if res == 0:
                comma = float(LOG2_3_FRAC * (i + 1) - acc_v2)
                comma_at_zero.append(comma)
                if last_zero_idx is not None:
                    gap = i - last_zero_idx
                    all_gaps.append(gap)
                last_zero_idx = i

    gap_counter = Counter(all_gaps)
    # Check divisibility
    all_by_13 = all(g % 13 == 0 for g in all_gaps) if all_gaps else None
    gcd_of_gaps = _gcd_list(all_gaps) if all_gaps else None

    return {
        "all_gaps": all_gaps,
        "gap_distribution": dict(gap_counter.most_common(20)),
        "total_zero_visits": len(comma_at_zero),
        "all_gaps_multiple_of_13": all_by_13,
        "gcd_of_gaps": gcd_of_gaps,
        "mean_comma_at_zero": statistics.mean(comma_at_zero) if comma_at_zero else 0.0,
        "median_comma_at_zero": statistics.median(comma_at_zero) if comma_at_zero else 0.0,
    }


def _gcd_list(lst):
    import math
    if not lst:
        return None
    g = lst[0]
    for x in lst[1:]:
        g = math.gcd(g, x)
    return g


# ---------------------------------------------------------------------------
# Step 6: Tritone flip analysis
# ---------------------------------------------------------------------------

UPPER_HALF = set(range(7, 13))   # residues 7-12 (past flip)
LOWER_HALF = set(range(1, 7))    # residues 1-6

def analyze_tritone(pitch_data):
    """Classify each step as expansion/contraction/zero, correlate with v2."""
    v2_expansion = []
    v2_contraction = []
    v2_zero = []

    streak_expansion = 0
    streak_contraction = 0
    max_bad_expansion = 0
    max_bad_contraction = 0
    bad_streak_expansion_count = 0
    bad_streak_contraction_count = 0

    for n, pitch_seq in pitch_data.items():
        cur_streak_exp = 0
        cur_streak_con = 0
        for res, vv in pitch_seq:
            if vv == 0:
                v2_zero.append(0)
                continue
            if res in UPPER_HALF:
                v2_expansion.append(vv)
                if vv == 1:
                    cur_streak_exp += 1
                    if cur_streak_exp > max_bad_expansion:
                        max_bad_expansion = cur_streak_exp
                else:
                    cur_streak_exp = 0
                cur_streak_con = 0
            elif res in LOWER_HALF:
                v2_contraction.append(vv)
                if vv == 1:
                    cur_streak_con += 1
                    if cur_streak_con > max_bad_contraction:
                        max_bad_contraction = cur_streak_con
                else:
                    cur_streak_con = 0
                cur_streak_exp = 0
            else:  # residue 0
                v2_zero.append(vv)
                cur_streak_exp = 0
                cur_streak_con = 0

    mean_exp = statistics.mean(v2_expansion) if v2_expansion else 0.0
    mean_con = statistics.mean(v2_contraction) if v2_contraction else 0.0

    # Fraction of v2=1 in each class
    frac_v2_1_exp = v2_expansion.count(1) / len(v2_expansion) if v2_expansion else 0.0
    frac_v2_1_con = v2_contraction.count(1) / len(v2_contraction) if v2_contraction else 0.0

    return {
        "mean_v2_expansion": mean_exp,
        "mean_v2_contraction": mean_con,
        "frac_v2_1_expansion": frac_v2_1_exp,
        "frac_v2_1_contraction": frac_v2_1_con,
        "count_expansion_steps": len(v2_expansion),
        "count_contraction_steps": len(v2_contraction),
        "max_bad_streak_expansion": max_bad_expansion,
        "max_bad_streak_contraction": max_bad_contraction,
    }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print("=" * 70)
    print("Q4: Harmonic Spiral Analysis of Collatz Trajectories")
    print("=" * 70)

    odd_ns = list(range(1, 1002, 2))  # odd n in 1..1001
    print(f"Analyzing {len(odd_ns)} odd starting values in 1..1001\n")

    # ------------------------------------------------------------------
    # Step 1: Pitch class mapping
    # ------------------------------------------------------------------
    print("Step 1: Computing pitch class sequences...")
    pitch_data = analyze_pitch_classes(odd_ns)
    print(f"  Done. Sample for n=3: {pitch_data[3][:6]}...")

    # Quick check: does every trajectory end at residue 1 mod 13?
    end_residues = Counter(seq[-1][0] for seq in pitch_data.values() if seq)
    print(f"  Final residue distribution: {dict(end_residues)}")

    # ------------------------------------------------------------------
    # Step 2: Cover time analysis
    # ------------------------------------------------------------------
    print("\nStep 2: Cover time analysis...")
    ct_raw = analyze_cover_times(pitch_data)
    cts = ct_raw["cover_times"]
    steps_after = ct_raw["steps_after"]
    total_lengths = ct_raw["total_lengths"]

    ct_mean = statistics.mean(cts) if cts else 0.0
    ct_median = statistics.median(cts) if cts else 0.0
    ct_max = max(cts) if cts else 0
    ct_dist = dict(Counter(cts).most_common(20))

    print(f"  Cover time  mean={ct_mean:.2f}  median={ct_median:.1f}  max={ct_max}")
    print(f"  Fraction of trajectories that cover all 12 nonzero residues: {ct_raw['fraction_covered']:.3f}")
    if steps_after:
        print(f"  Steps after cover until 1:  mean={statistics.mean(steps_after):.2f}  max={max(steps_after)}")

    # Correlation
    if len(cts) == len(total_lengths[:len(cts)]):
        tl_for_covered = total_lengths[:len(cts)]
        # simple Pearson manually
        if len(cts) > 1:
            mean_ct = statistics.mean(cts)
            mean_tl = statistics.mean(total_lengths)
            cov = sum((c - mean_ct) * (t - mean_tl) for c, t in zip(cts, total_lengths)) / len(cts)
            std_ct = statistics.stdev(cts)
            std_tl = statistics.stdev(total_lengths)
            corr = cov / (std_ct * std_tl) if std_ct * std_tl > 0 else 0.0
            print(f"  Pearson correlation (cover_time, total_length) = {corr:.4f}")

    # Random walk cover time
    print("  Computing random walk cover time (10000 trials)...")
    rw_cts = random_walk_cover_time_13()
    rw_mean = statistics.mean(rw_cts)
    rw_median = statistics.median(rw_cts)
    print(f"  Random walk on (Z/13Z)*:  mean={rw_mean:.2f}  median={rw_median:.1f}")

    cover_time_stats = {
        "mean": ct_mean,
        "median": ct_median,
        "max": ct_max,
        "distribution": ct_dist,
        "fraction_covered": ct_raw["fraction_covered"],
        "steps_after_mean": statistics.mean(steps_after) if steps_after else None,
        "steps_after_max": max(steps_after) if steps_after else None,
        "random_walk_mean": rw_mean,
        "random_walk_median": rw_median,
    }

    # ------------------------------------------------------------------
    # Step 3: Interval sequence analysis
    # ------------------------------------------------------------------
    print("\nStep 3: Interval (v2) sequence analysis...")
    interval_data = all_v2_sequences(odd_ns, max_n_for_streak=100000)

    print("\n  3a. v2 distribution (compare to Geometric(1/2)):")
    geom_p = 0.5
    for k in range(1, 9):
        observed = interval_data["v2_dist"].get(k, 0.0)
        # P(v2=k) for geometric on {1,2,3,...} with P(v2>=k) = (1/2)^(k-1)
        # Actually v2(3n+1) where n is odd: 3n+1 ≡ 0 mod 2 always, so v2>=1 always.
        # P(v2=k) = P(exactly k factors of 2) ~ 1/2^k (geometric starting at 1)
        # Geometric(p=1/2) on {1,2,3,...}: P(X=k) = (1/2)^k ... but sum = 1/2 + 1/4 + ... = 1, wait:
        # If v2>=1 always, then P(v2=k) = (1-p)*p^(k-1) shifted: P(v2=1)=1/2, P(v2=2)=1/4...
        geom_val = (0.5) ** k  # = (1/2)^k giving sum=1 on {1,2,...}
        print(f"    P(v2={k}) observed={observed:.4f}  geometric(p=1/2)={geom_val:.4f}")

    print("\n  3b. Top bigrams:")
    top_bigrams = list(interval_data["bigrams"].items())[:10]
    for bg, cnt in top_bigrams:
        print(f"    {bg}: {cnt}")
    print(f"  Forbidden bigrams (within v2 in 1..7): {interval_data['forbidden_bigrams']}")

    print("\n  3c. Forbidden trigrams (within v2 in 1..5, first 10):")
    print(f"    {interval_data['forbidden_trigrams'][:10]}")

    print(f"\n  3d. Max bad streak (consecutive v2=1) for n <= 100000:")
    print(f"    max_bad_streak = {interval_data['max_bad_streak']}  (at n={interval_data['max_bad_streak_n']})")
    print(f"    Five-consecutive v2=1 found? {interval_data['fivegram_found']} (example n={interval_data['fivegram_example']})")
    print(f"    Lean bound for k=3 level: max_bad_streak <= 4 for ZMod(104).")

    interval_distribution = {f"P_v2_{k}": interval_data["v2_dist"].get(k, 0.0) for k in range(1, 9)}

    # ------------------------------------------------------------------
    # Step 4: Comma accumulation curves
    # ------------------------------------------------------------------
    print("\nStep 4: Comma accumulation curves...")
    special_ns = [3, 7, 13, 27, 255]
    comma_curves = {}
    for n in special_ns:
        result = comma_curve(n)
        comma_curves[n] = result
        print(f"\n  n={n}:")
        print(f"    Total steps: {result['total_steps']}")
        print(f"    Max positive comma: {result['max_positive']:.6f} at step {result['max_positive_t']}")
        print(f"    First negative at step: {result['first_negative_t']}")
        print(f"    Steps after first negative: {result['steps_after_neg']}")
        # Print first few comma values
        preview = result["curve"][:8]
        print(f"    Comma values (first 8): {[f'{c:.4f}' for _, c in preview]}")

    print("\n  Comma statistics across all odd n in 1..1001...")
    comma_stats = analyze_comma_across_all(odd_ns)
    print(f"    Mean max positive comma: {comma_stats['mean_max_positive']:.4f}")
    print(f"    Median max positive comma: {comma_stats['median_max_positive']:.4f}")
    print(f"    Max of max positive comma: {comma_stats['max_max_positive']:.4f}")
    print(f"    Fraction where comma(1) > 0: {comma_stats['fraction_starting_positive']:.4f}")

    # Note: comma(1) > 0 iff log2(3)*1 > v2, i.e., log2(3) > v2.
    # Since log2(3) ≈ 1.585, this means v2(3n+1)=1, which gives comma ≈ 0.585 > 0.

    # ------------------------------------------------------------------
    # Step 5: Residue 0 analysis
    # ------------------------------------------------------------------
    print("\nStep 5: Resonance at residue 0 mod 13...")
    res0_stats = analyze_residue_0(pitch_data)
    print(f"  Total visits to residue 0: {res0_stats['total_zero_visits']}")
    print(f"  All gaps multiple of 13? {res0_stats['all_gaps_multiple_of_13']}")
    print(f"  GCD of all gaps: {res0_stats['gcd_of_gaps']}")
    print(f"  Mean comma at residue-0 visits: {res0_stats['mean_comma_at_zero']:.4f}")
    print(f"  Median comma at residue-0 visits: {res0_stats['median_comma_at_zero']:.4f}")
    gap_dist_top = dict(sorted(res0_stats["gap_distribution"].items())[:15])
    print(f"  Gap distribution (top): {gap_dist_top}")

    # ------------------------------------------------------------------
    # Step 6: Tritone flip
    # ------------------------------------------------------------------
    print("\nStep 6: Tritone flip analysis (mod 13: upper half 7-12 vs lower half 1-6)...")
    tritone_stats = analyze_tritone(pitch_data)
    print(f"  Mean v2 at expansion steps (residue 7-12): {tritone_stats['mean_v2_expansion']:.4f}")
    print(f"  Mean v2 at contraction steps (residue 1-6): {tritone_stats['mean_v2_contraction']:.4f}")
    print(f"  Fraction v2=1 at expansion steps: {tritone_stats['frac_v2_1_expansion']:.4f}")
    print(f"  Fraction v2=1 at contraction steps: {tritone_stats['frac_v2_1_contraction']:.4f}")
    print(f"  Count expansion steps: {tritone_stats['count_expansion_steps']}")
    print(f"  Count contraction steps: {tritone_stats['count_contraction_steps']}")
    print(f"  Max bad streak in expansion half: {tritone_stats['max_bad_streak_expansion']}")
    print(f"  Max bad streak in contraction half: {tritone_stats['max_bad_streak_contraction']}")

    # ------------------------------------------------------------------
    # Step 7: Summary and JSON save
    # ------------------------------------------------------------------
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    print(f"""
Key Findings:
1. Max bad streak (v2=1 run) in n<=100000: {interval_data['max_bad_streak']}
   Lean bound for ZMod(104) at k=3: max 4 consecutive v2=1.
   Consistent? {interval_data['max_bad_streak'] <= 4}
   Five-consecutive v2=1 found in actual integers? {interval_data['fivegram_found']}

2. Forbidden 2-grams among v2 in 1..7: {interval_data['forbidden_bigrams']}
   (These v2 sequences never appear in trajectories n<=1001)

3. Tritone flip (mod 13) correlation with v2:
   Expansion (upper half 7-12): mean v2 = {tritone_stats['mean_v2_expansion']:.4f}, P(v2=1) = {tritone_stats['frac_v2_1_expansion']:.4f}
   Contraction (lower half 1-6): mean v2 = {tritone_stats['mean_v2_contraction']:.4f}, P(v2=1) = {tritone_stats['frac_v2_1_contraction']:.4f}
   {'Expansion steps have HIGHER mean v2 (more contraction force)' if tritone_stats['mean_v2_expansion'] > tritone_stats['mean_v2_contraction'] else 'Contraction steps have HIGHER mean v2'}

4. Cover time analysis:
   Collatz: mean={ct_mean:.2f}, median={ct_median:.1f}, max={ct_max}
   Random walk on (Z/13Z)*: mean={rw_mean:.2f}, median={rw_median:.1f}
   {'Collatz cover time FASTER than random walk' if ct_mean < rw_mean else 'Collatz cover time SIMILAR TO or SLOWER than random walk'}

5. Comma analysis:
   Fraction where comma(1)>0 (v2=1 at first step): {comma_stats['fraction_starting_positive']:.4f}
   Mean max positive comma: {comma_stats['mean_max_positive']:.4f}

6. Residue-0 gaps:
   GCD of all gaps between residue-0 visits: {res0_stats['gcd_of_gaps']}
   All gaps multiple of 13? {res0_stats['all_gaps_multiple_of_13']}
""")

    results = {
        "cover_time_stats": cover_time_stats,
        "interval_distribution": interval_distribution,
        "forbidden_bigrams": interval_data["forbidden_bigrams"],
        "forbidden_trigrams": interval_data["forbidden_trigrams"],
        "bad_streak_max_observed": interval_data["max_bad_streak"],
        "bad_streak_max_n": interval_data["max_bad_streak_n"],
        "fivegram_found": interval_data["fivegram_found"],
        "fivegram_example": interval_data["fivegram_example"],
        "comma_stats": comma_stats,
        "comma_curves_special": {
            str(n): {
                "total_steps": r["total_steps"],
                "max_positive": r["max_positive"],
                "max_positive_t": r["max_positive_t"],
                "first_negative_t": r["first_negative_t"],
                "steps_after_neg": r["steps_after_neg"],
                "curve_preview": [(t, c) for t, c in r["curve"][:20]],
            }
            for n, r in comma_curves.items()
        },
        "tritone_stats": tritone_stats,
        "residue_0_gaps": {
            "gcd_of_gaps": res0_stats["gcd_of_gaps"],
            "all_gaps_multiple_of_13": res0_stats["all_gaps_multiple_of_13"],
            "total_zero_visits": res0_stats["total_zero_visits"],
            "mean_comma_at_zero": res0_stats["mean_comma_at_zero"],
            "median_comma_at_zero": res0_stats["median_comma_at_zero"],
            "gap_distribution_top20": res0_stats["gap_distribution"],
        },
        "v2_counts": interval_data["v2_counts"],
        "random_walk_cover_time": {
            "mean": rw_mean,
            "median": rw_median,
        },
        "analysis_params": {
            "n_range": "1..1001 odd",
            "bad_streak_n_range": "1..100000 odd",
            "max_steps": 2000,
            "log2_3_approx": f"{LOG2_3_NUM}/{LOG2_3_DEN}",
        },
    }

    out_path = "/Users/dcharb/Documents/collatz/UFRF0-Lean4-Explore-v2/exploration/q4_results.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"Results saved to {out_path}")


if __name__ == "__main__":
    main()
