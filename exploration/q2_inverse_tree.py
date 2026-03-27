"""
Inverse Collatz tree exploration.

The Syracuse map: odd n -> (3n+1) / 2^v2(3n+1)  (result is odd)

Inverse map: given odd n, odd predecessors m satisfy
    3m + 1 = n * 2^j   =>   m = (n * 2^j - 1) / 3
for some j >= 1, with m odd and positive.

Divisibility condition:
    n ≡ 1 (mod 3): valid j are 2, 4, 6, ...  (j even)
    n ≡ 2 (mod 3): valid j are 1, 3, 5, ...  (j odd)
    n ≡ 0 (mod 3): NO odd predecessors

Key insight: The branching factor is ~20 per level.
At depth k the number of distinct odd integers reachable is O(20^k).
Enumerating all nodes past depth ~7 is infeasible (tens of millions+).

Strategy:
  (A) For coverage questions (which integers appear) we use FORWARD Collatz:
      compute Syracuse(n) repeatedly and record the depth at which each
      odd integer maps to 1.  This is the standard "stopping time."
      depth_to_root[n] = number of odd steps from n until reaching 1.

  (B) For structural analysis (mod-13, mod-104 distribution) we limit BFS
      to nodes <= BOUND (e.g. 10^7) so we can track the actual tree structure
      within that window.

  (C) For the deep inverse tree we enumerate the first few levels fully
      (depths 0..8 fit in memory) and analyse their properties.
"""

import json
from collections import deque, defaultdict

# ---------------------------------------------------------------------------
# Step 1: Odd predecessor function  (exact integer arithmetic)
# ---------------------------------------------------------------------------

def odd_predecessors(n, max_j=20):
    """Find all odd m such that Syracuse(m) = n.
    m = (n * 2^j - 1) / 3 for valid j, m odd and positive.
    """
    if n % 3 == 0:
        return []   # no odd predecessors for multiples of 3

    preds = []
    for j in range(1, max_j + 1):
        val = n * (1 << j) - 1          # exact: n * 2^j - 1
        if val % 3 == 0:
            m = val // 3
            if m > 0 and m % 2 == 1:
                preds.append((m, j))

    return preds


# ---------------------------------------------------------------------------
# Step 2a: Forward Collatz stopping time (most reliable for coverage)
# ---------------------------------------------------------------------------

def v2(n):
    """2-adic valuation."""
    if n == 0:
        return -1
    return (n & -n).bit_length() - 1


def syracuse(n):
    """One odd step: n must be odd."""
    x = 3 * n + 1
    return x >> v2(x)


def collatz_depth(n, max_steps=10000):
    """Number of odd Syracuse steps from n until reaching 1.
    Returns None if exceeds max_steps (should not happen for reasonable n)."""
    steps = 0
    x = n
    while x != 1:
        if x % 2 == 0:
            x //= 2
        else:
            x = syracuse(x)
        steps += 1
        if steps > max_steps:
            return None
    return steps


def compute_forward_depths(limit=10000):
    """For each odd integer in [1, limit], compute its Collatz depth to 1.
    depth = number of odd Syracuse steps until reaching 1.
    Returns dict: n -> depth (odd steps only)."""
    depths = {}
    for n in range(1, limit + 1, 2):
        x = n
        odd_steps = 0
        while x != 1:
            # do even steps without counting
            while x % 2 == 0:
                x //= 2
            if x == 1:
                break
            x = 3 * x + 1
            odd_steps += 1
            # do even steps
            while x % 2 == 0:
                x //= 2
        depths[n] = odd_steps
    return depths


# ---------------------------------------------------------------------------
# Step 2b: Bounded BFS (only track nodes <= BOUND)
# ---------------------------------------------------------------------------

def build_bounded_inverse_tree(bound=10_000_000, max_depth=40):
    """BFS the inverse Collatz tree from 1, keeping only nodes <= bound.
    Returns depth dict for those nodes."""
    depth = {1: 0}
    queue = deque([1])

    while queue:
        n = queue.popleft()
        d = depth[n]
        if d >= max_depth:
            continue

        for (m, j) in odd_predecessors(n, max_j=60):
            if m <= bound and m not in depth:
                depth[m] = d + 1
                queue.append(m)

    return depth


# ---------------------------------------------------------------------------
# Step 3: Full BFS for first few depths (to study tree structure)
# ---------------------------------------------------------------------------

def build_inverse_tree_to_depth(max_depth=8, max_nodes=5_000_000):
    """BFS the inverse Collatz tree up to max_depth.
    Returns (depth_dict, by_depth_list)."""
    depth = {1: 0}
    queue = deque([1])
    by_depth = defaultdict(list)
    by_depth[0].append(1)

    while queue:
        n = queue.popleft()
        d = depth[n]
        if d >= max_depth:
            continue

        for (m, j) in odd_predecessors(n, max_j=60):
            if m not in depth:
                depth[m] = d + 1
                by_depth[d + 1].append(m)
                queue.append(m)
                if len(depth) >= max_nodes:
                    break

        if len(depth) >= max_nodes:
            break

    return depth, by_depth


# ---------------------------------------------------------------------------
# Step 4: Unsafe residues mod 104
# ---------------------------------------------------------------------------

UNSAFE_RESIDUES_104 = [5, 13, 21, 29, 37, 45, 53, 61, 69, 77, 85, 93, 101]
HIGH_DISC = {85, 21, 53}
LOW_DISC  = {13, 29, 45, 61, 77, 93}


# ---------------------------------------------------------------------------
# Step 6: Tower compatibility mod 208 -> mod 104
# ---------------------------------------------------------------------------

def inverse_tree_modM(M, max_depth=8):
    """BFS inverse tree in ZMod(M) space."""
    seed = 1 % M
    depth_m = {seed: 0}
    queue = deque([seed])
    while queue:
        n = queue.popleft()
        d = depth_m[n]
        if d >= max_depth:
            continue
        for j in range(1, 61):
            val = n * (1 << j) - 1
            if val % 3 == 0:
                m = (val // 3) % M
                if m % 2 == 1 and m not in depth_m:
                    depth_m[m] = d + 1
                    queue.append(m)
    return depth_m


def tower_compatibility(max_depth=8):
    depth104 = inverse_tree_modM(104, max_depth=max_depth)
    depth208 = inverse_tree_modM(208, max_depth=max_depth)

    violations = []
    for r208, d208 in depth208.items():
        r104 = r208 % 104
        if r104 not in depth104:
            violations.append((r208, d208, r104, "missing"))
        elif depth104[r104] > d208:
            violations.append((r208, d208, r104, "later"))

    return {
        "mod104_residues": len(depth104),
        "mod208_residues": len(depth208),
        "mod104_depth": {str(k): v for k, v in sorted(depth104.items())},
        "violations": len(violations),
        "violation_examples": violations[:10],
    }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print("=" * 72)
    print("Inverse Collatz Tree Analysis")
    print("=" * 72)

    # -----------------------------------------------------------------------
    # A. Forward Collatz depths (stopping times) for coverage analysis
    # -----------------------------------------------------------------------
    print("\n[A] Computing forward Collatz stopping times for odd n <= 10000 ...")
    fwd_depth = compute_forward_depths(limit=10000)
    # fwd_depth[n] = number of odd Syracuse steps from n to reach 1

    max_fwd = max(fwd_depth.values())
    print(f"    Max odd-step depth in [1, 10000]: {max_fwd}")
    print(f"    (This is equivalent to 'depth in inverse tree' by Collatz if conjecture holds)")

    # Coverage at each "depth" (stopping time threshold)
    print("\n--- Stopping-time distribution (forward Collatz, odd n <= 10000) ---")
    print(f"{'Depth<=':>8}  {'Count(<=1000)':>14}  {'Frac(<=1000)':>13}  {'Count(<=10000)':>15}  {'Frac(<=10000)':>14}")

    for thresh in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 20, 30, 50, 100, 200, max_fwd]:
        c1000  = sum(1 for n in range(1, 1001,  2) if fwd_depth.get(n, 9999) <= thresh)
        c10000 = sum(1 for n in range(1, 10001, 2) if fwd_depth.get(n, 9999) <= thresh)
        print(f"{thresh:>8}  {c1000:>14,}  {c1000/500:>13.6f}  {c10000:>15,}  {c10000/5000:>14.6f}")

    # Dead branches
    missing_fwd = sorted(n for n in range(1, 10001, 2) if fwd_depth.get(n) is None)
    print(f"\n    Odd n <= 10000 with no finite depth: {len(missing_fwd)}")
    if missing_fwd:
        print(f"    Examples: {missing_fwd[:10]}")
    else:
        print("    None — every odd integer <= 10000 reaches 1.")

    # -----------------------------------------------------------------------
    # B. Bounded inverse BFS (nodes <= 10^6, deep)
    # -----------------------------------------------------------------------
    BOUND = 1_000_000
    print(f"\n[B] Bounded inverse BFS: tracking odd nodes <= {BOUND:,} ...")
    bnd_depth = build_bounded_inverse_tree(bound=BOUND, max_depth=40)
    print(f"    Odd nodes <= {BOUND:,} reached: {len(bnd_depth):,} / {BOUND//2:,}  ({len(bnd_depth)/(BOUND//2)*100:.2f}%)")

    # Distribution of bounded depths
    max_bnd = max(bnd_depth.values()) if bnd_depth else 0
    print(f"    Max depth in bounded tree: {max_bnd}")

    bnd_by_depth = defaultdict(list)
    for n, d in bnd_depth.items():
        bnd_by_depth[d].append(n)

    print("\n--- Bounded inverse BFS: cumulative coverage of odd n <= N ---")
    print(f"{'Depth':>6}  {'#at depth':>10}  {'Cum.total':>11}  {'<=1000':>8}  {'Frac(1k)':>10}  {'<=10000':>9}  {'Frac(10k)':>11}")
    cumulative = 0
    cumulative_data = {}
    cum_1k = cum_10k = 0
    bnd_stats = {}
    for d in range(max_bnd + 1):
        nodes_d = bnd_by_depth.get(d, [])
        cnt = len(nodes_d)
        cumulative += cnt
        c1k  = sum(1 for n in nodes_d if n <= 1000)
        c10k = sum(1 for n in nodes_d if n <= 10000)
        cum_1k  += c1k
        cum_10k += c10k
        cumulative_data[d] = cumulative
        bnd_stats[d] = {"count": cnt, "cum": cumulative, "cum_1k": cum_1k, "cum_10k": cum_10k}
        print(f"{d:>6}  {cnt:>10,}  {cumulative:>11,}  {cum_1k:>8,}  {cum_1k/500:>10.6f}  {cum_10k:>9,}  {cum_10k/5000:>11.6f}")

    missing_bnd = sorted(n for n in range(1, 10001, 2) if n not in bnd_depth)
    print(f"\n    Odd n <= 10000 NOT in bounded inverse BFS: {len(missing_bnd)}")
    if missing_bnd:
        print(f"    First 20: {missing_bnd[:20]}")
    missing_bnd_1k = [n for n in missing_bnd if n <= 1000]
    print(f"    Missing <= 1000: {len(missing_bnd_1k)}, examples: {missing_bnd_1k[:10]}")

    # Cross-check: fwd_depth vs bounded_bnd_depth
    print("\n--- Cross-check: forward stopping time vs bounded inverse depth ---")
    compare = []
    for n in range(1, 1001, 2):
        fd = fwd_depth.get(n)
        bd = bnd_depth.get(n)
        if fd is not None and bd is not None:
            compare.append((n, fd, bd))
    if compare:
        diffs = [(n, fd, bd, abs(fd - bd)) for (n, fd, bd) in compare]
        max_diff = max(d for _, _, _, d in diffs)
        perfect = sum(1 for _, fd, bd, _ in diffs if fd == bd)
        print(f"    Samples (n<=1000): {len(compare)}")
        print(f"    fwd_depth == bnd_depth: {perfect}")
        print(f"    Max |fwd - bnd| = {max_diff}")
        if max_diff > 0:
            examples = [(n, fd, bd) for n, fd, bd, d in diffs if d == max_diff][:5]
            print(f"    Examples where they differ: {examples}")
        print("    (They should match if the Collatz graph is a tree rooted at 1)")

    # -----------------------------------------------------------------------
    # C. Full BFS to depth 8 (structure analysis)
    # -----------------------------------------------------------------------
    FULL_DEPTH = 8
    print(f"\n[C] Full inverse BFS to depth {FULL_DEPTH} (no size bound) ...")
    full_depth, full_by_depth = build_inverse_tree_to_depth(max_depth=FULL_DEPTH, max_nodes=5_000_000)
    print(f"    Total nodes at depth <= {FULL_DEPTH}: {len(full_depth):,}")
    print(f"    Actual max depth reached: {max(full_depth.values()) if full_depth else 0}")

    print("\n--- Full BFS: nodes per depth ---")
    full_cum = 0
    full_stats = {}
    for d in range(FULL_DEPTH + 1):
        nodes_d = full_by_depth.get(d, [])
        full_cum += len(nodes_d)
        full_stats[d] = {"count": len(nodes_d), "cum": full_cum}
        sample = sorted(nodes_d)[:5]
        print(f"  depth {d:2d}: {len(nodes_d):>12,} nodes  (cum {full_cum:>12,})  sample={sample}")

    # Mod-13 distribution in full BFS
    print(f"\n--- Mod-13 distribution (full BFS, depths 0..{FULL_DEPTH}) ---")
    mod13_full = {}
    for d in range(FULL_DEPTH + 1):
        nodes_d = full_by_depth.get(d, [])
        counts = defaultdict(int)
        for n in nodes_d:
            counts[n % 13] += 1
        mod13_full[d] = dict(counts)

    print("Depth  " + "  ".join(f"r={r:>2}" for r in range(13)))
    for d in range(FULL_DEPTH + 1):
        dist = mod13_full.get(d, {})
        row = "  ".join(f"{dist.get(r, 0):>6}" for r in range(13))
        total = sum(dist.values())
        print(f"  {d:3d}  {row}  total={total:,}")

    # Uniformity test at last full depth
    d_last = FULL_DEPTH
    dist_last = mod13_full.get(d_last, {})
    total_last = sum(dist_last.values())
    if total_last > 0:
        expected = total_last / 13
        chi2 = sum((dist_last.get(r, 0) - expected) ** 2 / expected for r in range(13))
        print(f"\n  Depth-{d_last} chi2 for mod-13 uniformity: {chi2:.2f}  (expected ~12 if uniform, >21 suspicious)")
        uniform = chi2 < 21
        print(f"  Distribution is {'UNIFORM' if uniform else 'NON-UNIFORM / has breathing pattern'}")

    # Mod-104 unsafe residues in full BFS
    print(f"\n--- Unsafe residues mod 104: first appearance depth (full BFS up to depth {FULL_DEPTH}) ---")
    unsafe_first = {}
    unsafe_count = defaultdict(int)
    for r in UNSAFE_RESIDUES_104:
        unsafe_first[r] = None
    for d in range(FULL_DEPTH + 1):
        for n in full_by_depth.get(d, []):
            r = n % 104
            if r in unsafe_first:
                if unsafe_first[r] is None:
                    unsafe_first[r] = d
                unsafe_count[r] += 1

    print(f"{'Residue':>8}  {'First depth':>12}  {'Count in tree':>14}  Category")
    for r in UNSAFE_RESIDUES_104:
        cat = "HIGH-DISC" if r in HIGH_DISC else ("LOW-DISC" if r in LOW_DISC else "other")
        print(f"{r:>8}  {str(unsafe_first[r]):>12}  {unsafe_count[r]:>14,}  {cat}")

    high_first = [unsafe_first[r] for r in UNSAFE_RESIDUES_104 if r in HIGH_DISC and unsafe_first[r] is not None]
    low_first  = [unsafe_first[r] for r in UNSAFE_RESIDUES_104 if r in LOW_DISC  and unsafe_first[r] is not None]
    print(f"\n  High-discrepancy (85,21,53) first depths: {high_first}")
    print(f"  Low-discrepancy        first depths:      {low_first}")
    if high_first and low_first:
        avg_h = sum(high_first) / len(high_first)
        avg_l = sum(low_first)  / len(low_first)
        print(f"  Avg first depth: HIGH={avg_h:.2f}, LOW={avg_l:.2f}")
        if avg_h > avg_l:
            print("  -> HIGH-DISC residues appear LATER in inverse tree (confirms hypothesis)")
        elif avg_h < avg_l:
            print("  -> HIGH-DISC residues appear EARLIER (contradicts hypothesis)")
        else:
            print("  -> No systematic difference in first depth")

    # -----------------------------------------------------------------------
    # D. Unsafe residue analysis using forward stopping times
    # -----------------------------------------------------------------------
    print("\n--- Unsafe residues: forward stopping times (odd n <= 10000) ---")
    unsafe_fwd = defaultdict(list)
    for n in range(1, 10001, 2):
        r = n % 104
        if r in set(UNSAFE_RESIDUES_104):
            unsafe_fwd[r].append(fwd_depth.get(n, None))

    print(f"{'Residue':>8}  {'Count':>7}  {'Min depth':>10}  {'Max depth':>10}  {'Avg depth':>10}  Category")
    unsafe_avg = {}
    for r in UNSAFE_RESIDUES_104:
        vals = [v for v in unsafe_fwd[r] if v is not None]
        cat = "HIGH-DISC" if r in HIGH_DISC else ("LOW-DISC" if r in LOW_DISC else "other")
        if vals:
            avg = sum(vals) / len(vals)
            unsafe_avg[r] = avg
            print(f"{r:>8}  {len(vals):>7,}  {min(vals):>10}  {max(vals):>10}  {avg:>10.2f}  {cat}")
        else:
            print(f"{r:>8}  {0:>7}  {'N/A':>10}  {'N/A':>10}  {'N/A':>10}  {cat}")

    high_avgs = [unsafe_avg[r] for r in UNSAFE_RESIDUES_104 if r in HIGH_DISC and r in unsafe_avg]
    low_avgs  = [unsafe_avg[r] for r in UNSAFE_RESIDUES_104 if r in LOW_DISC  and r in unsafe_avg]
    if high_avgs and low_avgs:
        print(f"\n  Avg stopping time HIGH-DISC: {sum(high_avgs)/len(high_avgs):.2f}")
        print(f"  Avg stopping time LOW-DISC:  {sum(low_avgs)/len(low_avgs):.2f}")

    # -----------------------------------------------------------------------
    # E. Tower compatibility
    # -----------------------------------------------------------------------
    print("\n--- Tower compatibility mod 208 -> mod 104 ---")
    compat = tower_compatibility(max_depth=8)
    print(f"  Residues in mod-104 inverse tree (depth<=8): {compat['mod104_residues']}")
    print(f"  Residues in mod-208 inverse tree (depth<=8): {compat['mod208_residues']}")
    print(f"  Violations: {compat['violations']}")
    if compat["violation_examples"]:
        print("  Violation examples (r208, depth208, r104, reason):")
        for ex in compat["violation_examples"][:8]:
            print(f"    {ex}")
    else:
        print("  -> Tower compatibility holds perfectly.")

    # -----------------------------------------------------------------------
    # F. Key findings summary
    # -----------------------------------------------------------------------
    print("\n" + "=" * 72)
    print("KEY FINDINGS")
    print("=" * 72)

    # Finding 1: coverage
    d8_cum_1k = bnd_stats.get(8, {}).get("cum_1k", 0)
    d8_cum_10k = bnd_stats.get(8, {}).get("cum_10k", 0)
    print(f"\n1. DENSITY APPROACHING 1:")
    print(f"   By bounded inverse depth 8, coverage:")
    print(f"     odd n <= 1000:  {d8_cum_1k}/500  = {d8_cum_1k/500:.4f}")
    print(f"     odd n <= 10000: {d8_cum_10k}/5000 = {d8_cum_10k/5000:.4f}")
    print(f"   Full bounded BFS covers {len(bnd_depth)/500000*100:.2f}% of odd n <= 1,000,000")
    print(f"   (Branching factor ~20/level => covers all integers quickly if Collatz holds)")

    print(f"\n2. BREATHING STRUCTURE mod 13 (full BFS depth {FULL_DEPTH}):")
    for d in (0, 2, 4, 6, 8):
        if d > FULL_DEPTH:
            continue
        dist = mod13_full.get(d, {})
        total = sum(dist.values())
        if total == 0:
            continue
        vals = [dist.get(r, 0) for r in range(13)]
        ratio = max(vals) / (min(v for v in vals if v > 0)) if any(v > 0 for v in vals) else None
        ratio_str = f"{ratio:.2f}" if ratio is not None else "N/A"
        print(f"   depth {d}: total={total:,}, max/min ratio={ratio_str}")

    print(f"\n3. UNSAFE RESIDUES appearing:")
    for r in UNSAFE_RESIDUES_104:
        fd = unsafe_first[r]
        cat = "HIGH-DISC" if r in HIGH_DISC else ("LOW-DISC" if r in LOW_DISC else "other")
        print(f"   mod104={r:3d} ({cat}): first at depth {fd}")

    print(f"\n4. DEAD BRANCHES (odd n <= 10000 not in bounded inverse tree):")
    print(f"   {len(missing_bnd)} integers not yet reached (bounded BFS, max_depth=40, bound=10^6)")
    if missing_bnd:
        print(f"   First 10: {missing_bnd[:10]}")
        print(f"   These are multiples of 3 or nodes needing a very long chain.")
        # Check: are missing ones all multiples of 3?
        mult3 = [n for n in missing_bnd if n % 3 == 0]
        non_mult3 = [n for n in missing_bnd if n % 3 != 0]
        print(f"   Of missing: {len(mult3)} are multiples of 3, {len(non_mult3)} are not.")
        if non_mult3:
            print(f"   Non-multiples of 3 that are missing: {non_mult3[:10]}")
    else:
        print("   None! All odd integers <= 10000 are reachable.")

    # -----------------------------------------------------------------------
    # Save JSON
    # -----------------------------------------------------------------------
    output = {
        "method_note": (
            "Branching factor ~20/level makes full BFS infeasible past depth 8. "
            "We use: (A) forward stopping times for coverage; "
            "(B) bounded inverse BFS (nodes<=10^6); "
            "(C) full inverse BFS to depth 8."
        ),
        "forward_stopping_times": {
            "max_depth_le_10000": max_fwd,
            "coverage_thresholds": {
                str(t): {
                    "le1000":  sum(1 for n in range(1, 1001,  2) if fwd_depth.get(n, 9999) <= t),
                    "le10000": sum(1 for n in range(1, 10001, 2) if fwd_depth.get(n, 9999) <= t),
                }
                for t in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 20, 30, 50, 100]
            },
        },
        "bounded_inverse_bfs": {
            "bound": BOUND,
            "nodes_reached": len(bnd_depth),
            "total_odd_in_bound": BOUND // 2,
            "max_depth": max_bnd,
            "coverage_fraction": len(bnd_depth) / (BOUND // 2),
            "missing_le_10000": missing_bnd,
            "missing_le_1000": missing_bnd_1k,
            "by_depth": {str(d): bnd_stats.get(d, {}) for d in range(max_bnd + 1)},
        },
        "full_bfs_depth_8": {
            "total_nodes": len(full_depth),
            "by_depth": {str(d): full_stats.get(d, {}) for d in range(FULL_DEPTH + 1)},
            "mod13_distribution": {
                str(d): {str(r): mod13_full.get(d, {}).get(r, 0) for r in range(13)}
                for d in range(FULL_DEPTH + 1)
            },
        },
        "unsafe_residues_mod104": {
            str(r): {
                "first_depth_in_full_bfs": unsafe_first[r],
                "count_in_full_bfs": unsafe_count[r],
                "avg_forward_stopping_time": round(unsafe_avg.get(r, 0), 4),
                "category": ("HIGH-DISC" if r in HIGH_DISC else ("LOW-DISC" if r in LOW_DISC else "other")),
            }
            for r in UNSAFE_RESIDUES_104
        },
        "tower_compatibility": compat,
    }

    out_path = "/Users/dcharb/Documents/collatz/UFRF0-Lean4-Explore-v2/exploration/q2_results.json"
    with open(out_path, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\nResults saved to {out_path}")
    print("\nDone.")


if __name__ == "__main__":
    main()
