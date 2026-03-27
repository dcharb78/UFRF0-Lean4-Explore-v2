#!/usr/bin/env python3
"""
Collatz Orbit Analysis via Syracuse Map on ZMod structures.

Performs:
  Part 1: Syracuse map on ZMod 13
  Part 2: Joint analysis on ZMod(13 * 2^k)
  Part 3: Bad streak analysis and window-based convergence search

Uses exact integer arithmetic throughout; fractions.Fraction for drift.
"""

import json
import sys
from collections import defaultdict
from fractions import Fraction
from math import gcd, log2


# ---------------------------------------------------------------------------
# Utility helpers
# ---------------------------------------------------------------------------

def v2(n):
    """Return the 2-adic valuation of n (number of trailing zeros)."""
    if n == 0:
        return -1  # convention
    return (n & -n).bit_length() - 1


def mod_inverse(a, m):
    """Return modular inverse of a mod m using extended Euclidean algorithm."""
    g, x, _ = extended_gcd(a, m)
    if g != 1:
        return None
    return x % m


def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x1, y1 = extended_gcd(b % a, a)
    return g, y1 - (b // a) * x1, x1


# Exact log2(3) as a Fraction -- use a high-precision rational approximation
# log2(3) = 1.58496250072115618145373894394...
# This is the best rational approximation at double precision via
# Fraction(log2(3)).limit_denominator(10**15).
LOG2_3 = Fraction(892254565955501, 562949953421312)


def drift_per_step(v2_val):
    """Return log2(3) - v2_val as a Fraction."""
    return LOG2_3 - v2_val


# ---------------------------------------------------------------------------
# Part 1: Syracuse Map on ZMod 13
# ---------------------------------------------------------------------------

def part1_syracuse_zmod13():
    """Analyse the Syracuse map on ZMod 13 for odd residue classes."""
    print("=" * 72)
    print("PART 1: Syracuse Map on ZMod 13")
    print("=" * 72)

    m = 13
    odd_residues = [r for r in range(1, m, 2)]  # {1,3,5,7,9,11}

    # Precompute inverses of 2^k mod 13 for k = 1..12 (period divides 12)
    inv_table = {}
    for k in range(1, 13):
        inv = mod_inverse(pow(2, k, m), m)
        inv_table[k] = inv

    print(f"\nOdd residues mod {m}: {odd_residues}")
    print(f"\nModular inverses of 2^k mod {m}:")
    for k in range(1, 13):
        print(f"  2^{k} = {pow(2, k, m):>4d} mod {m},  inverse = {inv_table[k]}")

    results = {}
    print(f"\nSyracuse images for each odd residue and v2 value:")
    print(f"{'r':>4s} | {'3r+1':>6s} | {'v2':>3s} | {'image mod 13':>12s}")
    print("-" * 40)

    for r in odd_residues:
        val = 3 * r + 1
        results[r] = {}
        for k in range(1, 13):
            image = (inv_table[k] * val) % m
            results[r][k] = image

        # Determine which v2 values are actually achievable
        # We need to find actual integers n = r mod 13 (odd) and check v2(3n+1)
        # Sample n = r, r+26, r+52, ... (odd, = r mod 13)
        achieved_v2 = set()
        for trial in range(100):
            n = r + m * trial * 2  # keep same residue mod 13, try to stay odd
            if n % 2 == 0:
                n += m
            if n % m != r:
                continue
            if n % 2 == 0:
                continue
            vv = v2(3 * n + 1)
            achieved_v2.add(vv)

        for k in sorted(achieved_v2):
            marker = "*" if k in achieved_v2 else " "
            print(f"{r:>4d} | {val:>6d} | {k:>3d} | {results[r][k]:>12d}  {marker}")

    # Also print the full table for all v2 values
    print(f"\nFull table (all v2 from 1..12):")
    for r in odd_residues:
        val = 3 * r + 1
        images = [results[r][k] for k in range(1, 13)]
        print(f"  r={r:>2d}: 3r+1={val:>3d}, images = {images}")

    return results


# ---------------------------------------------------------------------------
# Part 2: Joint Analysis on ZMod(13 * 2^k)
# ---------------------------------------------------------------------------

def build_transition_graph(k_exp):
    """
    Build the Syracuse transition graph on ZMod(13 * 2^k_exp).
    Returns (modulus, transitions) where transitions is a dict:
      r -> (v2_val, image)
    for each odd residue r.
    """
    modulus = 13 * (1 << k_exp)
    transitions = {}

    for r in range(modulus):
        if r % 2 == 0:
            continue  # skip even residues
        val = 3 * r + 1
        vv = v2(val)
        image = (val >> vv) % modulus
        transitions[r] = (vv, image)

    return modulus, transitions


def find_cycles(transitions):
    """Find all cycles in the transition graph. Returns list of cycles."""
    visited = set()
    cycles = []

    for start in transitions:
        if start in visited:
            continue
        path = []
        path_set = set()
        node = start
        while node not in visited and node not in path_set:
            path.append(node)
            path_set.add(node)
            _, image = transitions[node]
            node = image

        if node in path_set:
            # Found a cycle
            cycle_start_idx = path.index(node)
            cycle = path[cycle_start_idx:]
            cycles.append(cycle)

        visited.update(path)

    return cycles


def find_connected_components(transitions):
    """Find connected components treating the graph as undirected."""
    adj = defaultdict(set)
    all_nodes = set(transitions.keys())

    for r, (_, image) in transitions.items():
        adj[r].add(image)
        adj[image].add(r)

    visited = set()
    components = 0

    for node in all_nodes:
        if node in visited:
            continue
        components += 1
        stack = [node]
        while stack:
            n = stack.pop()
            if n in visited:
                continue
            visited.add(n)
            for nb in adj[n]:
                if nb not in visited and nb in all_nodes:
                    stack.append(nb)

    return components


def part2_joint_analysis():
    """Joint analysis on ZMod(13 * 2^k) for k in {3..8}."""
    print("\n" + "=" * 72)
    print("PART 2: Joint Analysis on ZMod(13 * 2^k)")
    print("=" * 72)

    all_results = {}

    for k_exp in range(3, 11):
        modulus, transitions = build_transition_graph(k_exp)
        num_odd = len(transitions)

        # v2 distribution
        v2_dist = defaultdict(int)
        for r, (vv, _) in transitions.items():
            v2_dist[vv] += 1

        # Connected components
        num_components = find_connected_components(transitions)

        # Cycles
        cycles = find_cycles(transitions)

        print(f"\n--- k = {k_exp}, modulus = {modulus} ---")
        print(f"  Number of odd residues: {num_odd}")
        print(f"  v2 distribution:")
        for vv in sorted(v2_dist.keys()):
            pct = 100.0 * v2_dist[vv] / num_odd
            print(f"    v2 = {vv}: {v2_dist[vv]:>6d} residues ({pct:5.1f}%)")
        print(f"  Connected components (undirected): {num_components}")
        print(f"  Number of cycles: {len(cycles)}")
        for i, cycle in enumerate(cycles):
            v2s = [transitions[r][0] for r in cycle]
            drift_sum = sum(drift_per_step(vv) for vv in v2s)
            if len(cycle) <= 20:
                print(f"    Cycle {i}: length={len(cycle)}, v2s={v2s}, "
                      f"total drift={float(drift_sum):.6f}, residues={cycle}")
            else:
                print(f"    Cycle {i}: length={len(cycle)}, "
                      f"total drift={float(drift_sum):.6f}, "
                      f"v2 sum={sum(v2s)}, residues=[{cycle[0]},...,{cycle[-1]}]")

        all_results[k_exp] = {
            "modulus": modulus,
            "num_odd": num_odd,
            "v2_distribution": {str(k): v for k, v in sorted(v2_dist.items())},
            "num_components": num_components,
            "num_cycles": len(cycles),
            "cycles": [
                {
                    "length": len(c),
                    "residues": c if len(c) <= 50 else c[:5] + ["..."] + c[-5:],
                    "v2_values": [transitions[r][0] for r in c],
                    "total_drift": float(sum(
                        drift_per_step(transitions[r][0]) for r in c
                    )),
                }
                for c in cycles
            ],
        }

    return all_results


# ---------------------------------------------------------------------------
# Part 3: Bad Streak Analysis
# ---------------------------------------------------------------------------

def find_bad_streaks(transitions):
    """
    Find all maximal bad streaks (consecutive v2=1 steps).
    Returns list of (start_residue, streak_length, v2_after).
    """
    streaks = []
    for start in transitions:
        vv_start = transitions[start][0]
        if vv_start != 1:
            continue
        # Follow chain while v2 == 1
        length = 0
        node = start
        visited_in_streak = set()
        while node in transitions and transitions[node][0] == 1:
            if node in visited_in_streak:
                # We hit a cycle of all v2=1 -- record and break
                length = len(visited_in_streak)
                streaks.append((start, length, None))
                break
            visited_in_streak.add(node)
            length += 1
            _, node = transitions[node]
        else:
            if length > 0:
                v2_after = transitions[node][0] if node in transitions else None
                streaks.append((start, length, v2_after))

    return streaks


def window_drift_analysis_dp(transitions, max_window):
    """
    For each window size W from 1..max_window, find the maximum cumulative
    drift over ALL W-step paths in the transition graph.

    Uses DP where we track maximum drift achievable *starting from* each
    residue in exactly W steps.

    dp[w][r] = max cumulative drift over any w-step path starting at r.
    Recurrence: dp[w][r] = drift(r) + dp[w-1][image(r)]
      where drift(r) = log2(3) - v2(r) and image(r) is the Syracuse successor.

    Only residues in `transitions` (odd residues) are valid starting points.

    Returns dict: W -> (max_drift_fraction, max_drift_float)
    """
    odd_residues = list(transitions.keys())
    odd_set = set(odd_residues)
    results = {}

    # dp_prev[r] = max cumulative drift starting from r in 0 more steps = 0
    dp_prev = {r: Fraction(0) for r in odd_residues}

    for w in range(1, max_window + 1):
        dp_curr = {}
        for r in odd_residues:
            vv, image = transitions[r]
            d = drift_per_step(vv)
            if image in dp_prev:
                dp_curr[r] = d + dp_prev[image]
            else:
                # image is not an odd residue in our table; this path ends
                # (shouldn't normally happen for well-formed Syracuse on ZMod)
                # Just count this single step's drift
                dp_curr[r] = d

        max_drift = max(dp_curr.values())
        results[w] = (max_drift, float(max_drift))
        dp_prev = dp_curr

        if w % 10 == 0 or w == max_window:
            print(f"    W={w:>3d}: max drift = {float(max_drift):+.6f}")

    return results


def part3_bad_streak_analysis():
    """Bad streak analysis and window-based convergence search."""
    print("\n" + "=" * 72)
    print("PART 3: Bad Streak Analysis & Window Convergence Search")
    print("=" * 72)

    # Determine max window per k
    max_windows = {3: 50, 4: 50, 5: 50, 6: 50, 7: 200, 8: 200, 9: 200, 10: 200}

    all_results = {}

    for k_exp in range(3, 11):
        modulus, transitions = build_transition_graph(k_exp)
        max_w = max_windows[k_exp]

        print(f"\n--- k = {k_exp}, modulus = {modulus} ---")

        # Bad streak analysis
        streaks = find_bad_streaks(transitions)
        if streaks:
            max_streak = max(streaks, key=lambda x: x[1])
            streak_lengths = [s[1] for s in streaks]
            max_len = max(streak_lengths)

            # Distribution of streak lengths
            len_dist = defaultdict(int)
            for _, slen, _ in streaks:
                len_dist[slen] += 1

            print(f"  Bad streak statistics (consecutive v2=1):")
            print(f"    Total starting points with v2=1: {len(streaks)}")
            print(f"    Maximum bad streak length: {max_len}")
            print(f"    Streak length distribution:")
            for sl in sorted(len_dist.keys()):
                print(f"      length {sl}: {len_dist[sl]} occurrences")

            # Worst case analysis
            print(f"\n  Worst-case bad streak analysis:")
            print(f"    Worst streak: start={max_streak[0]}, "
                  f"length={max_streak[1]}, v2_after={max_streak[2]}")
            L = max_streak[1]
            v2_after = max_streak[2]
            bad_drift = L * drift_per_step(1)
            print(f"    Cumulative drift during streak: "
                  f"{float(bad_drift):+.6f} "
                  f"(= {L} * {float(drift_per_step(1)):.6f})")
            if v2_after is not None and v2_after >= 2:
                recovery = drift_per_step(v2_after)
                net = bad_drift + recovery
                print(f"    Recovery step (v2={v2_after}): "
                      f"drift = {float(recovery):+.6f}")
                print(f"    Net drift (streak + recovery): "
                      f"{float(net):+.6f}")
                if net < 0:
                    print(f"    ==> Recovery COMPENSATES for bad streak!")
                else:
                    print(f"    ==> Recovery does NOT fully compensate.")
            elif v2_after is None:
                print(f"    (streak ends in a v2=1 cycle -- no recovery)")
        else:
            max_len = 0
            print(f"  No bad streaks found (no residue has v2=1).")

        # Window drift analysis using DP
        print(f"\n  Window drift analysis (DP, max W={max_w}):")
        window_results = window_drift_analysis_dp(transitions, max_w)

        # Find convergence window
        convergence_w = None
        for w in range(1, max_w + 1):
            if window_results[w][0] < 0:
                convergence_w = w
                break

        if convergence_w is not None:
            print(f"\n  ** CONVERGENCE WINDOW FOUND at W={convergence_w}: "
                  f"worst-case drift = {window_results[convergence_w][1]:+.6f} < 0 **")
        else:
            print(f"\n  No convergence window found up to W={max_w}.")
            # Show trend
            print(f"  Drift trend (last 5 windows):")
            for w in range(max(1, max_w - 4), max_w + 1):
                d = window_results[w][1]
                print(f"    W={w}: {d:+.6f}")

        all_results[k_exp] = {
            "modulus": 13 * (1 << k_exp),
            "max_bad_streak": max_len,
            "num_streak_starts": len(streaks) if streaks else 0,
            "convergence_window": convergence_w,
            "window_drifts": {
                str(w): window_results[w][1] for w in sorted(window_results)
            },
        }

    return all_results


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print("Collatz Orbit Analysis via Syracuse Map")
    print("Using exact integer arithmetic + Fraction for drift")
    print(f"LOG2_3 approximation: {LOG2_3} = {float(LOG2_3):.15f}")
    print(f"Actual log2(3):                 {log2(3):.15f}")
    print()

    results = {}

    # Part 1
    p1 = part1_syracuse_zmod13()
    results["part1"] = {
        "description": "Syracuse map on ZMod 13",
        "odd_residues": [1, 3, 5, 7, 9, 11],
        "images": {
            str(r): {str(k): p1[r][k] for k in range(1, 13)}
            for r in [1, 3, 5, 7, 9, 11]
        },
    }

    # Part 2
    p2 = part2_joint_analysis()
    results["part2"] = p2

    # Part 3
    p3 = part3_bad_streak_analysis()
    results["part3"] = p3

    # Summary
    print("\n" + "=" * 72)
    print("SUMMARY")
    print("=" * 72)

    print("\nPart 2 summary (cycles per k):")
    for k_exp in sorted(p2.keys()):
        info = p2[k_exp]
        print(f"  k={k_exp}: modulus={info['modulus']}, "
              f"odd={info['num_odd']}, "
              f"components={info['num_components']}, "
              f"cycles={info['num_cycles']}")

    print("\nPart 3 summary (convergence windows):")
    for k_exp in sorted(p3.keys()):
        info = p3[k_exp]
        cw = info["convergence_window"]
        ms = info["max_bad_streak"]
        if cw:
            drift_at_cw = info["window_drifts"][str(cw)]
            print(f"  k={k_exp}: max_bad_streak={ms}, "
                  f"convergence at W={cw} (drift={drift_at_cw:+.6f})")
        else:
            # Show max window drift
            max_w = max(int(w) for w in info["window_drifts"])
            drift_at_max = info["window_drifts"][str(max_w)]
            print(f"  k={k_exp}: max_bad_streak={ms}, "
                  f"NO convergence up to W={max_w} "
                  f"(drift@W={max_w}: {drift_at_max:+.6f})")

    # Save JSON
    output_path = "/Users/dcharb/Documents/collatz/UFRF0-Lean4-Explore-v2/analysis/results.json"
    with open(output_path, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResults saved to {output_path}")


if __name__ == "__main__":
    main()
