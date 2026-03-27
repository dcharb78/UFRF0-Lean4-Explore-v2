#!/usr/bin/env python3
"""
Collatz Nested Scale Analysis: Syracuse transition graph on ZMod(169 * 2^k)
vs ZMod(13 * 2^k).  169 = 13^2 tests whether the nested UFRF scale gives
tighter bounds.

Exact arithmetic throughout; fractions.Fraction for drift.
"""

import json
import sys
from collections import defaultdict
from fractions import Fraction

# ---------------------------------------------------------------------------
# Constants and utilities
# ---------------------------------------------------------------------------

LOG2_3 = Fraction(892254565955501, 562949953421312)


def v2(n):
    """2-adic valuation of n > 0."""
    return (n & -n).bit_length() - 1


def drift_per_step(v2_val):
    return LOG2_3 - v2_val


# ---------------------------------------------------------------------------
# Graph construction
# ---------------------------------------------------------------------------

def build_transition_graph(modulus):
    """
    Build the Syracuse transition graph on ZMod(modulus).
    Returns dict {r: (v2_val, image)} for each odd r in range(modulus).
    """
    transitions = {}
    for r in range(1, modulus, 2):
        val = 3 * r + 1
        vv = v2(val)
        image = (val >> vv) % modulus
        transitions[r] = (vv, image)
    return transitions


# ---------------------------------------------------------------------------
# Graph analysis helpers
# ---------------------------------------------------------------------------

def find_connected_components(transitions):
    """Count connected components (treating graph as undirected)."""
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


def find_cycles(transitions):
    """Find all cycles in the functional graph (each node has out-degree 1)."""
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
            cycle_start_idx = path.index(node)
            cycles.append(path[cycle_start_idx:])
        visited.update(path)
    return cycles


def find_max_bad_streak(transitions):
    """
    BFS/follow from each odd residue: count consecutive v2=1 steps until v2>=2.
    Returns the maximum streak length found.
    """
    max_streak = 0
    for start in transitions:
        length = 0
        node = start
        seen = set()
        while node in transitions:
            vv, image = transitions[node]
            if vv != 1:
                break
            if node in seen:
                # cycle of all v2=1 steps; truncate at seen length
                break
            seen.add(node)
            length += 1
            node = image
        if length > max_streak:
            max_streak = length
    return max_streak


def window_drift_dp(transitions, max_window=200):
    """
    DP to find maximum cumulative drift over W steps.
    dp[r] = max cumulative drift starting at r over remaining steps.
    Returns (convergence_window, dp_results_dict).
    convergence_window is the first W where max drift < 0 (or None).
    """
    odd_residues = list(transitions.keys())
    dp_prev = {r: Fraction(0) for r in odd_residues}
    convergence_w = None

    for w in range(1, max_window + 1):
        dp_curr = {}
        for r in odd_residues:
            vv, image = transitions[r]
            d = drift_per_step(vv)
            succ_val = dp_prev.get(image, Fraction(0))
            dp_curr[r] = d + succ_val

        max_drift = max(dp_curr.values())
        if convergence_w is None and max_drift < 0:
            convergence_w = w
            break
        dp_prev = dp_curr

    return convergence_w


# ---------------------------------------------------------------------------
# Main analysis
# ---------------------------------------------------------------------------

def analyse_k(k, base):
    """
    Analyse Syracuse transition graph on ZMod(base * 2^k).
    Returns dict of results.
    """
    modulus = base * (1 << k)
    transitions = build_transition_graph(modulus)
    odd_count = len(transitions)

    components = find_connected_components(transitions)
    cycles = find_cycles(transitions)
    max_bad = find_max_bad_streak(transitions)
    conv_w = window_drift_dp(transitions, max_window=200)

    return {
        "modulus": modulus,
        "odd_count": odd_count,
        "components": components,
        "cycles": len(cycles),
        "max_bad_streak": max_bad,
        "convergence_window": conv_w,
    }


def main():
    print("Collatz Nested Scale Analysis: ZMod(169*2^k) vs ZMod(13*2^k)")
    print(f"LOG2_3 = {LOG2_3} = {float(LOG2_3):.15f}")
    print()

    # Load existing 13*2^k results
    results_path = "/Users/dcharb/Documents/collatz/UFRF0-Lean4-Explore-v2/analysis/results.json"
    with open(results_path) as f:
        existing = json.load(f)

    part3 = existing["part3"]
    results_13 = {}
    for k_str in sorted(part3.keys(), key=int):
        k = int(k_str)
        if 3 <= k <= 7:
            results_13[k] = {
                "modulus": part3[k_str]["modulus"],
                "max_bad_streak": part3[k_str]["max_bad_streak"],
                "convergence_window": part3[k_str]["convergence_window"],
            }

    print("Computing ZMod(169*2^k) results...")
    results_169 = {}
    nested_output = {}

    for k in range(3, 8):
        print(f"  k={k} (modulus={169 * (1 << k)})...", end=" ", flush=True)
        res = analyse_k(k, 169)
        results_169[k] = res
        nested_output[f"k={k}"] = res
        print(f"done. W={res['convergence_window']}, bad={res['max_bad_streak']}")

    # Save results
    out_path = "/Users/dcharb/Documents/collatz/UFRF0-Lean4-Explore-v2/analysis/nested_scale_results.json"
    with open(out_path, "w") as f:
        json.dump(nested_output, f, indent=2)
    print(f"\nResults saved to {out_path}")

    # Comparison table
    print()
    print("Comparison Table: ZMod(13*2^k) vs ZMod(169*2^k)")
    print()
    header = f"{'k':>3s} | {'13×2^k':>10s} | {'W(13)':>7s} | {'bad(13)':>7s} | {'169×2^k':>10s} | {'W(169)':>7s} | {'bad(169)':>8s} | {'W ratio':>8s}"
    print(header)
    print("-" * len(header))

    for k in range(3, 8):
        r13 = results_13.get(k)
        r169 = results_169[k]
        if r13 is None:
            continue
        w13 = r13["convergence_window"]
        w169 = r169["convergence_window"]
        b13 = r13["max_bad_streak"]
        b169 = r169["max_bad_streak"]
        m13 = r13["modulus"]
        m169 = r169["modulus"]

        w13_str = str(w13) if w13 is not None else "None"
        w169_str = str(w169) if w169 is not None else "None"

        if w13 is not None and w169 is not None:
            ratio_str = f"{w169 / w13:.3f}"
        else:
            ratio_str = "N/A"

        print(f"{k:>3d} | {m13:>10d} | {w13_str:>7s} | {b13:>7d} | {m169:>10d} | {w169_str:>7s} | {b169:>8d} | {ratio_str:>8s}")

    # Summary observations
    print()
    print("Key Observations:")
    for k in range(3, 8):
        r13 = results_13.get(k)
        r169 = results_169[k]
        if r13 is None:
            continue
        w13 = r13["convergence_window"]
        w169 = r169["convergence_window"]
        b13 = r13["max_bad_streak"]
        b169 = r169["max_bad_streak"]

        if w13 is not None and w169 is not None:
            tighter = "TIGHTER" if w169 < w13 else ("SAME" if w169 == w13 else "LOOSER")
            print(f"  k={k}: W(169)={w169}, W(13)={w13} => {tighter}; "
                  f"bad(169)={b169}, bad(13)={b13}")
        else:
            print(f"  k={k}: W(13)={w13}, W(169)={w169} (one or both not converged by W=200)")


if __name__ == "__main__":
    main()
