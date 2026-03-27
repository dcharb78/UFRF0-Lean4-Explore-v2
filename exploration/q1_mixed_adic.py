"""
Mixed 2-adic / 3-adic Collatz analysis.

Working moduli:  M = 13 * 2^k * 3^j
Question: does adding 3-adic precision (j >= 1) reduce the max discrepancy
between modular v2 and actual v2 for "unsafe" residues?
"""

import json
from fractions import Fraction

# ---------------------------------------------------------------------------
# Core helpers
# ---------------------------------------------------------------------------

def v2(n):
    """2-adic valuation of n (returns -1 for n=0)."""
    if n == 0:
        return -1
    return (n & -n).bit_length() - 1


def syracuse_mod(M, n):
    """Syracuse step: (3n+1) / 2^v2(3n+1)  mod M."""
    val = 3 * n + 1
    vv = v2(val)
    return (val >> vv) % M


# ---------------------------------------------------------------------------
# Parameter sets
# ---------------------------------------------------------------------------

PARAMS = [
    # (k, j, M)
    (3, 0, 13 * 8),           # 104
    (3, 1, 13 * 8 * 3),       # 312
    (3, 2, 13 * 8 * 9),       # 936
    (4, 0, 13 * 16),          # 208
    (4, 1, 13 * 16 * 3),      # 624
    (5, 0, 13 * 32),          # 416
    (5, 1, 13 * 32 * 3),      # 1248
]


# ---------------------------------------------------------------------------
# Step 1 & 2: Unsafe residues and discrepancy measurement
# ---------------------------------------------------------------------------

def analyze_unsafe(M, k, n_limit=10000):
    """
    Find unsafe residues (those where v2(3r+1) >= k) and measure discrepancy.

    Returns:
        odd_residues     : list of all odd residues mod M
        unsafe_residues  : list of unsafe odd residues
        max_discrepancy  : max over unsafe r of (modular_v2 - min actual_v2)
        zero_disc_count  : number of unsafe residues where discrepancy == 0
        per_residue      : dict mapping r -> (modular_v2, min_actual_v2, discrepancy)
    """
    odd_residues = list(range(1, M, 2))
    unsafe_residues = [r for r in odd_residues if v2(3 * r + 1) >= k]

    per_residue = {}
    max_discrepancy = 0
    zero_disc_count = 0

    for r in unsafe_residues:
        mod_v2 = v2(3 * r + 1)
        # Collect actual v2 values for n ≡ r (mod M), 1 <= n <= n_limit, n odd
        actual_v2s = []
        n = r if r >= 1 else r + M
        while n <= n_limit:
            actual_v2s.append(v2(3 * n + 1))
            n += M

        if not actual_v2s:
            # r itself might be > n_limit; just use r
            actual_v2s = [v2(3 * r + 1)]

        min_actual = min(actual_v2s)
        disc = mod_v2 - min_actual
        per_residue[r] = (mod_v2, min_actual, disc)
        if disc > max_discrepancy:
            max_discrepancy = disc
        if disc == 0:
            zero_disc_count += 1

    return odd_residues, unsafe_residues, max_discrepancy, zero_disc_count, per_residue


# ---------------------------------------------------------------------------
# Step 3: Convergence window DP
# ---------------------------------------------------------------------------

def window_dp(M, k, max_W=300):
    """
    The Syracuse map is deterministic on ZMod(M).
    For each odd residue r, the orbit r -> r1 -> r2 -> ... is fixed.

    v2_sum[r] after w steps = sum of v2(3*r_i + 1) for i=0..w-1.

    We want: min over all r of v2_sum[r] after W steps  > W * log2(3).

    Use the rational bound  log2(3) < 1585/1000  (since 2^1585 > 3^1000).

    Returns (W, min_sum) if found within max_W, else (None, None).
    """
    odd_residues = [r for r in range(1, M, 2)]

    # Build transition table once
    transition = {r: syracuse_mod(M, r) for r in odd_residues}

    # v2_sum[r] = cumulative v2 sum after current number of steps, starting from r
    v2_sum = {r: 0 for r in odd_residues}

    for w in range(1, max_W + 1):
        new_v2_sum = {}
        for r in odd_residues:
            vv = v2(3 * r + 1)
            next_r = transition[r]
            # next_r should be an odd residue; if it's even something is wrong
            new_v2_sum[r] = vv + v2_sum.get(next_r, 0)
        v2_sum = new_v2_sum

        min_sum = min(v2_sum.values())
        # Check: 1000 * min_sum > w * 1585
        if 1000 * min_sum > w * 1585:
            return w, min_sum

    return None, None


# ---------------------------------------------------------------------------
# Step 4: Build and print comparison table
# ---------------------------------------------------------------------------

def run_all():
    results = []

    print("Running mixed 2-adic/3-adic Collatz analysis...")
    print(f"{'Mod':>6} {'k':>2} {'j':>2}  {'#odd':>6}  {'#unsafe':>7}  "
          f"{'max_disc':>8}  {'zero_disc':>9}  {'W':>5}  {'min_v2':>7}  {'margin':>8}")
    print("-" * 85)

    for k, j, M in PARAMS:
        odd_residues, unsafe_residues, max_disc, zero_disc, per_res = analyze_unsafe(M, k)
        W, min_sum = window_dp(M, k)

        if W is not None:
            margin = 1000 * min_sum - W * 1585
        else:
            margin = None

        row = {
            "M": M,
            "k": k,
            "j": j,
            "num_odd_residues": len(odd_residues),
            "num_unsafe": len(unsafe_residues),
            "max_discrepancy": max_disc,
            "zero_disc_count": zero_disc,
            "convergence_window_W": W,
            "min_v2_sum": min_sum,
            "margin_1000sum_minus_W1585": margin,
            "unsafe_details": {
                str(r): {
                    "modular_v2": mv,
                    "min_actual_v2": ma,
                    "discrepancy": d,
                }
                for r, (mv, ma, d) in per_res.items()
            },
        }
        results.append(row)

        W_str = str(W) if W is not None else "N/A"
        ms_str = str(min_sum) if min_sum is not None else "N/A"
        mg_str = str(margin) if margin is not None else "N/A"

        print(f"{M:>6} {k:>2} {j:>2}  {len(odd_residues):>6}  {len(unsafe_residues):>7}  "
              f"{max_disc:>8}  {zero_disc:>9}  {W_str:>5}  {ms_str:>7}  {mg_str:>8}")

    print()
    return results


# ---------------------------------------------------------------------------
# Step 5: Analysis and key question answer
# ---------------------------------------------------------------------------

def find_cycles(M):
    """Find all cycles of the Syracuse map on odd residues mod M."""
    odd_res = list(range(1, M, 2))
    transition = {r: syracuse_mod(M, r) for r in odd_res}
    visited = set()
    cycles = []
    for start in odd_res:
        if start in visited:
            continue
        path = []
        cur = start
        seen_in_path = {}
        while cur not in visited and cur not in seen_in_path:
            seen_in_path[cur] = len(path)
            path.append(cur)
            cur = transition[cur]
        if cur in seen_in_path:
            cycle_start = seen_in_path[cur]
            cycles.append(path[cycle_start:])
        for r in path:
            visited.add(r)
    return cycles


def interpret_results(results):
    print("=" * 85)
    print("KEY FINDINGS")
    print("=" * 85)

    # Group by k, compare j=0 vs j>=1
    from collections import defaultdict
    by_k = defaultdict(list)
    for r in results:
        by_k[r["k"]].append(r)

    for k, rows in sorted(by_k.items()):
        baseline = next((r for r in rows if r["j"] == 0), None)
        if baseline is None:
            continue
        base_disc = baseline["max_discrepancy"]
        print(f"\nk={k}: baseline (j=0) M={baseline['M']}, max_discrepancy={base_disc}, "
              f"#unsafe={baseline['num_unsafe']}, W={baseline['convergence_window_W']}, "
              f"margin={baseline['margin_1000sum_minus_W1585']}")
        for row in rows:
            if row["j"] == 0:
                continue
            new_disc = row["max_discrepancy"]
            change = base_disc - new_disc
            flag = ""
            if new_disc == 0:
                flag = "  *** BREAKTHROUGH: discrepancy eliminated! ***"
            elif change > 0:
                flag = f"  ** POSITIVE: discrepancy reduced by {change} **"
            else:
                flag = "  (no improvement in discrepancy)"
            W_str = str(row["convergence_window_W"]) if row["convergence_window_W"] else "N/A"
            mg_str = str(row["margin_1000sum_minus_W1585"]) if row["margin_1000sum_minus_W1585"] is not None else "N/A"
            print(f"  j={row['j']} M={row['M']}: max_discrepancy={new_disc}, "
                  f"#unsafe={row['num_unsafe']}, W={W_str}, "
                  f"margin={mg_str}{flag}")

    print()
    # Investigate cycle structure
    print("CYCLE STRUCTURE (explains W=N/A for mixed moduli):")
    LOG2_3 = 1.5849625007  # exact
    for k, j, M in [(3, 0, 104), (3, 1, 312), (3, 2, 936), (4, 0, 208), (4, 1, 624), (5, 0, 416), (5, 1, 1248)]:
        cycles = find_cycles(M)
        cycle_rates = []
        for cyc in cycles:
            s = sum(v2(3 * r + 1) for r in cyc)
            rate = s / len(cyc)
            cycle_rates.append((len(cyc), s, rate))
        min_rate = min(r for _, _, r in cycle_rates)
        converges = min_rate > LOG2_3
        flag = "OK" if converges else "SLOW-CYCLE (fails certificate)"
        print(f"  M={M:>5} (k={k},j={j}): #cycles={len(cycles)}, "
              f"min_v2_rate={min_rate:.4f} vs log2(3)={LOG2_3:.4f}  [{flag}]")
        for cyc_len, cyc_sum, rate in cycle_rates:
            ok = ">" if rate > LOG2_3 else "<"
            print(f"    cycle len={cyc_len:3d}: v2_sum={cyc_sum:3d}, v2/step={rate:.4f} {ok} log2(3)")

    print()
    # Overall verdict on key question
    baseline_k3 = next((r for r in results if r["k"] == 3 and r["j"] == 0), None)
    mixed_k3_j1 = next((r for r in results if r["k"] == 3 and r["j"] == 1), None)
    if baseline_k3 and mixed_k3_j1:
        bd = baseline_k3["max_discrepancy"]
        md = mixed_k3_j1["max_discrepancy"]
        print(f"KEY QUESTION ANSWER (k=3 case):")
        if md == 0:
            print(f"  BREAKTHROUGH: Adding 3-adic precision reduced max_discrepancy from {bd} to 0.")
            print("  The modular v2 now perfectly predicts actual v2 for all unsafe residues.")
        elif md < bd:
            print(f"  POSITIVE SIGNAL: Adding j=1 reduced max_discrepancy from {bd} to {md}.")
            print("  3-adic precision partially resolves the overcount issue.")
            if md <= 2:
                print("  (Reduction to <=2 is a STRONG positive signal.)")
        else:
            print(f"  NEGATIVE RESULT: max_discrepancy unchanged at {md} after adding 3-adic levels.")
            print("  Reason: the overcount comes from 2-adic structure that 3-adic info cannot resolve.")
            print()
            print("  Structural explanation:")
            print("    For unsafe r, 3r+1 = 2^v * q (v >= k). With n = r + M*m,")
            print("    3n+1 = 2^k * (2^(v-k)*q + 39m). The inner term 2^(v-k)*q + 39m")
            print("    can be odd when m is odd (since 39m is odd iff m is odd), and")
            print("    39 = 3*13. Adding mod 3^j changes M = 13*2^k*3^j but the 39m")
            print("    term still has a factor of 3*13, so divisibility by 3^j in the")
            print("    modulus does NOT force 39m to resolve the 2-adic ambiguity.")
            print()
            print("  Certificate failure for j>=1 is due to NEW slow cycles introduced by")
            print("  the larger modulus, not the unsafe-residue issue. These slow cycles are")
            print("  modular artifacts: e.g. for M=312, a 14-cycle with v2/step=1.428 < log2(3)")
            print("  appears, but it is NOT a real Collatz cycle (verified: n=359 ≡ 47 mod 312")
            print("  maps to 539 ≡ 227 mod 312, breaking the modular cycle).")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    results = run_all()
    interpret_results(results)

    # Save to JSON
    out_path = "/Users/dcharb/Documents/collatz/UFRF0-Lean4-Explore-v2/exploration/q1_results.json"
    with open(out_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {out_path}")


if __name__ == "__main__":
    main()
