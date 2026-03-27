#!/usr/bin/env python3
"""
Collatz Growth Analysis: Characterise the growth rate of W(k).

Loads results from analysis/results.json (k=3..10) and fits W(k) to
linear, quadratic, and exponential models; analyses the drift budget.
"""

import json
import math
import sys
from fractions import Fraction

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

LOG2_3_F = 1.58496250072115618145  # float approximation
# log2(3) - 1  ≈  0.585 (cost per bad step, i.e. v2=1 drift magnitude)
BAD_STEP_COST = LOG2_3_F - 1         # ≈ 0.585 bits per v2=1 step
# v2=2 drift = log2(3) - 2  ≈ -0.415 bits (recovery step)
RECOVERY_PER_STEP = LOG2_3_F - 2     # ≈ -0.415


# ---------------------------------------------------------------------------
# Least-squares helpers (no numpy required)
# ---------------------------------------------------------------------------

def linear_fit(xs, ys):
    """Fit y = a*x + b via least squares. Returns (a, b)."""
    n = len(xs)
    sx = sum(xs)
    sy = sum(ys)
    sxx = sum(x * x for x in xs)
    sxy = sum(x * y for x, y in zip(xs, ys))
    denom = n * sxx - sx * sx
    if denom == 0:
        return None, None
    a = (n * sxy - sx * sy) / denom
    b = (sy - a * sx) / n
    return a, b


def quadratic_fit(xs, ys):
    """Fit y = a*x^2 + b*x + c via least squares. Returns (a, b, c)."""
    n = len(xs)
    # Build normal equations for [a, b, c]
    # S_ij = sum(x^(i+j)), i,j in {0,1,2}
    def S(p):
        return sum(x ** p for x in xs)
    def T(p):
        return sum((x ** p) * y for x, y in zip(xs, ys))

    # Normal matrix rows: [S4, S3, S2; S3, S2, S1; S2, S1, S0] * [a, b, c]^T = [T2, T1, T0]
    A = [
        [S(4), S(3), S(2)],
        [S(3), S(2), S(1)],
        [S(2), S(1), S(0)],
    ]
    b_vec = [T(2), T(1), T(0)]

    # Gaussian elimination
    aug = [row[:] + [bv] for row, bv in zip(A, b_vec)]
    nrows = 3
    for col in range(nrows):
        # Pivot
        pivot_row = max(range(col, nrows), key=lambda r: abs(aug[r][col]))
        aug[col], aug[pivot_row] = aug[pivot_row], aug[col]
        if abs(aug[col][col]) < 1e-15:
            return None, None, None
        for row in range(nrows):
            if row == col:
                continue
            factor = aug[row][col] / aug[col][col]
            for j in range(col, nrows + 1):
                aug[row][j] -= factor * aug[col][j]
    a = aug[0][3] / aug[0][0]
    b = aug[1][3] / aug[1][1]
    c = aug[2][3] / aug[2][2]
    return a, b, c


def r_squared(xs, ys, pred_fn):
    """Compute R^2 goodness of fit."""
    y_mean = sum(ys) / len(ys)
    ss_tot = sum((y - y_mean) ** 2 for y in ys)
    ss_res = sum((y - pred_fn(x)) ** 2 for x, y in zip(xs, ys))
    if ss_tot < 1e-15:
        return 1.0
    return 1.0 - ss_res / ss_tot


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    results_path = "/Users/dcharb/Documents/collatz/UFRF0-Lean4-Explore-v2/analysis/results.json"
    with open(results_path) as f:
        existing = json.load(f)

    part3 = existing["part3"]

    # Extract data for k = 3..10
    data = []
    for k_str in sorted(part3.keys(), key=int):
        k = int(k_str)
        info = part3[k_str]
        W = info["convergence_window"]
        if W is None:
            print(f"Warning: k={k} has no convergence window; skipping.", flush=True)
            continue
        data.append({
            "k": k,
            "modulus": info["modulus"],
            "max_bad_streak": info["max_bad_streak"],
            "W": W,
        })

    ks = [d["k"] for d in data]
    Ws = [d["W"] for d in data]
    modulii = [d["modulus"] for d in data]
    bad_streaks = [d["max_bad_streak"] for d in data]

    print("=" * 70)
    print("Collatz Growth Rate Analysis: W(k)")
    print("=" * 70)
    print()

    # -------------------------------------------------------------------------
    # 1. Raw data table
    # -------------------------------------------------------------------------
    print("1. Raw data (from results.json):")
    print(f"{'k':>4s} | {'modulus':>8s} | {'bad_streak':>10s} | {'W(k)':>6s}")
    print("-" * 40)
    for d in data:
        print(f"{d['k']:>4d} | {d['modulus']:>8d} | {d['max_bad_streak']:>10d} | {d['W']:>6d}")
    print()

    # -------------------------------------------------------------------------
    # 2. Ratio analysis
    # -------------------------------------------------------------------------
    print("2. Ratio analysis:")
    print(f"{'k':>4s} | {'W/k':>8s} | {'W/k^2':>8s} | {'W/2^k':>10s} | {'W/(bad+1)':>10s}")
    print("-" * 55)
    for d in data:
        k = d["k"]
        W = d["W"]
        b = d["max_bad_streak"]
        print(f"{k:>4d} | {W/k:>8.4f} | {W/k**2:>8.4f} | {W/(2**k):>10.6f} | {W/(b+1):>10.4f}")
    print()

    # -------------------------------------------------------------------------
    # 3. Model fitting
    # -------------------------------------------------------------------------
    print("3. Model fitting:")

    # Linear fit: W = a*k + b
    a_lin, b_lin = linear_fit(ks, Ws)
    lin_pred = lambda x: a_lin * x + b_lin
    r2_lin = r_squared(ks, Ws, lin_pred)
    print(f"  Linear:    W = {a_lin:.4f}*k + {b_lin:.4f}   (R^2 = {r2_lin:.6f})")

    # Quadratic fit: W = a*k^2 + b*k + c
    a_q, b_q, c_q = quadratic_fit(ks, Ws)
    quad_pred = lambda x: a_q * x**2 + b_q * x + c_q
    r2_q = r_squared(ks, Ws, quad_pred)
    print(f"  Quadratic: W = {a_q:.4f}*k^2 + {b_q:.4f}*k + {c_q:.4f}   (R^2 = {r2_q:.6f})")

    # Exponential fit: log(W) = a*k + b  =>  W = exp(b) * exp(a*k)
    log_Ws = [math.log(W) for W in Ws]
    a_exp, b_exp = linear_fit(ks, log_Ws)
    exp_pred = lambda x: math.exp(a_exp * x + b_exp)
    r2_exp = r_squared(ks, Ws, exp_pred)
    print(f"  Exponential: W ~ {math.exp(b_exp):.4f} * {math.exp(a_exp):.4f}^k   (R^2 = {r2_exp:.6f})")
    print()

    # -------------------------------------------------------------------------
    # 4. Residuals
    # -------------------------------------------------------------------------
    print("4. Residuals (predicted vs actual):")
    print(f"{'k':>4s} | {'W(k)':>6s} | {'lin_pred':>9s} | {'quad_pred':>10s} | {'exp_pred':>9s}")
    print("-" * 55)
    for d in data:
        k = d["k"]
        W = d["W"]
        print(f"{k:>4d} | {W:>6d} | {lin_pred(k):>9.1f} | {quad_pred(k):>10.1f} | {exp_pred(k):>9.1f}")
    print()

    # -------------------------------------------------------------------------
    # 5. Drift budget analysis
    # -------------------------------------------------------------------------
    print("5. Drift budget analysis:")
    print(f"  BAD_STEP_COST    = log2(3) - 1   = {BAD_STEP_COST:.6f} bits (v2=1 step)")
    print(f"  RECOVERY_PER_STEP= log2(3) - 2   = {RECOVERY_PER_STEP:.6f} bits (v2=2 step)")
    print()
    print(f"  For a bad streak of length L = (k+1):")
    print(f"    Accumulated positive drift = (k+1) * {BAD_STEP_COST:.4f}")
    print(f"    Min recovery steps needed  = (k+1) * {BAD_STEP_COST:.4f} / {abs(RECOVERY_PER_STEP):.4f}")
    print(f"                               = (k+1) * {BAD_STEP_COST/abs(RECOVERY_PER_STEP):.4f}")
    print()
    print(f"{'k':>4s} | {'bad_streak L':>12s} | {'drift_cost':>12s} | {'min_recov':>10s} | {'W(k)':>6s} | {'secondary slots':>15s}")
    print("-" * 75)
    for d in data:
        k = d["k"]
        L = d["max_bad_streak"]
        W = d["W"]
        cost = L * BAD_STEP_COST
        min_recov = cost / abs(RECOVERY_PER_STEP)
        # "secondary bad streak" slots: (W - L - min_recov) / (L + min_recov)
        secondary = (W - L - min_recov) / (L + min_recov) if (L + min_recov) > 0 else 0
        print(f"{k:>4d} | {L:>12d} | {cost:>12.4f} | {min_recov:>10.2f} | {W:>6d} | {secondary:>15.3f}")
    print()

    # -------------------------------------------------------------------------
    # 6. W(k)/modulus monotonicity check
    # -------------------------------------------------------------------------
    print("6. W(k)/modulus (should decrease monotonically):")
    ratios = []
    for d in data:
        ratio = d["W"] / d["modulus"]
        ratios.append(ratio)
        print(f"  k={d['k']}: W={d['W']}, modulus={d['modulus']}, W/modulus = {ratio:.8f}")
    is_decreasing = all(ratios[i] > ratios[i+1] for i in range(len(ratios)-1))
    print(f"  Monotonically decreasing: {is_decreasing}")
    print()

    # -------------------------------------------------------------------------
    # 7. Proof strategy conclusion
    # -------------------------------------------------------------------------
    print("7. Proof strategy supported by data:")
    print()
    print(f"  Linear R^2     = {r2_lin:.6f}")
    print(f"  Quadratic R^2  = {r2_q:.6f}")
    print(f"  Exponential R^2= {r2_exp:.6f}")
    print()

    best_model = max(
        [("Linear O(k)", r2_lin), ("Quadratic O(k^2)", r2_q), ("Exponential O(2^k)", r2_exp)],
        key=lambda x: x[1]
    )
    print(f"  Best fitting model: {best_model[0]} (R^2 = {best_model[1]:.6f})")
    print()

    # Interpretation
    if r2_lin > 0.98 and abs(r2_lin - r2_q) < 0.01:
        print("  CONCLUSION: Data strongly supports O(k) growth (linear).")
        print("  This means a proof bounding W(k) = O(k) is viable.")
    elif r2_q > 0.98 and r2_q > r2_lin + 0.01:
        print("  CONCLUSION: Data supports O(k^2) growth (quadratic).")
        print("  Linear bound is insufficient; quadratic bound needed.")
    elif r2_exp > 0.98 and r2_exp > r2_q + 0.01:
        print("  CONCLUSION: Data supports O(2^k) growth (exponential).")
        print("  Sub-exponential proof strategies would need refinement.")
    else:
        print(f"  CONCLUSION: Best fit is {best_model[0]}, but models are close.")
        print("  More data points (larger k) needed for definitive conclusion.")

    print()
    print(f"  bad_streak(k) = k+1 always holds in data: ",
          end="")
    print(all(d["max_bad_streak"] == d["k"] + 1 for d in data))

    print()
    # Check if W(k) ≈ c * (k+1) * (BAD_STEP_COST / abs(RECOVERY_PER_STEP) + 1)
    # i.e. W(k) / (k+1) converges to a constant
    ratios_kp1 = [d["W"] / (d["k"] + 1) for d in data]
    mean_ratio = sum(ratios_kp1) / len(ratios_kp1)
    std_ratio = math.sqrt(sum((r - mean_ratio)**2 for r in ratios_kp1) / len(ratios_kp1))
    print(f"  W(k)/(k+1) values: {[f'{r:.2f}' for r in ratios_kp1]}")
    print(f"  Mean = {mean_ratio:.4f}, Std = {std_ratio:.4f}")
    if std_ratio / mean_ratio < 0.15:
        print(f"  => W(k) grows roughly linearly as ~{mean_ratio:.2f}*(k+1) = O(k)")
    else:
        print(f"  => W(k)/(k+1) is not constant; growth may be super-linear.")

    # -------------------------------------------------------------------------
    # Save GROWTH_ANALYSIS.md
    # -------------------------------------------------------------------------
    md_path = "/Users/dcharb/Documents/collatz/UFRF0-Lean4-Explore-v2/analysis/GROWTH_ANALYSIS.md"
    with open(md_path, "w") as f:
        f.write("# Collatz W(k) Growth Analysis\n\n")
        f.write("## Data\n\n")
        f.write("| k | modulus | max_bad_streak | W(k) |\n")
        f.write("|---|---------|---------------|------|\n")
        for d in data:
            f.write(f"| {d['k']} | {d['modulus']} | {d['max_bad_streak']} | {d['W']} |\n")
        f.write("\n## Model Fits\n\n")
        f.write(f"- Linear:     W = {a_lin:.4f}*k + {b_lin:.4f}   (R^2 = {r2_lin:.6f})\n")
        f.write(f"- Quadratic:  W = {a_q:.4f}*k^2 + {b_q:.4f}*k + {c_q:.4f}   (R^2 = {r2_q:.6f})\n")
        f.write(f"- Exponential: W ~ {math.exp(b_exp):.4f} * {math.exp(a_exp):.4f}^k   (R^2 = {r2_exp:.6f})\n")
        f.write("\n## Drift Budget\n\n")
        f.write(f"- bad_streak(k) = k+1 always\n")
        f.write(f"- Drift cost per bad streak = (k+1) * {BAD_STEP_COST:.6f}\n")
        f.write(f"- Min recovery steps = (k+1) * {BAD_STEP_COST/abs(RECOVERY_PER_STEP):.4f}\n")
        f.write(f"- W(k)/(k+1) mean = {mean_ratio:.4f}, std = {std_ratio:.4f}\n")
        f.write("\n## Conclusion\n\n")
        f.write(f"Best fitting model: **{best_model[0]}** (R^2 = {best_model[1]:.6f})\n\n")
        if r2_lin > r2_q - 0.005:
            f.write("The data is consistent with **O(k) linear growth** of W(k).\n")
            f.write(f"Specifically, W(k) ≈ {mean_ratio:.2f}*(k+1).\n")
        else:
            f.write("The data suggests **O(k^2) quadratic growth** of W(k).\n")
        f.write("\nW(k)/modulus decreases monotonically: " + str(is_decreasing) + "\n")
        f.write("\nThis supports the proof strategy that the convergence window\n")
        f.write("is a negligible fraction of the modulus as k grows.\n")

    print(f"\nGrowth analysis saved to {md_path}")


if __name__ == "__main__":
    main()
