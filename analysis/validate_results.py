#!/usr/bin/env python3
"""
Independent validation of Collatz orbit analysis results.

This script verifies the key claims from the main collatz_orbit_analysis.py
WITHOUT importing from or referencing it. All computations are done from
scratch using only Python standard library.
"""

import math
from fractions import Fraction
from collections import defaultdict

# ---------------------------------------------------------------------------
# Constants (independently defined)
# ---------------------------------------------------------------------------

# Rational approximation of log2(3) matching double precision
LOG2_3 = Fraction(892254565955501, 562949953421312)

PASS_COUNT = 0
FAIL_COUNT = 0


def report(name, passed, detail=""):
    global PASS_COUNT, FAIL_COUNT
    tag = "PASS" if passed else "FAIL"
    if not passed:
        FAIL_COUNT += 1
    else:
        PASS_COUNT += 1
    suffix = f"  ({detail})" if detail else ""
    print(f"  [{tag}] {name}{suffix}")


def section(title):
    print()
    print("=" * 72)
    print(f"  {title}")
    print("=" * 72)


# ---------------------------------------------------------------------------
# Independent helper functions
# ---------------------------------------------------------------------------

def val2(n):
    """2-adic valuation of n: number of trailing zeros in binary."""
    if n == 0:
        return -1
    count = 0
    while n % 2 == 0:
        n //= 2
        count += 1
    return count


def extended_gcd(a, b):
    """Extended Euclidean algorithm. Returns (gcd, x, y) with a*x + b*y = gcd."""
    if a == 0:
        return b, 0, 1
    g, x1, y1 = extended_gcd(b % a, a)
    return g, y1 - (b // a) * x1, x1


def modinv(a, m):
    """Modular inverse of a mod m, or None if it doesn't exist."""
    g, x, _ = extended_gcd(a % m, m)
    if g != 1:
        return None
    return x % m


def syracuse_step(n):
    """Apply one Syracuse step to odd n: return (3n+1) / 2^v2(3n+1)."""
    assert n % 2 == 1 and n > 0
    val = 3 * n + 1
    v = val2(val)
    return val >> v, v


def collatz_step(n):
    """One step of the standard Collatz map."""
    if n % 2 == 0:
        return n // 2
    else:
        return 3 * n + 1


def full_collatz_sequence(n, max_steps=10000):
    """Run the Collatz sequence from n until reaching 1 or max_steps."""
    seq = [n]
    for _ in range(max_steps):
        if n == 1:
            break
        n = collatz_step(n)
        seq.append(n)
    return seq


# ---------------------------------------------------------------------------
# CHECK 1: Syracuse map on ZMod 13
# ---------------------------------------------------------------------------

def check1_syracuse_zmod13():
    section("CHECK 1: Syracuse map on ZMod 13")
    print("  Verifying modular inverses and Syracuse images.")

    m = 13
    odd_residues = [1, 3, 5, 7, 9, 11]
    all_ok = True

    # Sub-check 1a: Verify pow(2, v2, 13) as modular inverse check
    for v in range(1, 7):
        p = pow(2, v, m)
        inv = modinv(p, m)
        # Verify inv * p == 1 (mod 13)
        ok = (inv * p) % m == 1
        if not ok:
            all_ok = False
        report(f"inv(2^{v} mod 13) = {inv}, check: {inv}*{p} mod 13 = {(inv*p)%m}",
               ok)

    # Sub-check 1b: Cross-check Syracuse images against direct computation
    # For each odd residue r mod 13, pick several actual integers n = r (mod 13)
    # that are odd, compute Syracuse step, verify image mod 13 matches table
    print()
    print("  Cross-checking modular Syracuse against actual integer computation:")

    # Expected images from results.json (the main analysis)
    expected_images = {
        1: {1: 2, 2: 1, 3: 7, 4: 10, 5: 5, 6: 9},
        3: {1: 5, 2: 9, 3: 11, 4: 12, 5: 6, 6: 3},
        5: {1: 8, 2: 4, 3: 2, 4: 1, 5: 7, 6: 10},
        7: {1: 11, 2: 12, 3: 6, 4: 3, 5: 8, 6: 4},
        9: {1: 1, 2: 7, 3: 10, 4: 5, 5: 9, 6: 11},
        11: {1: 4, 2: 2, 3: 1, 4: 7, 5: 10, 6: 5},
    }

    # Independently compute the Syracuse image mod 13 for each (r, v2)
    for r in odd_residues:
        val = 3 * r + 1
        for v in range(1, 7):
            inv = modinv(pow(2, v, m), m)
            computed_image = (inv * val) % m
            expected = expected_images[r][v]
            ok = computed_image == expected
            if not ok:
                all_ok = False
            report(f"r={r}, v2={v}: (3*{r}+1)/{2**v} mod 13 = {computed_image}, expected {expected}", ok)

    # Sub-check 1c: Verify against actual integers
    print()
    print("  Verifying a few cases against actual integer Syracuse steps:")
    test_cases = [
        # (n, expected residue mod 13, expected v2)
        (1, 1, None),    # 3*1+1=4, v2=2, 4/4=1 -> 1 mod 13 = 1
        (3, 3, None),    # 3*3+1=10, v2=1, 10/2=5 -> 5 mod 13 = 5
        (5, 5, None),    # 3*5+1=16, v2=4, 16/16=1 -> 1 mod 13 = 1
        (7, 7, None),    # 3*7+1=22, v2=1, 22/2=11 -> 11 mod 13 = 11
        (9, 9, None),    # 3*9+1=28, v2=2, 28/4=7 -> 7 mod 13 = 7
        (11, 11, None),  # 3*11+1=34, v2=1, 34/2=17 -> 17 mod 13 = 4
        (27, 1, None),   # 27 mod 13 = 1; 3*27+1=82, v2=1, 82/2=41; 41 mod 13 = 2
        (53, 1, None),   # 53 mod 13 = 1; 3*53+1=160, v2=5, 160/32=5; 5 mod 13 = 5
        (97, 6, None),   # 97 mod 13 = 6 (even! skip); let's use 99 instead
        (99, 8, None),   # 99 mod 13 = 8 (even! skip)
        (101, 10, None), # 101 mod 13 = 10 (even! skip)
        (103, 12, None), # 103 mod 13 = 12 (even! skip)
    ]

    # Actually just test all odd numbers from 1 to 201 that are odd and have odd residue mod 13
    cross_check_count = 0
    cross_check_ok = 0
    for n in range(1, 202, 2):
        r = n % m
        if r % 2 == 0:
            continue  # skip even residues mod 13
        result, v = syracuse_step(n)
        result_mod = result % m
        # Compute expected from modular formula
        inv = modinv(pow(2, v, m), m)
        expected_mod = (inv * (3 * r + 1)) % m
        cross_check_count += 1
        if result_mod == expected_mod:
            cross_check_ok += 1

    ok = cross_check_ok == cross_check_count
    report(f"Cross-check {cross_check_count} odd integers n in [1..201] with odd residue mod 13: "
           f"{cross_check_ok}/{cross_check_count} match", ok)


# ---------------------------------------------------------------------------
# CHECK 2: v2 distribution is geometric for k=3 (mod 104)
# ---------------------------------------------------------------------------

def check2_v2_distribution():
    section("CHECK 2: v2 distribution for k=3 (mod 104)")
    print("  Checking that v2 distribution among odd residues mod 104 is geometric-like.")

    modulus = 104  # 13 * 2^3
    odd_residues = [r for r in range(modulus) if r % 2 == 1]
    num_odd = len(odd_residues)

    # Compute v2 distribution
    v2_dist = defaultdict(int)
    for r in odd_residues:
        val = 3 * r + 1
        v = val2(val)
        v2_dist[v] += 1

    print(f"  Number of odd residues mod {modulus}: {num_odd}")
    report(f"num_odd = {num_odd} (expected 52)", num_odd == 52)

    # Expected from results.json: {1:26, 2:13, 3:6, 4:4, 5:1, 6:1, 8:1}
    expected_dist = {1: 26, 2: 13, 3: 6, 4: 4, 5: 1, 6: 1, 8: 1}

    print(f"  v2 distribution:")
    dist_ok = True
    for v in sorted(v2_dist.keys()):
        pct = 100.0 * v2_dist[v] / num_odd
        exp = expected_dist.get(v, 0)
        match = v2_dist[v] == exp
        if not match:
            dist_ok = False
        print(f"    v2={v}: {v2_dist[v]:>3d} ({pct:5.1f}%), expected {exp}")

    report("v2 distribution matches expected values", dist_ok)

    # Check geometric-like pattern: v2=1 should be ~50%, v2=2 ~25%, etc.
    # The dominant terms should satisfy: count(v2=1) ~ num_odd/2, count(v2=2) ~ num_odd/4
    geo_ok = True
    ratio_1 = v2_dist[1] / num_odd
    ratio_2 = v2_dist[2] / num_odd
    ratio_3 = v2_dist[3] / num_odd

    report(f"v2=1 fraction = {ratio_1:.4f} (expected ~0.50)", abs(ratio_1 - 0.50) < 0.01)
    report(f"v2=2 fraction = {ratio_2:.4f} (expected ~0.25)", abs(ratio_2 - 0.25) < 0.01)
    report(f"v2=3 fraction = {ratio_3:.4f} (expected ~0.115)", abs(ratio_3 - 0.115) < 0.02)

    return v2_dist


# ---------------------------------------------------------------------------
# CHECK 3: Spot-check bad streaks for k=3
# ---------------------------------------------------------------------------

def check3_bad_streaks():
    section("CHECK 3: Bad streak spot-checks for k=3 (mod 104)")
    print("  Building transition graph and manually tracing bad streaks.")

    modulus = 104
    # Build transition graph independently
    transitions = {}
    for r in range(modulus):
        if r % 2 == 0:
            continue
        val = 3 * r + 1
        v = val2(val)
        image = (val >> v) % modulus
        transitions[r] = (v, image)

    # Find all bad streaks (consecutive v2=1 steps)
    all_streaks = []
    for start in transitions:
        if transitions[start][0] != 1:
            continue
        length = 0
        node = start
        visited = set()
        while node in transitions and transitions[node][0] == 1 and node not in visited:
            visited.add(node)
            length += 1
            _, node = transitions[node]
        if length > 0:
            v2_after = transitions[node][0] if node in transitions else None
            all_streaks.append((start, length, v2_after))

    max_streak_len = max(s[1] for s in all_streaks) if all_streaks else 0

    report(f"Maximum bad streak length = {max_streak_len} (expected 4)", max_streak_len == 4)
    report(f"Number of starting points with v2=1: {len(all_streaks)} (expected 26)",
           len(all_streaks) == 26)

    # Manually trace the longest streaks
    print()
    print("  Longest bad streaks (length 4):")
    for start, length, v2_after in all_streaks:
        if length == 4:
            # Trace the streak step by step
            node = start
            trace = []
            for _ in range(length + 1):
                v, img = transitions[node]
                trace.append((node, v, img))
                node = img
            print(f"    Start={start}: ", end="")
            for r, v, img in trace:
                print(f"r={r}->v2={v}->", end="")
            print(f"r={node} (v2={transitions[node][0]})")

    # Verify a specific streak manually
    # Pick one length-4 streak and verify each step by direct computation
    long_streaks = [(s, l, v) for s, l, v in all_streaks if l == 4]
    if long_streaks:
        s, l, va = long_streaks[0]
        print(f"\n  Manual verification of streak starting at r={s}:")
        node = s
        manual_ok = True
        for step in range(l):
            val = 3 * node + 1
            v = val2(val)
            img = (val >> v) % modulus
            expected_v, expected_img = transitions[node]
            step_ok = (v == expected_v == 1) and (img == expected_img)
            if not step_ok:
                manual_ok = False
            print(f"    Step {step+1}: r={node}, 3r+1={val}, v2={v}, image={img} "
                  f"(expected v2={expected_v}, image={expected_img})")
            node = img
        # After streak, v2 should be > 1
        final_v = transitions[node][0]
        print(f"    After streak: r={node}, v2={final_v} (should be > 1)")
        report(f"Manual streak trace: all v2=1 in streak, v2_after={final_v}>1",
               manual_ok and final_v > 1)


# ---------------------------------------------------------------------------
# CHECK 4: Convergence window for k=3
# ---------------------------------------------------------------------------

def check4_convergence_window():
    section("CHECK 4: Convergence window DP for k=3")
    print("  Running independent DP to confirm W=10 gives negative worst-case drift.")

    modulus = 104
    # Build transition graph
    transitions = {}
    for r in range(modulus):
        if r % 2 == 0:
            continue
        val = 3 * r + 1
        v = val2(val)
        image = (val >> v) % modulus
        transitions[r] = (v, image)

    odd_residues = list(transitions.keys())

    # DP: dp[r] = max cumulative drift starting from r in exactly w steps
    dp_prev = {r: Fraction(0) for r in odd_residues}

    convergence_w = None
    drift_at_10 = None

    for w in range(1, 51):
        dp_curr = {}
        for r in odd_residues:
            v, image = transitions[r]
            d = LOG2_3 - v  # drift for this step
            dp_curr[r] = d + dp_prev[image]
        max_drift = max(dp_curr.values())

        if w == 10:
            drift_at_10 = float(max_drift)

        if convergence_w is None and max_drift < 0:
            convergence_w = w

        dp_prev = dp_curr

    report(f"Convergence window = {convergence_w} (expected 10)", convergence_w == 10)
    report(f"Worst-case drift at W=10: {drift_at_10:+.6f} (expected < 0)", drift_at_10 < 0)

    # Cross-check specific drift values from results.json
    expected_drift_w10 = -0.15037499278843924
    report(f"Drift at W=10 matches expected: {drift_at_10:.6f} vs {expected_drift_w10:.6f}",
           abs(drift_at_10 - expected_drift_w10) < 1e-10)

    # Also verify some earlier window drifts
    # Re-run to collect all
    dp_prev = {r: Fraction(0) for r in odd_residues}
    all_drifts = {}
    for w in range(1, 16):
        dp_curr = {}
        for r in odd_residues:
            v, image = transitions[r]
            d = LOG2_3 - v
            dp_curr[r] = d + dp_prev[image]
        all_drifts[w] = float(max(dp_curr.values()))
        dp_prev = dp_curr

    expected_drifts = {
        1: 0.5849625007211561,
        2: 1.1699250014423122,
        5: 1.9248125036057804,
        8: 0.6797000057692486,
        9: 0.2646625064904047,
        10: -0.15037499278843924,
        15: -2.225562489182659,
    }
    print()
    all_drift_ok = True
    for w, expected in expected_drifts.items():
        got = all_drifts[w]
        ok = abs(got - expected) < 1e-10
        if not ok:
            all_drift_ok = False
        report(f"Drift W={w}: got {got:+.10f}, expected {expected:+.10f}", ok)


# ---------------------------------------------------------------------------
# CHECK 5: Cross-validate against actual Collatz sequences
# ---------------------------------------------------------------------------

def check5_actual_sequences():
    section("CHECK 5: Cross-validate with actual Collatz sequences")
    print("  Tracing actual Collatz sequences and comparing to modular predictions.")
    print()
    print("  The transition graph on ZMod(13*2^k) determines v2(3n+1) for each")
    print("  residue class, but only when the actual v2 value is < k (the 2-adic")
    print("  precision of the modulus). For larger k, predictions are more accurate.")
    print("  We test at k=8 (mod 3328) where precision suffices for all encountered v2.")

    test_values = [27, 97, 871, 6171, 77031, 837799]

    # --- Primary validation: k=8 (mod 3328) should be fully accurate ---
    k_exp = 8
    modulus = 13 * (1 << k_exp)
    print(f"\n  --- Primary test: modulus {modulus} (k={k_exp}, high precision) ---")

    transitions = {}
    for r in range(modulus):
        if r % 2 == 0:
            continue
        val = 3 * r + 1
        v = val2(val)
        image = (val >> v) % modulus
        transitions[r] = (v, image)

    for n_start in test_values:
        n = n_start
        steps_checked = 0
        v2_mismatches = 0
        mod13_mismatches = 0
        max_steps = 500

        step = 0
        while n != 1 and step < max_steps:
            if n % 2 == 0:
                n = n // 2
                continue

            r_mod = n % modulus
            actual_next, actual_v2 = syracuse_step(n)
            predicted_v2, predicted_image = transitions[r_mod]

            if actual_v2 != predicted_v2:
                v2_mismatches += 1
            if actual_next % 13 != predicted_image % 13:
                mod13_mismatches += 1

            steps_checked += 1
            n = actual_next
            step += 1

        ok = v2_mismatches == 0 and mod13_mismatches == 0
        report(f"n={n_start} (mod {modulus}): {steps_checked} steps, "
               f"v2 mismatches={v2_mismatches}, mod-13 mismatches={mod13_mismatches}", ok)

    # --- Secondary: show that accuracy improves with k ---
    print(f"\n  --- Accuracy improvement with k (informational, not scored) ---")
    for k_exp in [3, 5, 8]:
        modulus = 13 * (1 << k_exp)
        transitions = {}
        for r in range(modulus):
            if r % 2 == 0:
                continue
            val = 3 * r + 1
            v = val2(val)
            image = (val >> v) % modulus
            transitions[r] = (v, image)

        total_steps = 0
        total_v2_mismatch = 0
        for n_start in test_values:
            n = n_start
            step = 0
            while n != 1 and step < 500:
                if n % 2 == 0:
                    n = n // 2
                    continue
                r_mod = n % modulus
                actual_next, actual_v2 = syracuse_step(n)
                predicted_v2, _ = transitions[r_mod]
                if actual_v2 != predicted_v2:
                    total_v2_mismatch += 1
                total_steps += 1
                n = actual_next
                step += 1

        pct = 100.0 * (total_steps - total_v2_mismatch) / total_steps
        print(f"    k={k_exp} (mod {modulus:>5d}): {pct:6.2f}% v2 predictions correct "
              f"({total_v2_mismatch} mismatches in {total_steps} steps)")

    # --- Verify v2 prediction is exact when actual v2 < k ---
    print(f"\n  --- Verifying: v2 prediction exact when actual v2 < k ---")
    k_exp = 3
    modulus = 13 * (1 << k_exp)
    transitions = {}
    for r in range(modulus):
        if r % 2 == 0:
            continue
        val = 3 * r + 1
        v = val2(val)
        image = (val >> v) % modulus
        transitions[r] = (v, image)

    total_low_v2 = 0
    low_v2_mismatches = 0
    total_high_v2 = 0
    high_v2_mismatches = 0
    for n_start in test_values:
        n = n_start
        step = 0
        while n != 1 and step < 500:
            if n % 2 == 0:
                n = n // 2
                continue
            r_mod = n % modulus
            actual_next, actual_v2 = syracuse_step(n)
            predicted_v2, _ = transitions[r_mod]
            if actual_v2 < k_exp:
                total_low_v2 += 1
                if actual_v2 != predicted_v2:
                    low_v2_mismatches += 1
            else:
                total_high_v2 += 1
                if actual_v2 != predicted_v2:
                    high_v2_mismatches += 1
            n = actual_next
            step += 1

    report(f"v2 < k={k_exp}: {total_low_v2} steps, {low_v2_mismatches} mismatches "
           f"(should be 0)", low_v2_mismatches == 0)
    print(f"    (For reference: v2 >= {k_exp}: {total_high_v2} steps, "
          f"{high_v2_mismatches} mismatches -- expected due to limited precision)")

    # Additional: trace one trajectory in detail to show the correspondence
    print(f"\n  Detailed trace for n=27 (mod 104, showing mod-13 agreement):")
    modulus = 104
    transitions = {}
    for r in range(modulus):
        if r % 2 == 0:
            continue
        val = 3 * r + 1
        v = val2(val)
        image = (val >> v) % modulus
        transitions[r] = (v, image)

    n = 27
    for step in range(min(10, 50)):
        if n == 1:
            break
        if n % 2 == 0:
            n = n // 2
            continue
        r_mod = n % modulus
        r_mod13 = n % 13
        actual_next, actual_v2 = syracuse_step(n)
        predicted_v2, predicted_image = transitions[r_mod]
        v2_sym = "==" if actual_v2 == predicted_v2 else "!="
        m13_sym = "==" if actual_next % 13 == predicted_image % 13 else "!="
        print(f"    n={n:>6d} | r mod 104={r_mod:>3d} | r mod 13={r_mod13:>2d} | "
              f"v2: {actual_v2}{v2_sym}{predicted_v2} | "
              f"img mod 13: {actual_next%13}{m13_sym}{predicted_image%13}")
        n = actual_next


# ---------------------------------------------------------------------------
# CHECK 6: Bad streak bound grows with k: max bad streak = k+1
# ---------------------------------------------------------------------------

def check6_bad_streak_growth():
    section("CHECK 6: Bad streak bound grows with k")
    print("  Verifying max bad streak = k+1 for k=3..8.")

    expected_max_streaks = {3: 4, 4: 5, 5: 6, 6: 7, 7: 8, 8: 9}

    for k_exp in range(3, 9):
        modulus = 13 * (1 << k_exp)

        # Build transition graph
        transitions = {}
        for r in range(modulus):
            if r % 2 == 0:
                continue
            val = 3 * r + 1
            v = val2(val)
            image = (val >> v) % modulus
            transitions[r] = (v, image)

        # Find max bad streak
        max_streak = 0
        for start in transitions:
            if transitions[start][0] != 1:
                continue
            length = 0
            node = start
            visited = set()
            while node in transitions and transitions[node][0] == 1 and node not in visited:
                visited.add(node)
                length += 1
                _, node = transitions[node]
            if length > max_streak:
                max_streak = length

        expected = expected_max_streaks[k_exp]
        ok = max_streak == expected
        report(f"k={k_exp} (mod {modulus}): max bad streak = {max_streak}, expected {expected} (= k+1)",
               ok)

    # Also verify the claimed pattern: max_bad_streak = k+1
    print()
    print("  Checking the formula max_bad_streak = k + 1:")
    formula_ok = True
    for k_exp in range(3, 9):
        modulus = 13 * (1 << k_exp)
        transitions = {}
        for r in range(modulus):
            if r % 2 == 0:
                continue
            val = 3 * r + 1
            v = val2(val)
            image = (val >> v) % modulus
            transitions[r] = (v, image)

        max_streak = 0
        for start in transitions:
            if transitions[start][0] != 1:
                continue
            length = 0
            node = start
            visited = set()
            while node in transitions and transitions[node][0] == 1 and node not in visited:
                visited.add(node)
                length += 1
                _, node = transitions[node]
            max_streak = max(max_streak, length)

        if max_streak != k_exp + 1:
            formula_ok = False

    report("Formula max_bad_streak = k + 1 holds for all k in {3..8}", formula_ok)


# ---------------------------------------------------------------------------
# CHECK 7: Statistical analysis on actual trajectories
# ---------------------------------------------------------------------------

def check7_statistical_analysis():
    section("CHECK 7: Statistical analysis on first 10,000 odd numbers")
    print("  Computing empirical statistics and comparing to theoretical predictions.")

    total_v2 = 0
    total_steps = 0
    max_bad_streak_global = 0
    all_drifts = []

    modulus = 104  # 13 * 2^3

    # Build transition graph for streak tracking
    transitions = {}
    for r in range(modulus):
        if r % 2 == 0:
            continue
        val = 3 * r + 1
        v = val2(val)
        image = (val >> v) % modulus
        transitions[r] = (v, image)

    num_tested = 0
    for start in range(1, 20001, 2):  # first 10,000 odd numbers
        n = start
        steps = 0
        current_bad_streak = 0
        max_bad_streak_this = 0

        while n != 1 and steps < 10000:
            if n % 2 == 0:
                n = n // 2
                continue

            result, v = syracuse_step(n)
            total_v2 += v
            total_steps += 1
            drift = float(LOG2_3) - v
            all_drifts.append(drift)

            if v == 1:
                current_bad_streak += 1
                max_bad_streak_this = max(max_bad_streak_this, current_bad_streak)
            else:
                current_bad_streak = 0

            n = result
            steps += 1

        max_bad_streak_global = max(max_bad_streak_global, max_bad_streak_this)
        num_tested += 1

    avg_v2 = total_v2 / total_steps if total_steps > 0 else 0
    avg_drift = sum(all_drifts) / len(all_drifts) if all_drifts else 0

    # Theoretical predictions:
    # E[v2] = sum_{k=1}^{inf} k * 2^{-k} = 2.0 (for ideal geometric distribution)
    # E[drift] = log2(3) - E[v2] = 1.585 - 2.0 = -0.415
    theoretical_avg_v2 = 2.0
    theoretical_avg_drift = float(LOG2_3) - 2.0

    print(f"\n  Total Syracuse steps analyzed: {total_steps}")
    print(f"  Numbers tested: {num_tested}")
    print()
    print(f"  Average v2 per step: {avg_v2:.4f}")
    print(f"  Theoretical E[v2]:   {theoretical_avg_v2:.4f}")
    # v2 average should be close to 2.0; allow some slack for finite sample
    report(f"Average v2 = {avg_v2:.4f} (expected ~{theoretical_avg_v2:.4f}, tolerance 0.1)",
           abs(avg_v2 - theoretical_avg_v2) < 0.1)

    print()
    print(f"  Average drift per step: {avg_drift:.6f}")
    print(f"  Theoretical E[drift]:   {theoretical_avg_drift:.6f}")
    report(f"Average drift = {avg_drift:.6f} (expected ~{theoretical_avg_drift:.6f}, tolerance 0.1)",
           abs(avg_drift - theoretical_avg_drift) < 0.1)

    print()
    print(f"  Maximum consecutive bad streak observed: {max_bad_streak_global}")
    # The max bad streak in actual trajectories can exceed the modular bound
    # because the modular bound is for the *transition graph* at a fixed modulus,
    # not for actual trajectories (which can traverse different modular classes).
    # But it shouldn't be astronomically large -- typically bounded by ~20 or so
    # for the first 10,000 odd numbers.
    report(f"Max bad streak = {max_bad_streak_global} (expected reasonable, < 30)",
           max_bad_streak_global < 30)

    # Check that drift is negative on average (this is the key convergence claim)
    report(f"Average drift is negative: {avg_drift:.6f} < 0", avg_drift < 0)

    # Additional: v2 distribution in actual trajectories should be roughly geometric
    v2_counts = defaultdict(int)
    for d in all_drifts:
        v = round(float(LOG2_3) - d)  # recover v2 from drift
        v2_counts[v] += 1

    print()
    print("  Empirical v2 distribution (from trajectories):")
    for v in sorted(v2_counts.keys()):
        if v2_counts[v] > 0:
            pct = 100.0 * v2_counts[v] / total_steps
            theoretical_pct = 100.0 * (0.5 ** v) if v >= 1 else 0
            print(f"    v2={v}: {pct:5.2f}% (theoretical ~{theoretical_pct:5.2f}%)")

    # Check v2=1 is roughly 50%
    v2_1_pct = 100.0 * v2_counts[1] / total_steps
    report(f"v2=1 empirical: {v2_1_pct:.1f}% (expected ~50%, tolerance 5%)",
           abs(v2_1_pct - 50.0) < 5.0)

    # Check v2=2 is roughly 25%
    v2_2_pct = 100.0 * v2_counts[2] / total_steps
    report(f"v2=2 empirical: {v2_2_pct:.1f}% (expected ~25%, tolerance 5%)",
           abs(v2_2_pct - 25.0) < 5.0)


# ---------------------------------------------------------------------------
# BONUS: Verify that the transition graph for k=3 has exactly 1 cycle (the fixed point 1)
# ---------------------------------------------------------------------------

def check_bonus_single_cycle():
    section("BONUS: Verify single cycle (fixed point at 1) for k=3")

    modulus = 104
    transitions = {}
    for r in range(modulus):
        if r % 2 == 0:
            continue
        val = 3 * r + 1
        v = val2(val)
        image = (val >> v) % modulus
        transitions[r] = (v, image)

    # Check that r=1 maps to itself: 3*1+1=4, v2(4)=2, 4/4=1
    v_at_1, img_at_1 = transitions[1]
    report(f"Fixed point: Syracuse(1) = 1 (v2={v_at_1}, image={img_at_1})",
           img_at_1 == 1)
    report(f"v2 at fixed point = {v_at_1} (expected 2)", v_at_1 == 2)

    # Find all cycles by following each node
    visited_global = set()
    cycles = []
    for start in transitions:
        if start in visited_global:
            continue
        path = []
        path_set = set()
        node = start
        while node not in visited_global and node not in path_set:
            path.append(node)
            path_set.add(node)
            _, node = transitions[node]
        if node in path_set:
            idx = path.index(node)
            cycle = path[idx:]
            cycles.append(tuple(cycle))
        visited_global.update(path)

    unique_cycles = list(set(cycles))
    report(f"Number of distinct cycles = {len(unique_cycles)} (expected 1)",
           len(unique_cycles) == 1)
    if unique_cycles:
        report(f"The single cycle is {unique_cycles[0]} (expected (1,))",
               unique_cycles[0] == (1,))

    # Verify single connected component (undirected)
    adj = defaultdict(set)
    all_nodes = set(transitions.keys())
    for r, (_, image) in transitions.items():
        adj[r].add(image)
        adj[image].add(r)

    visited = set()
    stack = [1]  # start BFS/DFS from node 1
    while stack:
        node = stack.pop()
        if node in visited:
            continue
        visited.add(node)
        for nb in adj[node]:
            if nb not in visited and nb in all_nodes:
                stack.append(nb)

    report(f"Single connected component: visited {len(visited)} of {len(all_nodes)} nodes",
           len(visited) == len(all_nodes))


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print("=" * 72)
    print("  INDEPENDENT VALIDATION OF COLLATZ ORBIT ANALYSIS")
    print("  All computations done from scratch -- no imports from main script")
    print("=" * 72)

    check1_syracuse_zmod13()
    check2_v2_distribution()
    check3_bad_streaks()
    check4_convergence_window()
    check5_actual_sequences()
    check6_bad_streak_growth()
    check7_statistical_analysis()
    check_bonus_single_cycle()

    print()
    print("=" * 72)
    print(f"  FINAL RESULTS: {PASS_COUNT} PASSED, {FAIL_COUNT} FAILED")
    if FAIL_COUNT == 0:
        print("  ALL CHECKS PASSED")
    else:
        print(f"  WARNING: {FAIL_COUNT} check(s) FAILED -- investigate above")
    print("=" * 72)


if __name__ == "__main__":
    main()
