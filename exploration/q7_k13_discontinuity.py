"""
Q7: The k=13 Discontinuity — Why the Tower Breaks at Meta-Bridge

Diagnoses the k=13 DP divergence and tests the multi-prime tower hypothesis:
  2-tower breaks at k=13 (= ord₁₃(2)+1 = 12+1)
  3-tower breaks at j=4  (= ord₁₃(3)+1 = 3+1)
  5-tower breaks at j=5  (= ord₁₃(5)+1 = 4+1)
  11-tower breaks at j=5 (= ord₁₃(11)+1 = 4+1)
  7-tower breaks at j=13 (= ord₁₃(7)+1 = 12+1) — too large to test
"""

import json
import math
import statistics
from collections import defaultdict

LOG2_3 = math.log2(3)  # ≈ 1.58496

# ---------------------------------------------------------------------------
# Core helpers
# ---------------------------------------------------------------------------

def v2(n):
    if n == 0:
        return -1
    return (n & -n).bit_length() - 1

def build_transition_graph(modulus):
    """
    Odd residues r in [1, modulus) -> (vv, image).
    For EVEN modulus: image is always odd (reduction of an odd integer mod even M).
    For ODD modulus: image may be even or 0 in ZMod(M); skip such residues (domain issue).
    Returns (transitions_dict, skipped_count).
    """
    transitions = {}
    skipped = 0
    for r in range(1, modulus, 2):
        val = 3 * r + 1
        vv = v2(val)
        image = (val >> vv) % modulus
        if modulus % 2 == 1 and image % 2 == 0:
            # Odd modulus: image is even or 0 in ZMod — skip (domain not closed)
            skipped += 1
            continue
        transitions[r] = (vv, image)
    return transitions, skipped

def find_cycles(transitions):
    """
    Find all cycles in the functional graph (deterministic: each node has 1 outgoing edge).
    Returns list of cycles: each cycle is (list_of_residues, avg_v2, avg_drift_millibits).
    """
    visited = {}     # node -> step when first visited
    in_cycle = set() # nodes known to be in a cycle
    cycles = []

    for start in transitions:
        if start in visited:
            continue
        path = []
        path_set = {}
        cur = start
        step = 0
        while cur not in visited and cur not in path_set and cur in transitions:
            path_set[cur] = step
            path.append(cur)
            step += 1
            vv, nxt = transitions[cur]
            cur = nxt

        if cur in path_set:
            # Found a new cycle
            cycle_start_step = path_set[cur]
            cycle = path[cycle_start_step:]
            avg_v2 = statistics.mean(transitions[r][0] for r in cycle)
            avg_drift = 1585 - 1000 * avg_v2
            cycles.append((cycle, avg_v2, avg_drift))
            in_cycle.update(cycle)

        # Mark everything we traversed as visited
        for r in path:
            visited[r] = True
        if cur in transitions and cur not in visited:
            visited[cur] = True

    return cycles

def build_transition_graph_even(modulus):
    """Convenience wrapper for even moduli — always returns clean dict."""
    tr, _ = build_transition_graph(modulus)
    return tr

def graph_reachability(transitions, start):
    """BFS from start. Returns set of reachable nodes."""
    reachable = set()
    queue = [start]
    while queue:
        node = queue.pop()
        if node in reachable:
            continue
        reachable.add(node)
        if node in transitions:
            _, nxt = transitions[node]
            if nxt not in reachable:
                queue.append(nxt)
    return reachable

def v2_distribution(transitions):
    """Count v₂ values across all transitions. Returns dict v2_val -> count."""
    counts = defaultdict(int)
    for r, (vv, img) in transitions.items():
        counts[vv] += 1
    return dict(counts)

def window_dp_integer(transitions, max_window, print_progress=False, modname=""):
    """
    Integer millibit DP. Returns (W_cert, margin) or (None, None) if no cert found.
    Also returns max_drift_at_max_window and worst_residue_at_max_window.
    """
    odd_residues = list(transitions.keys())
    dp = {r: 0 for r in odd_residues}
    W_cert = None
    margin = None

    for w in range(1, max_window + 1):
        dp_next = {}
        for r in odd_residues:
            vv, image = transitions[r]
            # image might not be in dp (skipped residue in odd-modulus towers)
            prev = dp.get(image, 0)
            dp_next[r] = 1585 - 1000 * vv + prev
        dp = dp_next
        max_val = max(dp.values())
        if print_progress and w % 20 == 0:
            worst = max(dp, key=dp.get)
            print(f"    {modname} W={w}: max_drift={max_val}, worst_r={worst}")
        if max_val < 0 and W_cert is None:
            W_cert = w
            margin = -max_val
            break

    worst_r = max(dp, key=dp.get)
    return W_cert, margin, max(dp.values()), worst_r

def trace_orbit(transitions, start, length):
    """Follow the deterministic orbit from start for length steps. Returns list of (r, v₂)."""
    orbit = []
    cur = start
    for _ in range(length):
        vv, nxt = transitions.get(cur, (0, cur))
        orbit.append((cur, vv))
        cur = nxt
    return orbit

# ---------------------------------------------------------------------------
# Part A: Diagnose k=13 divergence
# ---------------------------------------------------------------------------

print("=" * 65)
print("Part A: Diagnosing k=13 Divergence")
print("=" * 65)

for k in [12, 13, 14]:
    M = 13 * (1 << k)
    print(f"\n--- k={k}, modulus={M}, odd residues={M//2} ---")
    transitions, _ = build_transition_graph(M)

    # A1: Graph structure
    cycles = find_cycles(transitions)
    n_odd = len(transitions)

    # Fixed-point check (r=1)
    vv1, img1 = transitions[1]
    fp_ok = (img1 == 1)

    # v₂ distribution
    v2_dist = v2_distribution(transitions)
    max_streak_modular = 0
    # Count streaks by following paths
    for r in transitions:
        run = 0
        cur = r
        seen = set()
        while cur not in seen:
            seen.add(cur)
            vv, nxt = transitions[cur]
            if vv == 1:
                run += 1
                if run > max_streak_modular:
                    max_streak_modular = run
            else:
                run = 0
            cur = nxt

    print(f"  r=1 is fixed point: {fp_ok} (v₂={vv1}, image={img1})")
    print(f"  Number of cycles: {len(cycles)}")
    for i, (cycle, avg_v2, avg_drift) in enumerate(cycles):
        print(f"    Cycle {i+1}: length={len(cycle)}, avg_v₂={avg_v2:.4f}, "
              f"avg_drift={avg_drift:.1f} mb, "
              f"{'DIVERGENT (avg_v₂ < 1.585)' if avg_drift > 0 else 'convergent'}")
        if len(cycle) <= 20:
            print(f"      Residues: {cycle}")
        else:
            print(f"      First/last 5: {cycle[:5]}...{cycle[-5:]}")

    # Reachability from r=1
    reachable_from_1 = graph_reachability(transitions, 1)
    print(f"  Reachable from r=1: {len(reachable_from_1)}/{n_odd} ({100*len(reachable_from_1)/n_odd:.1f}%)")

    # v₂ distribution summary
    total = sum(v2_dist.values())
    print(f"  v₂ distribution: ", end="")
    for vv in sorted(v2_dist.keys())[:8]:
        print(f"v₂={vv}: {100*v2_dist[vv]/total:.1f}%  ", end="")
    print()

# ---------------------------------------------------------------------------
# Part A2: Find and trace the worst path at k=13
# ---------------------------------------------------------------------------

print("\n" + "=" * 65)
print("Part A2: Worst Path at k=13")
print("=" * 65)

k13_M = 13 * (1 << 13)
transitions_13, _ = build_transition_graph(k13_M)

# Find cycles — the divergent one(s)
cycles_13 = find_cycles(transitions_13)
print(f"\nCycles at k=13:")
divergent_cycles = [(c, avg, drift) for c, avg, drift in cycles_13 if drift > 0]
convergent_cycles = [(c, avg, drift) for c, avg, drift in cycles_13 if drift <= 0]
print(f"  Total cycles: {len(cycles_13)}")
print(f"  Divergent (avg_v₂ < 1.585): {len(divergent_cycles)}")
print(f"  Convergent: {len(convergent_cycles)}")

if divergent_cycles:
    print("\nDivergent cycles:")
    for i, (cycle, avg_v2, avg_drift) in enumerate(divergent_cycles):
        print(f"  Cycle {i+1}: length={len(cycle)}, avg_v₂={avg_v2:.6f}, "
              f"avg_drift={avg_drift:.2f} mb/step")
        v2_seq = [transitions_13[r][0] for r in cycle]
        v2_counts = defaultdict(int)
        for vv in v2_seq:
            v2_counts[vv] += 1
        print(f"    v₂ sequence distribution: {dict(sorted(v2_counts.items()))}")
        print(f"    mod-13 residues visited: {sorted(set(r % 13 for r in cycle))}")
        print(f"    mod-169 residues sample: {sorted(set(r % 169 for r in cycle[:20]))}")
        # Show first 20 elements
        if len(cycle) <= 30:
            print(f"    Cycle elements: {cycle}")
        else:
            print(f"    First 10 elements: {cycle[:10]}")

# Run short DP to find worst starting residue at k=13
print(f"\nRunning DP to W=100 at k=13 to find worst starting residue...")
_, _, max_drift_100, worst_r_13 = window_dp_integer(transitions_13, 100)
print(f"  max_drift at W=100: {max_drift_100}")
print(f"  Worst starting residue: {worst_r_13}")
print(f"  worst_r mod 13: {worst_r_13 % 13}")
print(f"  worst_r mod 169: {worst_r_13 % 169}")
print(f"  worst_r mod 104: {worst_r_13 % 104}")

# Trace orbit of worst residue for 50 steps
orbit_50 = trace_orbit(transitions_13, worst_r_13, 50)
avg_v2_orbit = statistics.mean(vv for _, vv in orbit_50)
print(f"\n50-step orbit of worst residue {worst_r_13}:")
print(f"  v₂ sequence: {[vv for _, vv in orbit_50]}")
print(f"  Average v₂: {avg_v2_orbit:.4f} (threshold 1.585)")
print(f"  Average drift per step: {1585 - 1000*avg_v2_orbit:.1f} mb")

# ---------------------------------------------------------------------------
# Part C: Fibonacci prime mod-13 positions
# ---------------------------------------------------------------------------

print("\n" + "=" * 65)
print("Part C: Fibonacci Primes — Position in 13-Cycle")
print("=" * 65)

def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a

# Fibonacci primes: indices are primes
fib_prime_indices = [3, 5, 7, 11, 13, 17, 23, 29, 43, 47, 83, 131, 137]

print(f"\n{'idx':>5s} | {'F(idx)':>15s} | {'idx mod 13':>10s} | {'F(idx) mod 13':>13s} | note")
print("-" * 70)
for idx in fib_prime_indices:
    fn = fib(idx)
    idx_mod13 = idx % 13
    fn_mod13 = fn % 13
    note = ""
    if fn_mod13 == 0:
        note = "← ONLY F(7)=13 itself"
    elif idx == 13:
        note = "← meta-cycle completion"
    elif idx == 7:
        note = "← meta-flip"
    print(f"{idx:>5d} | {fn:>15d} | {idx_mod13:>10d} | {fn_mod13:>13d} | {note}")

# Pattern in F(idx) mod 13:
fn_mod13_seq = [fib(idx) % 13 for idx in fib_prime_indices if idx <= 47]
idx_mod13_seq = [idx % 13 for idx in fib_prime_indices if idx <= 47]
print(f"\nidx mod 13 sequence:    {idx_mod13_seq}")
print(f"F(idx) mod 13 sequence: {fn_mod13_seq}")

# ---------------------------------------------------------------------------
# Part E: Exponent-Period Resonance (2^k mod 13)
# ---------------------------------------------------------------------------

print("\n" + "=" * 65)
print("Part E: Exponent-Period Resonance")
print("=" * 65)

print(f"\n2^k mod 13 for k=0..28 (ord₁₃(2) = 12):")
pow2_mod13 = [pow(2, k, 13) for k in range(29)]
print(f"  {pow2_mod13}")

print(f"\nKey values:")
for k in [12, 13, 24, 25, 26]:
    print(f"  2^{k} ≡ {pow(2,k,13)} (mod 13)  [k mod 12 = {k%12}]")

print(f"\n3^j mod 13 for j=0..8 (ord₁₃(3) = 3):")
pow3_mod13 = [pow(3, j, 13) for j in range(9)]
print(f"  {pow3_mod13}")
for j in [3, 4, 6, 7]:
    print(f"  3^{j} ≡ {pow(3,j,13)} (mod 13)  [j mod 3 = {j%3}]")

print(f"\n5^j mod 13 for j=0..8 (ord₁₃(5) = 4):")
pow5_mod13 = [pow(5, j, 13) for j in range(9)]
print(f"  {pow5_mod13}")
for j in [4, 5, 8, 9]:
    print(f"  5^{j} ≡ {pow(5,min(j,8),13)} (mod 13)  [j mod 4 = {j%4}]")

print(f"\n11^j mod 13 for j=0..8 (ord₁₃(11) = 4):")
pow11_mod13 = [pow(11, j, 13) for j in range(9)]
print(f"  {pow11_mod13}")

print(f"\nResonance table (p, ord₁₃(p), predicted break at j=ord+1):")
primes_and_orders = [(2, 12), (3, 3), (5, 4), (7, 12), (11, 4)]
for p, ord_p in primes_and_orders:
    predicted_break = ord_p + 1
    print(f"  p={p}: ord₁₃(p)={ord_p}, predicted break at j={predicted_break}, "
          f"p^{predicted_break} mod 13 = {pow(p, predicted_break, 13)} ≡ p (mod 13)")

# ---------------------------------------------------------------------------
# Part F: Multi-Prime Towers
# ---------------------------------------------------------------------------

print("\n" + "=" * 65)
print("Part F: Multi-Prime Tower Analysis")
print("=" * 65)

# Orders in (Z/13Z)*:
# ord₁₃(2)=12, ord₁₃(3)=3, ord₁₃(5)=4, ord₁₃(7)=12, ord₁₃(11)=4
# Predicted breaks:
# 2-tower: j=13 (confirmed)
# 3-tower: j=4
# 5-tower: j=5
# 11-tower: j=5
# 7-tower: j=13 (too large)

tower_results = {}

print("\nNOTE: 5-tower and 11-tower use ODD moduli (13×5^j, 13×11^j).")
print("  For odd M, (3r+1)/2^v₂ mod M may be even, so the domain of odd residues")
print("  is NOT closed. These towers are skipped; 3-tower uses odd M but mostly works.")
print("  The mixed-modulus approach (13×2^k×p^j) was tested in Q1 and diverges at j=1.")

for base_prime, ord_p, max_j in [(3, 3, 7)]:
    print(f"\n--- {base_prime}-tower (ord₁₃({base_prime})={ord_p}, predicted break at j={ord_p+1}) ---")
    tower_results[base_prime] = []

    for j in range(1, max_j + 1):
        M = 13 * (base_prime ** j)

        if M > 2_000_000:
            print(f"  j={j}: M={M}, too large — skipping")
            tower_results[base_prime].append({
                "j": j, "modulus": M, "skipped": True,
                "predicted_break": j == ord_p + 1
            })
            continue

        tr, n_skipped = build_transition_graph(M)
        n_in_domain = len(tr)
        print(f"  j={j}: M={M}, in-domain odd residues={n_in_domain} "
              f"(skipped {n_skipped} with even image)")

        # Graph diagnostics
        cycs = find_cycles(tr)
        div_cycs = [(c, avg, drift) for c, avg, drift in cycs if drift > 0]

        # DP (only if domain is reasonably closed)
        max_w = 200
        W_cert, margin, max_drift_end, worst_r = window_dp_integer(
            tr, max_w, print_progress=(j == ord_p + 1), modname=f"{base_prime}^{j}"
        )

        predicted_break = (j == ord_p + 1)
        status = "W=None (DIVERGES)" if W_cert is None else f"W={W_cert} margin={margin}"
        mark = " ← PREDICTED BREAK" if predicted_break else ""
        print(f"    cycles={len(cycs)} (divergent={len(div_cycs)}), {status}{mark}")
        if div_cycs:
            for c, avg, drift in div_cycs:
                print(f"      divergent cycle: length={len(c)}, avg_v₂={avg:.4f}")

        tower_results[base_prime].append({
            "j": j,
            "modulus": M,
            "n_odd": n_in_domain,
            "n_cycles": len(cycs),
            "n_divergent_cycles": len(div_cycs),
            "W_k": W_cert,
            "margin": margin,
            "max_drift_at_maxW": max_drift_end,
            "predicted_break": predicted_break,
            "skipped": False,
        })

# Also verify 2-tower at k=12,13,14 using same cycle analysis (Part A already did this)

# Summary table for F
print("\n\nSummary: Multi-Prime Tower Results")
print(f"{'prime':>6s} | {'j':>3s} | {'modulus':>10s} | {'cycles':>6s} | {'div_cyc':>7s} | {'W(j)':>6s} | {'predicted_break':>15s}")
print("-" * 75)

# 2-tower results from Q5
w_k_q5 = {3:10, 4:22, 5:26, 6:42, 7:52, 8:54, 9:59, 10:78, 11:84, 12:80, 13:None, 14:90, 15:108}
for k in [11, 12, 13, 14]:
    M = 13 * (1 << k)
    predicted = (k == 13)
    print(f"{'2':>6s} | {k:>3d} | {M:>10d} | {'?':>6s} | {'?':>7s} | {str(w_k_q5.get(k)):>6s} | "
          f"{'← CONFIRMED' if predicted else '':>15s}")

for p in [3]:
    for row in tower_results[p]:
        if row.get('skipped'):
            continue
        pred_str = '← CONFIRMED' if row['W_k'] is None and row['predicted_break'] else \
                   '← WRONG' if row['W_k'] is not None and row['predicted_break'] else ''
        print(f"{p:>6d} | {row['j']:>3d} | {row['modulus']:>10d} | {row['n_cycles']:>6d} | "
              f"{row['n_divergent_cycles']:>7d} | {str(row['W_k']):>6s} | {pred_str:>15s}")

# Coprimality of break points
print("\n\nPart F3: Coprimality of predicted break points")
import math as _math
break_points = [(2, 13), (3, 4), (5, 5), (11, 5)]
for i in range(len(break_points)):
    for j_idx in range(i+1, len(break_points)):
        p1, b1 = break_points[i]
        p2, b2 = break_points[j_idx]
        g = _math.gcd(b1, b2)
        print(f"  gcd(break({p1})={b1}, break({p2})={b2}) = {g} {'✓ COPRIME' if g==1 else '✗ NOT COPRIME'}")

# ---------------------------------------------------------------------------
# Save results
# ---------------------------------------------------------------------------

# Cycles at k=13 (already computed above)
cycles_13_save = []
for c, avg, drift in cycles_13:
    v2_seq = [transitions_13[r][0] for r in c]
    v2_counts = defaultdict(int)
    for vv in v2_seq:
        v2_counts[vv] += 1
    cycles_13_save.append({
        "length": len(c),
        "avg_v2": round(avg, 6),
        "avg_drift_mb": round(drift, 2),
        "divergent": drift > 0,
        "v2_distribution": {str(k): v for k, v in sorted(v2_counts.items())},
        "mod13_residues_visited": sorted(set(r % 13 for r in c)),
        "first_10_elements": c[:10],
    })

results = {
    "part_A1_k12_cycles": [],   # populated below
    "part_A1_k13_cycles": cycles_13_save,
    "part_A1_k14_cycles": [],   # populated below
    "part_A2_worst_residue_k13": {
        "residue": worst_r_13,
        "mod_13": worst_r_13 % 13,
        "mod_169": worst_r_13 % 169,
        "mod_104": worst_r_13 % 104,
        "avg_v2_50steps": round(avg_v2_orbit, 6),
        "avg_drift_mb_50steps": round(1585 - 1000*avg_v2_orbit, 2),
        "v2_sequence_50steps": [vv for _, vv in orbit_50],
    },
    "part_C_fibonacci_mod13": [
        {"index": idx, "prime": fib(idx), "idx_mod13": idx % 13, "prime_mod13": fib(idx) % 13}
        for idx in fib_prime_indices if idx <= 47
    ],
    "part_E_resonance": {
        "ord_13_of_2": 12,
        "ord_13_of_3": 3,
        "ord_13_of_5": 4,
        "ord_13_of_7": 12,
        "ord_13_of_11": 4,
        "2_pow_k_mod13": {str(k): pow(2,k,13) for k in range(29)},
        "3_pow_j_mod13": {str(j): pow(3,j,13) for j in range(9)},
        "5_pow_j_mod13": {str(j): pow(5,j,13) for j in range(9)},
        "predicted_breaks": {str(p): ord_p+1 for p, ord_p in primes_and_orders},
    },
    "part_F_tower_results": {
        "3": tower_results.get(3, []),
        "5_and_11": "skipped_odd_modulus_domain_issue",
    },
    "part_F3_coprimality": {
        f"gcd_break_{p1}_{p2}": _math.gcd(b1, b2)
        for (p1, b1), (p2, b2) in [
            ((2,13),(3,4)), ((2,13),(5,5)), ((2,13),(11,5)),
            ((3,4),(5,5)), ((3,4),(11,5)), ((5,5),(11,5))
        ]
    }
}

# Populate k=12 and k=14 cycle data (from Part A loops above)
# We re-run briefly just for the save
for k, key in [(12, "part_A1_k12_cycles"), (14, "part_A1_k14_cycles")]:
    M = 13 * (1 << k)
    tr, _ = build_transition_graph(M)
    cycs = find_cycles(tr)
    results[key] = [
        {
            "length": len(c), "avg_v2": round(avg, 6),
            "avg_drift_mb": round(drift, 2), "divergent": drift > 0
        }
        for c, avg, drift in cycs
    ]

with open('exploration/q7_results.json', 'w') as f:
    json.dump(results, f, indent=2)

print("\nResults saved to exploration/q7_results.json")
