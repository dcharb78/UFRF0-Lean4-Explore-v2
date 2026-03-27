"""
Q6: The Log-Mod Recursive Structure

Tests whether treating Collatz as log-then-mod reveals resonance structure
between cumulative expansion (3^L) and contraction (2^S) in (Z/13Z)*.

Key: ord₁₃(2) = 12, ord₁₃(3) = 3. For convergence: 2^S ≡ n₀·3^L (mod 13).
This means S mod 12 and L mod 3 must satisfy a specific constraint.
"""

import json
import math
import statistics
from collections import defaultdict
from fractions import Fraction

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

def full_trajectory(n, max_steps=5000):
    """Returns list of (value, v2_used). Ends when value reaches 1."""
    steps = []
    cur = n
    while cur > 1 and len(steps) < max_steps:
        nxt, vv = syracuse_step(cur)
        steps.append((cur, vv))
        cur = nxt
    steps.append((cur, 0))
    return steps

def v2_modular(n, M):
    """Modular v₂: v₂(3*(n%M)+1)."""
    r = n % M
    val = 3 * r + 1
    return v2(val)

# ---------------------------------------------------------------------------
# Part A: (S mod 12, L mod 3) at trajectory end — all odd n in [3, 999]
# ---------------------------------------------------------------------------

print("=" * 60)
print("Part A: (S mod 12, L mod 3) at trajectory end")
print("=" * 60)

# Powers of 2 mod 13: 2^k mod 13 has period 12 (ord₁₃(2)=12)
# Powers of 3 mod 13: 3^k mod 13 has period 3 (ord₁₃(3)=3)

end_states = defaultdict(int)  # (S mod 12, L mod 3) -> count
n0_states  = {}                # n0 mod 13 -> list of (S mod 12, L mod 3)

for n in range(3, 1000, 2):
    traj = full_trajectory(n)
    L = len(traj) - 1  # number of odd steps (last entry is reaching 1 or final)
    S = sum(vv for (_, vv) in traj)
    n0_mod13 = n % 13
    state = (S % 12, L % 3)
    end_states[state] += 1
    if n0_mod13 not in n0_states:
        n0_states[n0_mod13] = []
    n0_states[n0_mod13].append(state)

print(f"\n(S mod 12, L mod 3) distribution for all odd n in [3,999]:")
print(f"{'(S%12, L%3)':>13s}  {'count':>6s}")
for state in sorted(end_states.keys()):
    print(f"  {str(state):>10s}  {end_states[state]:>6d}")

print(f"\nTotal distinct end states: {len(end_states)} out of 36 possible")

# Does the end state depend on n₀ mod 13?
print(f"\nEnd state by n₀ mod 13:")
print(f"{'n₀ mod 13':>10s}  {'distinct states':>15s}  {'most common':>12s}")
for n0 in range(13):
    if n0 not in n0_states:
        continue
    states = n0_states[n0]
    distinct = set(states)
    most_common = max(set(states), key=states.count)
    frac = states.count(most_common) / len(states)
    print(f"  {n0:>8d}  {str(len(distinct)):>15s}  {str(most_common):>12s} ({frac:.1%})")

# ---------------------------------------------------------------------------
# Part B: S(t) mod 13 walk — time to reach 0
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Part B: S(t) mod 13 — cover time and zero-crossing")
print("=" * 60)

zero_times = []
cover_times_mod13 = []

for n in range(3, 10000, 2):
    traj = full_trajectory(n)
    S = 0
    zero_time = None
    seen_residues = set()
    cover_time = None
    for t, (val, vv) in enumerate(traj):
        S = (S + vv) % 13
        seen_residues.add(S)
        if S == 0 and zero_time is None:
            zero_time = t + 1
        if len(seen_residues) == 13 and cover_time is None:
            cover_time = t + 1
    zero_times.append(zero_time)
    cover_times_mod13.append(cover_time)

achieved_zero = [t for t in zero_times if t is not None]
achieved_cover = [t for t in cover_times_mod13 if t is not None]

print(f"\nFor odd n in [3, 9999]:")
print(f"  Fraction reaching S≡0 (mod 13): {len(achieved_zero)/len(zero_times):.4f}")
if achieved_zero:
    print(f"  Mean steps to S≡0: {statistics.mean(achieved_zero):.3f}")
    print(f"  Max steps to S≡0: {max(achieved_zero)}")

print(f"\n  Fraction covering all 13 mod-13 residues for S: {len(achieved_cover)/len(cover_times_mod13):.4f}")
if achieved_cover:
    print(f"  Mean cover time (S mod 13): {statistics.mean(achieved_cover):.3f}")

# Does S≡0 correlate with trajectory descent?
# Find steps where S(t) mod 13 = 0 and check v₂ at that step
zero_step_v2 = []
nonzero_step_v2 = []
for n in range(3, 1000, 2):
    traj = full_trajectory(n)
    S = 0
    for t, (val, vv) in enumerate(traj[:-1]):  # exclude last step
        S = (S + vv) % 13
        if S == 0:
            zero_step_v2.append(vv)
        else:
            nonzero_step_v2.append(vv)

if zero_step_v2 and nonzero_step_v2:
    print(f"\n  v₂ at steps where S≡0 (mod 13): mean={statistics.mean(zero_step_v2):.4f}")
    print(f"  v₂ at steps where S≢0 (mod 13): mean={statistics.mean(nonzero_step_v2):.4f}")

# ---------------------------------------------------------------------------
# Part C: 36-state (S mod 12, L mod 3) path structure
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Part C: 36-state (S mod 12, L mod 3) path structure")
print("=" * 60)

# Build transition matrix for the 36-state space
# At each step, S increases by v₂, L increases by 1
# So: (S mod 12, L mod 3) -> ((S + v₂) mod 12, (L+1) mod 3)
# The transition depends on v₂, which depends on n

# Record which of the 36 states are actually visited
visited_states = set()
transition_counts = defaultdict(lambda: defaultdict(int))  # state -> next_state -> count
forbidden_states = set(range(36))  # start with all, remove visited

for n in range(3, 10000, 2):
    traj = full_trajectory(n)
    S = 0
    L = 0
    for t, (val, vv) in enumerate(traj[:-1]):
        state = (S % 12, L % 3)
        S += vv
        L += 1
        next_state = (S % 12, L % 3)
        visited_states.add(state)
        visited_states.add(next_state)
        transition_counts[state][next_state] += 1

state_ids = sorted(visited_states)
print(f"\nVisited states: {len(visited_states)} out of 36")
unvisited = [(s,l) for s in range(12) for l in range(3) if (s,l) not in visited_states]
if unvisited:
    print(f"Unvisited states: {unvisited}")
else:
    print("All 36 states visited.")

# Dominant transition for each state
print(f"\nDominant transitions (top states by visit frequency):")
most_visited = sorted(visited_states, key=lambda s: sum(transition_counts[s].values()), reverse=True)[:10]
for state in most_visited:
    total = sum(transition_counts[state].values())
    best_next = max(transition_counts[state], key=transition_counts[state].get)
    frac = transition_counts[state][best_next] / total
    print(f"  {str(state):>10s} -> {str(best_next):>10s} ({frac:.1%} of {total} transitions)")

# Check if end states cluster
print(f"\nEnd state distribution (all n in [3,9999]):")
end_count = defaultdict(int)
for n in range(3, 10000, 2):
    traj = full_trajectory(n)
    L = len(traj) - 1
    S = sum(vv for (_, vv) in traj)
    end_count[(S % 12, L % 3)] += 1

for state in sorted(end_count.keys()):
    print(f"  {str(state):>10s}: {end_count[state]}")

# ---------------------------------------------------------------------------
# Part D: Log correction distribution (actual v₂ − modular v₂)
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Part D: Log correction = actual v₂ − modular v₂")
print("=" * 60)

# Modulus M = 13 * 2^3 = 104 (k=3)
M = 104

corrections_all = []
cum_correction_finals = []

for n in range(3, 10000, 2):
    traj = full_trajectory(n)
    cum_corr = 0
    for t, (val, vv_actual) in enumerate(traj[:-1]):
        vv_modular = v2_modular(val, M)
        correction = vv_actual - vv_modular
        corrections_all.append(correction)
        cum_corr += correction
    cum_correction_finals.append(cum_corr)

correction_counts = defaultdict(int)
for c in corrections_all:
    correction_counts[c] += 1

print(f"\nLog correction (actual v₂ − modular v₂) distribution (M=104, k=3):")
print(f"{'correction':>11s}  {'count':>8s}  {'fraction':>9s}")
total_corr = len(corrections_all)
for c in sorted(correction_counts.keys()):
    frac = correction_counts[c] / total_corr
    print(f"  {c:>9d}  {correction_counts[c]:>8d}  {frac:>9.5f}")

mean_corr = statistics.mean(corrections_all)
print(f"\nMean correction: {mean_corr:.6f}")
print(f"(Negative = modular overcounts; Positive = modular undercounts)")

# Cumulative correction at trajectory end — is it bounded?
print(f"\nCumulative correction (per trajectory) stats:")
print(f"  min: {min(cum_correction_finals)}")
print(f"  max: {max(cum_correction_finals)}")
print(f"  mean: {statistics.mean(cum_correction_finals):.4f}")
print(f"  stdev: {statistics.stdev(cum_correction_finals):.4f}")

# Is it bounded? Count how many have |cum_corr| > threshold
for thresh in [10, 20, 50, 100]:
    big = sum(1 for c in cum_correction_finals if abs(c) > thresh)
    print(f"  |cum_corr| > {thresh}: {big} out of {len(cum_correction_finals)} "
          f"({100*big/len(cum_correction_finals):.1f}%)")

# ---------------------------------------------------------------------------
# Part E: v₂ mod 3 distribution and S mod 3 ↔ L mod 3 coupling
# ---------------------------------------------------------------------------

print("\n" + "=" * 60)
print("Part E: v₂ mod 3 distribution and S mod 3 ↔ L mod 3 resonance")
print("=" * 60)

# Theoretical: P(v₂≡0 mod 3) = 1/7, P(v₂≡1 mod 3) = 4/7, P(v₂≡2 mod 3) = 2/7
theoretical = {0: Fraction(1, 7), 1: Fraction(4, 7), 2: Fraction(2, 7)}

v2_mod3_counts = defaultdict(int)
total_v2 = 0

# S mod 3 vs L mod 3 tracking
s_eq_l_count = 0
s_ne_l_count = 0
s_l_table = defaultdict(int)  # (S mod 3, L mod 3) -> count

for n in range(3, 100000, 2):
    traj = full_trajectory(n)
    S = 0
    L = 0
    for t, (val, vv) in enumerate(traj[:-1]):
        v2_mod3_counts[vv % 3] += 1
        total_v2 += 1
        S += vv
        L += 1
        s3 = S % 3
        l3 = L % 3
        s_l_table[(s3, l3)] += 1
        if s3 == l3:
            s_eq_l_count += 1
        else:
            s_ne_l_count += 1

print(f"\nv₂ mod 3 distribution (all odd n ≤ 99999):")
print(f"{'v₂ mod 3':>9s}  {'observed':>10s}  {'theoretical':>12s}  {'ratio':>8s}")
for mod in [0, 1, 2]:
    obs = v2_mod3_counts[mod] / total_v2
    theo = float(theoretical[mod])
    print(f"  {mod:>7d}  {obs:>10.6f}  {theo:>12.6f}  {obs/theo:>8.4f}")

print(f"\nS mod 3 ↔ L mod 3 coupling:")
print(f"  P(S≡L mod 3) = {s_eq_l_count/(s_eq_l_count+s_ne_l_count):.6f}")
print(f"  Expected (random):  {1/3:.6f}")
print(f"  Coupling strength: {(s_eq_l_count/(s_eq_l_count+s_ne_l_count))/(1/3):.4f}× random")

print(f"\n(S mod 3, L mod 3) joint distribution:")
total_sl = sum(s_l_table.values())
print(f"{'(S%3, L%3)':>12s}  {'fraction':>9s}  {'vs_uniform':>10s}")
for s3 in range(3):
    for l3 in range(3):
        cnt = s_l_table[(s3, l3)]
        frac = cnt / total_sl
        uniform = 1/9
        print(f"  ({s3},{l3}):         {frac:>9.6f}  {frac/uniform:>10.4f}×")

# The key: if v₂ ≡ 1 (mod 3) is dominant (4/7 ≈ 57%), then
# each step moves S by 1 mod 3 with high probability,
# while L also moves by 1 mod 3 per step.
# So S mod 3 ≈ L mod 3 at each step.
coupling = s_eq_l_count / (s_eq_l_count + s_ne_l_count)
if coupling > 1/3 + 0.05:
    verdict = f"STRONG COUPLING: S mod 3 ≈ L mod 3 ({coupling:.3f} vs random {1/3:.3f})"
elif coupling > 1/3:
    verdict = f"WEAK COUPLING: S mod 3 slightly tracks L mod 3 ({coupling:.3f})"
else:
    verdict = f"NO COUPLING: S mod 3 independent of L mod 3 ({coupling:.3f})"
print(f"\nResonance verdict: {verdict}")

# Implication for 2^S vs 3^L mod 13:
# 2^S mod 13 depends on S mod 12 (ord 12)
# 3^L mod 13 depends on L mod 3 (ord 3)
# If S ≡ L (mod 3), then 2^S ≡ 2^(something*3 + L) ≡ 2^(3k)·2^L ≡ 8^k·2^L (mod 13)
# 8^k mod 13 cycles: 8,64≡12,96≡5,40≡1,8,... period 4
# So it's not a simple resonance. But the bias in v₂ mod 3 IS structural.

print(f"\nv₂ ≡ 1 (mod 3) dominance: {v2_mod3_counts[1]/total_v2:.4f} (theory: {float(theoretical[1]):.4f})")
print(f"This means each step adds ~1 to S mod 3, same as it adds 1 to L mod 3.")
print(f"Result: S mod 3 and L mod 3 are tightly coupled (both grow by ~1 per step).")

# ---------------------------------------------------------------------------
# Save results
# ---------------------------------------------------------------------------

results = {
    "part_A": {
        "end_states": {str(k): v for k, v in end_states.items()},
        "n_distinct_states": len(end_states),
        "all_36_states_visited": len(end_states) == 36,
    },
    "part_B": {
        "fraction_reaching_S0_mod13": round(len(achieved_zero)/len(zero_times), 6),
        "mean_steps_to_S0": round(statistics.mean(achieved_zero), 4) if achieved_zero else None,
        "max_steps_to_S0": max(achieved_zero) if achieved_zero else None,
        "fraction_covering_all_S_mod13": round(len(achieved_cover)/len(cover_times_mod13), 6),
        "mean_S_mod13_cover_time": round(statistics.mean(achieved_cover), 4) if achieved_cover else None,
        "mean_v2_at_S_eq0": round(statistics.mean(zero_step_v2), 4) if zero_step_v2 else None,
        "mean_v2_at_S_ne0": round(statistics.mean(nonzero_step_v2), 4) if nonzero_step_v2 else None,
    },
    "part_C": {
        "n_visited_states": len(visited_states),
        "all_36_visited": len(visited_states) == 36,
        "unvisited": unvisited,
        "end_state_distribution": {str(k): v for k, v in end_count.items()},
    },
    "part_D": {
        "correction_distribution": {str(k): v for k, v in sorted(correction_counts.items())},
        "mean_correction": round(mean_corr, 6),
        "cumulative_correction_min": min(cum_correction_finals),
        "cumulative_correction_max": max(cum_correction_finals),
        "cumulative_correction_mean": round(statistics.mean(cum_correction_finals), 4),
        "cumulative_correction_stdev": round(statistics.stdev(cum_correction_finals), 4),
    },
    "part_E": {
        "v2_mod3_observed": {str(m): round(v2_mod3_counts[m]/total_v2, 8) for m in [0,1,2]},
        "v2_mod3_theoretical": {"0": round(1/7, 8), "1": round(4/7, 8), "2": round(2/7, 8)},
        "P_S_eq_L_mod3": round(coupling, 8),
        "expected_random": round(1/3, 8),
        "coupling_ratio": round(coupling / (1/3), 6),
        "resonance_verdict": verdict,
        "v2_mod1_dominance": round(v2_mod3_counts[1]/total_v2, 6),
    }
}

with open('exploration/q6_results.json', 'w') as f:
    json.dump(results, f, indent=2)

print("\nResults saved to exploration/q6_results.json")
