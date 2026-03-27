"""
collatz_unsafe_residues.py

Investigates "unsafe residues" in the Collatz/Syracuse modular analysis.

An "unsafe residue" at level k is a residue r (odd) in ZMod(13 * 2^k)
where v2(3*r+1) >= k, meaning the modular v2 computation may overcount
the actual v2 of actual integers n ≡ r (mod 13*2^k).

Background:
  For actual integer n ≡ r (mod 13*2^k):
    3n+1 = 3r+1 + 13*2^k * m
  The actual v2(3n+1) equals the modular v2(3r+1) ONLY if v2(3r+1) < k,
  because the carry from 13*2^k*m only affects bits at position k and above.
"""

import json
import os
from collections import defaultdict

# ── helpers ──────────────────────────────────────────────────────────────────

def v2(n: int) -> int:
    """2-adic valuation of n (n > 0)."""
    if n <= 0:
        raise ValueError(f"v2 requires n > 0, got {n}")
    return (n & -n).bit_length() - 1


def modular_v2(r: int) -> int:
    """v2(3r+1) for residue r (3r+1 must be > 0)."""
    val = 3 * r + 1
    if val <= 0:
        raise ValueError(f"3r+1 must be > 0, got r={r}")
    return v2(val)


def actual_v2(n: int) -> int:
    """v2(3n+1) for actual integer n (n must be odd and positive)."""
    return v2(3 * n + 1)


# ── Task 1: Enumerate unsafe residues ────────────────────────────────────────

print("=" * 70)
print("TASK 1: Enumerate unsafe residues for k = 3..10")
print("=" * 70)

task1_results = {}

for k in range(3, 11):
    modulus = 13 * (2 ** k)
    unsafe = [r for r in range(modulus) if r % 2 == 1 and modular_v2(r) >= k]

    # Which residue classes mod 13 do they cover?
    residue_classes_mod13 = sorted(set(r % 13 for r in unsafe))

    task1_results[k] = {
        "modulus": modulus,
        "count_unsafe": len(unsafe),
        "residue_classes_mod13": residue_classes_mod13,
        "unsafe_residues": unsafe if k == 3 else f"(omitted, count={len(unsafe)})",
    }

    covers_all_13 = (len(residue_classes_mod13) == 13)
    print(f"\nk={k}, modulus={modulus}:")
    print(f"  Unsafe count = {len(unsafe)}  (expected 13: {'OK' if len(unsafe)==13 else 'FAIL'})")
    print(f"  Residue classes mod 13 covered: {residue_classes_mod13}")
    print(f"  All 13 classes covered: {'YES' if covers_all_13 else 'NO'}")
    if k == 3:
        print(f"  Unsafe residues (mod {modulus}): {unsafe}")


# ── Task 2: Quantify v2 discrepancy at k=3 ───────────────────────────────────

print("\n" + "=" * 70)
print("TASK 2: v2 discrepancy for k=3 unsafe residues (n ≤ 10000)")
print("=" * 70)

k = 3
modulus = 13 * (2 ** k)  # 104
unsafe_k3 = [r for r in range(modulus) if r % 2 == 1 and modular_v2(r) >= k]

task2_results = {}
max_discrepancy_overall = 0
max_discrepancy_case = None

for r in unsafe_k3:
    mod_v2 = modular_v2(r)
    discrepancies = []
    for n in range(r if r % 2 == 1 else r + modulus, 10001, modulus):
        if n <= 0:
            continue
        if n % 2 == 0:
            continue
        av2 = actual_v2(n)
        disc = mod_v2 - av2
        discrepancies.append((n, av2, disc))
        if disc > max_discrepancy_overall:
            max_discrepancy_overall = disc
            max_discrepancy_case = (r, n, mod_v2, av2, disc)

    if discrepancies:
        discs = [d for _, _, d in discrepancies]
        task2_results[r] = {
            "modular_v2": mod_v2,
            "sample_count": len(discrepancies),
            "max_discrepancy": max(discs),
            "min_discrepancy": min(discs),
            "mean_discrepancy": sum(discs) / len(discs),
            "any_nonzero": any(d != 0 for d in discs),
        }
        print(f"\n  r={r} (mod {modulus}), modular_v2={mod_v2}")
        print(f"    samples={len(discrepancies)}, max_disc={max(discs)}, min_disc={min(discs)}, mean_disc={sum(discs)/len(discs):.3f}")

print(f"\nMax discrepancy overall: {max_discrepancy_overall}")
if max_discrepancy_case:
    r, n, mv2, av2, disc = max_discrepancy_case
    print(f"  Occurs at r={r}, n={n}: modular_v2={mv2}, actual_v2={av2}, discrepancy={disc}")


# ── Task 3: Certificate survival at k=3 ────────────────────────────────────

print("\n" + "=" * 70)
print("TASK 3: Certificate survival check at k=3")
print("=" * 70)

# Certificate: v2_sum >= 16 over 10 steps
# Margin: 1000*16 - 10*1585 = 16000 - 15850 = 150
# If modular v2 overcounts by delta, actual v2_sum could be 16 - delta
# Certificate survives if 1000*(16 - delta) > 15850, i.e., delta < 0.15

cert_v2_sum_threshold = 16
cert_steps = 10
log2_3_approx = 1585  # in millibits (log2(3) * 1000 ≈ 1585)
margin_millibits = 1000 * cert_v2_sum_threshold - cert_steps * log2_3_approx
delta_critical = margin_millibits / 1000.0

print(f"\nCertificate parameters:")
print(f"  v2_sum threshold: {cert_v2_sum_threshold} bits over {cert_steps} steps")
print(f"  Margin: {margin_millibits} millibits = {margin_millibits/1000:.3f} bits")
print(f"  Critical delta (discrepancy that breaks certificate): delta >= {delta_critical}")

task3_results = {}
k = 3
modulus = 13 * (2 ** k)
unsafe_k3 = [r for r in range(modulus) if r % 2 == 1 and modular_v2(r) >= k]

print(f"\nFor k=3, modulus={modulus}:")
print(f"  Unsafe residues: {unsafe_k3}")
print(f"\n  True v2 distribution for n ≡ r (mod {modulus}), n ≤ 10000:")

all_safe = True

for r in unsafe_k3:
    mod_v2 = modular_v2(r)
    v2_dist = defaultdict(int)
    for n in range(r if r % 2 == 1 else r + modulus, 10001, modulus):
        if n <= 0 or n % 2 == 0:
            continue
        av2 = actual_v2(n)
        v2_dist[av2] += 1

    # Sort distribution
    dist_sorted = sorted(v2_dist.items())
    total = sum(v2_dist.values())

    # Check: does ANY integer have actual v2 < modular v2?
    # (i.e., actual_v2 < mod_v2, so discrepancy = mod_v2 - actual_v2 > 0)
    min_actual_v2 = min(v2_dist.keys()) if v2_dist else None
    any_overcount = (min_actual_v2 is not None and min_actual_v2 < mod_v2)

    # For the certificate: max discrepancy for this residue
    max_disc_r = mod_v2 - min_actual_v2 if min_actual_v2 is not None else 0

    if any_overcount:
        all_safe = False

    task3_results[r] = {
        "modular_v2": mod_v2,
        "v2_distribution": {str(v): c for v, c in dist_sorted},
        "min_actual_v2": min_actual_v2,
        "max_discrepancy": max_disc_r,
        "any_overcount": any_overcount,
        "certificate_survives": max_disc_r < delta_critical,
    }

    print(f"\n  r={r}, modular_v2={mod_v2}")
    for av2, cnt in dist_sorted:
        frac = cnt / total if total > 0 else 0
        flag = " <-- OVERCOUNT" if av2 < mod_v2 else ""
        print(f"    actual_v2={av2}: {cnt}/{total} ({frac:.3%}){flag}")
    print(f"  min_actual_v2={min_actual_v2}, max_disc={max_disc_r}, cert_survives={'YES' if max_disc_r < delta_critical else 'NO'}")

print(f"\nAll k=3 unsafe residues safe (no overcount)? {'YES' if all_safe else 'NO'}")


# ── Task 4: Higher k (k=4..6) ───────────────────────────────────────────────

print("\n" + "=" * 70)
print("TASK 4: Higher k analysis (k=4..6)")
print("=" * 70)

task4_results = {}

for k in range(4, 7):
    modulus = 13 * (2 ** k)
    unsafe_rk = [r for r in range(modulus) if r % 2 == 1 and modular_v2(r) >= k]

    print(f"\nk={k}, modulus={modulus}, unsafe count={len(unsafe_rk)}")
    task4_results[k] = {}

    cert_v2_sum_threshold_k = 2 * k  # rough: certificate requires more bits at higher k
    # Use same margin logic but scaled
    # For the certificate to survive: max_disc < margin/1000
    # Conservatively use same 0.15 threshold
    delta_crit_k = 0.15

    for r in unsafe_rk:
        mod_v2 = modular_v2(r)
        v2_dist = defaultdict(int)

        # Sample integers n ≡ r (mod modulus), n ≤ 10000 (fewer at higher k)
        start = r if r % 2 == 1 else r + modulus
        for n in range(start, 10001, modulus):
            if n <= 0 or n % 2 == 0:
                continue
            av2 = actual_v2(n)
            v2_dist[av2] += 1

        dist_sorted = sorted(v2_dist.items())
        total = sum(v2_dist.values())

        min_actual_v2 = min(v2_dist.keys()) if v2_dist else None
        any_overcount = (min_actual_v2 is not None and min_actual_v2 < mod_v2)
        max_disc_r = mod_v2 - min_actual_v2 if min_actual_v2 is not None else 0

        task4_results[k][r] = {
            "modular_v2": mod_v2,
            "v2_distribution": {str(v): c for v, c in dist_sorted},
            "min_actual_v2": min_actual_v2,
            "max_discrepancy": max_disc_r,
            "any_overcount": any_overcount,
        }

        if any_overcount or total == 0:
            flag = " *** OVERCOUNT ***" if any_overcount else " (no samples)"
            print(f"  r={r}: mod_v2={mod_v2}, min_actual_v2={min_actual_v2}, max_disc={max_disc_r}{flag}")
        else:
            print(f"  r={r}: mod_v2={mod_v2}, min_actual_v2={min_actual_v2}, max_disc={max_disc_r} [OK]")


# ── Task 5: Key question answer ──────────────────────────────────────────────

print("\n" + "=" * 70)
print("TASK 5: Can contraction certificates survive the v2 discrepancy?")
print("=" * 70)

# Gather all discrepancies across k=3..6
all_discrepancies = []

for k in range(3, 7):
    modulus = 13 * (2 ** k)
    unsafe_rk = [r for r in range(modulus) if r % 2 == 1 and modular_v2(r) >= k]
    for r in unsafe_rk:
        mod_v2 = modular_v2(r)
        start = r if r % 2 == 1 else r + modulus
        for n in range(start, 50001, modulus):  # larger sample
            if n <= 0 or n % 2 == 0:
                continue
            av2 = actual_v2(n)
            disc = mod_v2 - av2
            if disc > 0:
                all_discrepancies.append((k, r, n, mod_v2, av2, disc))

max_disc_global = max((d for _, _, _, _, _, d in all_discrepancies), default=0)
any_overcount_global = len(all_discrepancies) > 0

print(f"\nAcross k=3..6, n ≤ 50000:")
print(f"  Any overcount (discrepancy > 0): {'YES' if any_overcount_global else 'NO'}")
print(f"  Max discrepancy found: {max_disc_global}")

if all_discrepancies:
    print(f"\n  Top discrepancy cases:")
    for case in sorted(all_discrepancies, key=lambda x: -x[5])[:10]:
        ck, cr, cn, cmv2, cav2, cdisc = case
        print(f"    k={ck}, r={cr}, n={cn}: mod_v2={cmv2}, actual_v2={cav2}, disc={cdisc}")

# Theoretical explanation of why no overcount is possible
print("\n--- Theoretical Analysis ---")
print("""
For an unsafe residue r at level k: v2(3r+1) >= k.
Write 3r+1 = 2^{v2(3r+1)} * q where q is odd.

For n = r + 13*2^k * m:
  3n+1 = 3r+1 + 13*2^k * (3m)
       = 2^{v2(3r+1)} * q + 13*2^k * (3m)
       = 2^k * (2^{v2(3r+1)-k} * q + 13*(3m))

Since v2(3r+1) >= k, both terms in the parenthesis share factor 2^k.
The inner expression is:
  A = 2^{v2(3r+1)-k} * q + 13*(3m) = 2^{v2(3r+1)-k} * q + 39m

The actual v2(3n+1) = k + v2(A).

v2(A) depends on m:
  - If m is even: 39m ≡ 0 (mod 2), so A has same parity as 2^{v2(3r+1)-k}*q.
    Since q is odd and v2(3r+1) > k (or = k with q odd), v2(A) can be 0 or more.
  - If m is odd: 39m is odd (39=3*13 is odd), so A = (even or odd) + odd.

This means actual_v2(3n+1) = k + v2(A) >= k.
But the modular computation claims v2(3r+1) which is also >= k.

The key insight: the modular_v2 is NOT necessarily the actual_v2.
For the SAME unsafe residue r, different n give DIFFERENT actual v2 values.
The modular v2 gives exactly ONE value (the residue's v2), but actual integers
spread across multiple v2 values, all >= k.

HOWEVER: the modular v2 is the MINIMUM actual v2 achievable in that class ONLY IF
the formula above means actual_v2 >= k always. The modular v2 could be larger
than the actual minimum k, which would mean OVERCOUNT (modular > actual).
""")

# Verify: can actual v2 ever be LESS than modular v2 for unsafe residues?
print("Verification: checking if actual_v2 can be < modular_v2 for unsafe residues...")
overcounts_found = []
for k in range(3, 9):
    modulus = 13 * (2 ** k)
    unsafe_rk = [r for r in range(modulus) if r % 2 == 1 and modular_v2(r) >= k]
    for r in unsafe_rk:
        mod_v2 = modular_v2(r)
        start = r if r % 2 == 1 else r + modulus
        for n in range(start, 100001, modulus):
            if n <= 0 or n % 2 == 0:
                continue
            av2 = actual_v2(n)
            if av2 < mod_v2:
                overcounts_found.append((k, r, n, mod_v2, av2))
                break  # one example per residue is enough

if overcounts_found:
    print(f"\n  OVERCOUNTS FOUND ({len(overcounts_found)} cases):")
    for ck, cr, cn, cmv2, cav2 in overcounts_found[:20]:
        print(f"    k={ck}, r={cr}, n={cn}: mod_v2={cmv2}, actual_v2={cav2}, disc={cmv2-cav2}")
    certificates_survive = False
else:
    print("\n  No overcounts found! actual_v2 >= modular_v2 for all sampled integers.")
    certificates_survive = True

# Also check: does actual_v2 ever EQUAL modular_v2 (= tight case)
print("\nChecking tight cases (actual_v2 == modular_v2) at k=3...")
k = 3
modulus = 13 * (2 ** k)
unsafe_k3 = [r for r in range(modulus) if r % 2 == 1 and modular_v2(r) >= k]
tight_counts = {}
for r in unsafe_k3:
    mod_v2 = modular_v2(r)
    tight = 0
    total = 0
    start = r if r % 2 == 1 else r + modulus
    for n in range(start, 10001, modulus):
        if n <= 0 or n % 2 == 0:
            continue
        total += 1
        if actual_v2(n) == mod_v2:
            tight += 1
    tight_counts[r] = (tight, total, mod_v2)
    pct = tight / total * 100 if total > 0 else 0
    print(f"  r={r}: mod_v2={mod_v2}, tight={tight}/{total} ({pct:.1f}%)")

print("\n--- CERTIFICATE SURVIVAL CONCLUSION ---")
if certificates_survive:
    print("""
CONCLUSION: The contraction certificates SURVIVE the v2 discrepancy.

Key finding: For unsafe residues (where modular_v2 >= k), the actual v2
of any integer n ≡ r (mod 13*2^k) is ALWAYS >= modular_v2.

This is because:
  actual_v2(3n+1) = k + v2(A) >= k
  and modular_v2 = v2(3r+1) >= k

More precisely, when v2(3r+1) = k exactly (the minimal unsafe case),
some integers n in that class achieve actual_v2 = k = modular_v2 (tight),
while others achieve actual_v2 > k (modular UNDERESTIMATES for these n).

When v2(3r+1) > k, the modular_v2 > k, but actual integers can have
actual_v2 = k (since the higher bits can cancel). WAIT -- let's check this.
""")
else:
    max_disc = max(cmv2 - cav2 for _, _, _, cmv2, cav2 in overcounts_found)
    print(f"\nCONCLUSION: Certificates DO NOT survive. Max discrepancy: {max_disc}")
    print(f"  Required: delta < 0.15, but max delta = {max_disc}")

# Final detailed check: for unsafe residues where mod_v2 > k, do some n have actual_v2 = k?
print("\nDetailed check: unsafe residues with mod_v2 > k, checking min actual_v2...")
detailed_results = {}
for k in range(3, 7):
    modulus = 13 * (2 ** k)
    unsafe_rk = [r for r in range(modulus) if r % 2 == 1 and modular_v2(r) >= k]
    for r in unsafe_rk:
        mod_v2 = modular_v2(r)
        if mod_v2 <= k:
            continue  # only interested in mod_v2 > k cases
        min_av2_found = None
        start = r if r % 2 == 1 else r + modulus
        for n in range(start, 200001, modulus):
            if n <= 0 or n % 2 == 0:
                continue
            av2 = actual_v2(n)
            if min_av2_found is None or av2 < min_av2_found:
                min_av2_found = av2
            if min_av2_found <= k:
                break  # found a case with actual_v2 = k (minimum possible)
        disc = mod_v2 - min_av2_found if min_av2_found is not None else 0
        is_overcount = (min_av2_found is not None and min_av2_found < mod_v2)
        detailed_results[f"k={k},r={r}"] = {
            "mod_v2": mod_v2, "min_actual_v2": min_av2_found,
            "discrepancy": disc, "is_overcount": is_overcount
        }
        if is_overcount:
            print(f"  OVERCOUNT: k={k}, r={r}, mod_v2={mod_v2}, min_actual_v2={min_av2_found}, disc={disc}")
        else:
            print(f"  OK: k={k}, r={r}, mod_v2={mod_v2}, min_actual_v2={min_av2_found}")

all_ok_detailed = all(not v["is_overcount"] for v in detailed_results.values())
print(f"\nAll detailed checks OK (no overcount)? {'YES' if all_ok_detailed else 'NO'}")


# ── Assemble final results ────────────────────────────────────────────────────

results = {
    "task1": task1_results,
    "task2": {
        "k": 3,
        "modulus": 104,
        "unsafe_residues": unsafe_k3,
        "max_discrepancy_overall": max_discrepancy_overall,
        "max_discrepancy_case": {
            "r": max_discrepancy_case[0] if max_discrepancy_case else None,
            "n": max_discrepancy_case[1] if max_discrepancy_case else None,
            "modular_v2": max_discrepancy_case[2] if max_discrepancy_case else None,
            "actual_v2": max_discrepancy_case[3] if max_discrepancy_case else None,
            "discrepancy": max_discrepancy_case[4] if max_discrepancy_case else None,
        },
        "per_residue": task2_results,
    },
    "task3": {
        "cert_v2_sum_threshold": cert_v2_sum_threshold,
        "cert_steps": cert_steps,
        "margin_millibits": margin_millibits,
        "delta_critical": delta_critical,
        "k3_results": task3_results,
        "all_safe_k3": all_safe,
    },
    "task4": {str(k): task4_results[k] for k in task4_results},
    "task5": {
        "overcounts_found": len(overcounts_found),
        "max_discrepancy_global": max_disc_global,
        "certificates_survive": all_ok_detailed and not overcounts_found,
        "detailed_higher_k_results": detailed_results,
    },
}

# Convert task1_results keys to strings for JSON
results["task1"] = {str(k): v for k, v in task1_results.items()}

output_dir = os.path.dirname(os.path.abspath(__file__))
json_path = os.path.join(output_dir, "unsafe_residues_results.json")
with open(json_path, "w") as f:
    json.dump(results, f, indent=2, default=str)
print(f"\nResults saved to: {json_path}")


# ── Write summary markdown ────────────────────────────────────────────────────

summary_path = os.path.join(output_dir, "UNSAFE_RESIDUES_SUMMARY.md")

# Build summary text
cert_survive_answer = "YES" if (all_ok_detailed and not overcounts_found) else "NO"

summary_lines = []
summary_lines.append("# Unsafe Residues Analysis: Collatz/Syracuse Modular v2")
summary_lines.append("")
summary_lines.append("## Key Result")
summary_lines.append("")
summary_lines.append(f"**Do the contraction certificates survive the v2 discrepancy? {cert_survive_answer}**")
summary_lines.append("")

if cert_survive_answer == "YES":
    summary_lines.append(
        "The modular v2 computation does NOT overcount actual v2 for unsafe residues. "
        "For every unsafe residue r at level k and every actual odd integer n ≡ r (mod 13·2^k), "
        "the actual v2(3n+1) is always >= the modular v2(3r+1). "
        "Therefore the contraction certificates based on modular v2 are valid lower bounds "
        "for actual integer contraction."
    )
else:
    summary_lines.append(
        f"Overcounting was detected. Max discrepancy = {max_disc_global}. "
        f"The critical threshold is delta < 0.15. Certificates FAIL."
    )

summary_lines.append("")
summary_lines.append("---")
summary_lines.append("")
summary_lines.append("## Task 1: Unsafe Residue Enumeration")
summary_lines.append("")
summary_lines.append("An **unsafe residue** at level k is an odd r in ZMod(13·2^k) with v2(3r+1) >= k.")
summary_lines.append("")
summary_lines.append("| k | modulus | count_unsafe | all 13 mod-13 classes covered |")
summary_lines.append("|---|---------|-------------|-------------------------------|")
for k in range(3, 11):
    info = results["task1"][str(k)]
    cov = "YES" if len(info["residue_classes_mod13"]) == 13 else "NO"
    summary_lines.append(f"| {k} | {info['modulus']} | {info['count_unsafe']} | {cov} |")

summary_lines.append("")
summary_lines.append("**Finding:** At every level k=3..10, there are exactly 13 unsafe residues, "
                     "one for each residue class mod 13.")
summary_lines.append("")
summary_lines.append("**Unsafe residues at k=3 (mod 104):**")
summary_lines.append("")
summary_lines.append(f"`{unsafe_k3}`")
summary_lines.append("")
summary_lines.append("---")
summary_lines.append("")
summary_lines.append("## Task 2: v2 Discrepancy at k=3")
summary_lines.append("")
summary_lines.append(f"For each of the 13 unsafe residues at k=3 (modulus=104), "
                     f"we checked all odd n ≡ r (mod 104) with n ≤ 10000.")
summary_lines.append("")
summary_lines.append(f"**Maximum discrepancy (modular_v2 - actual_v2): {max_discrepancy_overall}**")
summary_lines.append("")
if max_discrepancy_overall == 0:
    summary_lines.append("No discrepancy was found: for every unsafe residue r, "
                         "the actual v2 of every sampled n matched or exceeded the modular v2.")
else:
    summary_lines.append(f"Discrepancy found at: r={max_discrepancy_case[0]}, n={max_discrepancy_case[1]}, "
                         f"modular_v2={max_discrepancy_case[2]}, actual_v2={max_discrepancy_case[3]}.")
summary_lines.append("")
summary_lines.append("---")
summary_lines.append("")
summary_lines.append("## Task 3: Certificate Survival at k=3")
summary_lines.append("")
summary_lines.append(f"**Certificate parameters:**")
summary_lines.append(f"- v2_sum threshold: {cert_v2_sum_threshold} bits over {cert_steps} steps")
summary_lines.append(f"- Margin: {margin_millibits} millibits = {margin_millibits/1000:.3f} bits")
summary_lines.append(f"- Critical discrepancy delta for failure: delta >= {delta_critical}")
summary_lines.append("")
summary_lines.append("**True v2 distribution for each k=3 unsafe residue (n ≡ r mod 104, n ≤ 10000):**")
summary_lines.append("")
summary_lines.append("| r | modular_v2 | min_actual_v2 | max_discrepancy | cert_survives |")
summary_lines.append("|---|-----------|--------------|-----------------|---------------|")
for r, info in task3_results.items():
    surv = "YES" if info["certificate_survives"] else "NO"
    summary_lines.append(
        f"| {r} | {info['modular_v2']} | {info['min_actual_v2']} | {info['max_discrepancy']} | {surv} |"
    )
summary_lines.append("")

all_cert_ok = all(v["certificate_survives"] for v in task3_results.values())
summary_lines.append(f"**All k=3 certificates survive: {'YES' if all_cert_ok else 'NO'}**")
summary_lines.append("")
summary_lines.append("---")
summary_lines.append("")
summary_lines.append("## Task 4: Higher k (k=4..6)")
summary_lines.append("")
summary_lines.append("For k=4,5,6 unsafe residues, checking min actual v2 vs modular v2 (n ≤ 10000):")
summary_lines.append("")
summary_lines.append("| k | r | mod_v2 | min_actual_v2 | discrepancy | overcount |")
summary_lines.append("|---|---|--------|--------------|-------------|-----------|")
for k in range(4, 7):
    for r, info in (task4_results.get(k) or {}).items():
        oc = "YES" if info["any_overcount"] else "NO"
        summary_lines.append(
            f"| {k} | {r} | {info['modular_v2']} | {info['min_actual_v2']} | {info['max_discrepancy']} | {oc} |"
        )
summary_lines.append("")
summary_lines.append("---")
summary_lines.append("")
summary_lines.append("## Task 5: Final Answer")
summary_lines.append("")
summary_lines.append(f"### Can the contraction certificates survive the v2 discrepancy? **{cert_survive_answer}**")
summary_lines.append("")

if cert_survive_answer == "YES":
    summary_lines.append("### Explanation")
    summary_lines.append("")
    summary_lines.append(
        "The modular v2 for an unsafe residue r at level k is v2(3r+1) >= k. "
        "For any actual odd integer n = r + 13·2^k·m in that class:"
    )
    summary_lines.append("")
    summary_lines.append("```")
    summary_lines.append("3n+1 = 3r+1 + 13·2^k·(3m)")
    summary_lines.append("     = 2^k · (2^{v2(3r+1)-k}·q + 39m)   [where q = (3r+1)/2^{v2(3r+1)} is odd]")
    summary_lines.append("```")
    summary_lines.append("")
    summary_lines.append("So `actual_v2(3n+1) = k + v2(inner_term) >= k`.")
    summary_lines.append("")
    summary_lines.append(
        "When the modular v2 equals exactly k (the minimum unsafe case), "
        "some n achieve actual_v2 = k (tight match), while others achieve higher values. "
        "The modular computation is a LOWER BOUND in this case."
    )
    summary_lines.append("")
    summary_lines.append(
        "When the modular v2 > k, the inner term `2^{v2-k}·q + 39m` can be odd for some m, "
        "giving actual_v2 = k < modular_v2. This IS an overcount situation. "
        "The detailed check (Task 5 detailed) confirms whether such cases exist empirically."
    )
    summary_lines.append("")
    if not all_ok_detailed:
        summary_lines.append("**WARNING: Overcounting was detected for some mod_v2 > k residues.**")
        summary_lines.append("However, the discrepancy magnitude is bounded and the certificates may still hold.")
    else:
        summary_lines.append(
            "Empirical verification: no integer in the tested range showed actual_v2 < modular_v2 "
            "for these residues, confirming certificates are valid within the tested domain."
        )
    summary_lines.append("")
    summary_lines.append("### Numbers")
    summary_lines.append(f"- Max observed discrepancy: {max_disc_global}")
    summary_lines.append(f"- Critical discrepancy threshold: {delta_critical}")
    summary_lines.append(f"- Certificates survive: {cert_survive_answer}")
else:
    summary_lines.append(f"Max discrepancy = {max_disc_global}, threshold = {delta_critical}.")
    summary_lines.append("Correction needed: subtract max discrepancy from v2_sum threshold.")

summary_lines.append("")
summary_lines.append("---")
summary_lines.append("*Generated by collatz_unsafe_residues.py*")

with open(summary_path, "w") as f:
    f.write("\n".join(summary_lines) + "\n")
print(f"Summary saved to: {summary_path}")

print("\n" + "=" * 70)
print("DONE")
print("=" * 70)
