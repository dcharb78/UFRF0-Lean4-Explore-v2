"""
Q9: Joint-Atlas Mining on the Regime-II Bad Frontier

Q8 showed that no single coherent bundle chart cell forces both source-threshold
defects to be nonincreasing on bad->bad transitions below the current search
limit. This script checks whether genuinely joint chart cells do better.

It studies two atlas levels:
  1. pairwise coherent bundle atlases
  2. the full coherent bundle atlas available on the source slice

The point is not to privilege one observer. The point is to see whether a
glued multiview cell can support local descent even when every single chart
fails on its own.
"""

import json
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path


B = 832
LIMIT = 200_000

BUNDLES = {
    "bundle5": {"modulus": 5, "period": 2, "dyadic_period": 4},
    "bundle7": {"modulus": 7, "period": 6, "dyadic_period": 3},
    "bundle11": {"modulus": 11, "period": 10, "dyadic_period": 10},
    "bundle13": {"modulus": 13, "period": 4, "dyadic_period": 12},
    "bundle65": {"modulus": 65, "period": 4, "dyadic_period": 12},
}


def v2(n: int) -> int:
    if n == 0:
        return -1
    c = 0
    while n % 2 == 0:
        n //= 2
        c += 1
    return c


def regime_state(n: int):
    t = v2(n + 1)
    base = (n + 1) >> t
    eject = v2((3 ** t) * base - 1)
    return t, base, eject


def state_value(t: int, base: int) -> int:
    return (1 << t) * base - 1


def next_value(t: int, base: int, eject: int) -> int:
    return ((3 ** t) * base - 1) >> eject


def base_threshold(cutoff: int, t: int, eject: int) -> int:
    return (cutoff * (1 << eject)) // (3 ** t) + 1


def defects(t: int, base: int, eject: int):
    n = state_value(t, base)
    nxt = next_value(t, base, eject)
    return {
        "self_thr": base + 1 - base_threshold(n, t, eject),
        "zone_thr": base + 1 - base_threshold(B, t, eject),
        "self_succ": nxt + 1 - n,
        "zone_succ": nxt + 1 - B,
    }


def is_bad_state(t: int, base: int, eject: int) -> bool:
    n = state_value(t, base)
    nxt = next_value(t, base, eject)
    return t >= 2 and n <= nxt and B <= nxt


def bundle_state(n: int, eject: int, spec: dict):
    return ((n + 1) % spec["modulus"], eject % spec["dyadic_period"])


def coherent_bundle_names(t: int):
    return sorted(name for name, spec in BUNDLES.items() if (t - 1) % spec["period"] == 0)


def promising(stats: dict) -> bool:
    return (
        stats["count"] > 0
        and stats["max_d_self_thr"] <= 0
        and stats["max_d_zone_thr"] <= 0
        and (stats["min_d_self_thr"] < 0 or stats["min_d_zone_thr"] < 0)
    )


def init_stats():
    return {
        "count": 0,
        "dst_slices": Counter(),
        "max_d_self_thr": -10**18,
        "min_d_self_thr": 10**18,
        "max_d_zone_thr": -10**18,
        "min_d_zone_thr": 10**18,
    }


def update(stats: dict, d_self: int, d_zone: int, dst_slice):
    stats["count"] += 1
    stats["dst_slices"][dst_slice] += 1
    stats["max_d_self_thr"] = max(stats["max_d_self_thr"], d_self)
    stats["min_d_self_thr"] = min(stats["min_d_self_thr"], d_self)
    stats["max_d_zone_thr"] = max(stats["max_d_zone_thr"], d_zone)
    stats["min_d_zone_thr"] = min(stats["min_d_zone_thr"], d_zone)


def serialize_rows(cell_map, limit=25):
    rows = []
    for key, stats in cell_map.items():
        if not promising(stats):
            continue
        rows.append(
            {
                "key": key,
                "count": stats["count"],
                "dst_slices": [
                    {"slice": list(s), "count": c}
                    for s, c in stats["dst_slices"].most_common(10)
                ],
                "delta_self_thr": {
                    "min": stats["min_d_self_thr"],
                    "max": stats["max_d_self_thr"],
                },
                "delta_zone_thr": {
                    "min": stats["min_d_zone_thr"],
                    "max": stats["max_d_zone_thr"],
                },
            }
        )
    rows.sort(key=lambda row: (-row["count"], str(row["key"])))
    return rows[:limit]


def main():
    pair_cells = defaultdict(init_stats)
    joint_cells = defaultdict(init_stats)
    coherent_profile_counts = Counter()
    sample_joint = []

    for n in range(3, LIMIT + 1, 2):
        t, base, eject = regime_state(n)
        if not is_bad_state(t, base, eject):
            continue
        nxt = next_value(t, base, eject)
        t2, base2, eject2 = regime_state(nxt)
        if not is_bad_state(t2, base2, eject2):
            continue

        src_def = defects(t, base, eject)
        dst_def = defects(t2, base2, eject2)
        d_self = dst_def["self_thr"] - src_def["self_thr"]
        d_zone = dst_def["zone_thr"] - src_def["zone_thr"]
        dst_slice = (t2, eject2)

        coherent = coherent_bundle_names(t)
        coherent_profile_counts[tuple(coherent)] += 1
        bundle_states = {
            name: bundle_state(n, eject, BUNDLES[name])
            for name in coherent
        }

        if len(coherent) >= 2:
            for pair in combinations(coherent, 2):
                key = (
                    (t, eject),
                    pair,
                    tuple((name, bundle_states[name]) for name in pair),
                )
                update(pair_cells[key], d_self, d_zone, dst_slice)

        joint_key = (
            (t, eject),
            tuple((name, bundle_states[name]) for name in coherent),
        )
        update(joint_cells[joint_key], d_self, d_zone, dst_slice)

        if len(sample_joint) < 20:
            sample_joint.append(
                {
                    "n": n,
                    "src_slice": [t, eject],
                    "coherent_bundles": [
                        {"name": name, "state": list(bundle_states[name])}
                        for name in coherent
                    ],
                    "dst_slice": [t2, eject2],
                    "delta_self_thr": d_self,
                    "delta_zone_thr": d_zone,
                }
            )

    summary = {
        "B": B,
        "limit": LIMIT,
        "coherent_profiles": [
            {"bundles": list(profile), "count": count}
            for profile, count in coherent_profile_counts.most_common()
        ],
        "pair_atlas_promising_cells": serialize_rows(pair_cells),
        "joint_atlas_promising_cells": serialize_rows(joint_cells),
        "samples": sample_joint,
    }

    out_path = Path(__file__).with_name("q9_results.json")
    out_path.write_text(json.dumps(summary, indent=2))

    print("=" * 60)
    print("Q9: Joint-Atlas Mining on the Regime-II Bad Frontier")
    print("=" * 60)
    print(f"B = {B}, odd search limit = {LIMIT}")
    print("\nCoherent bundle profiles:")
    for row in summary["coherent_profiles"][:10]:
        print(f"  bundles={tuple(row['bundles'])} count={row['count']}")
    print("\nPromising pair atlas cells:", len(summary["pair_atlas_promising_cells"]))
    for row in summary["pair_atlas_promising_cells"][:10]:
        print(
            "  ",
            f"key={row['key']}",
            f"count={row['count']}",
            f"d_self={row['delta_self_thr']}",
            f"d_zone={row['delta_zone_thr']}",
        )
    print("\nPromising full joint atlas cells:", len(summary["joint_atlas_promising_cells"]))
    for row in summary["joint_atlas_promising_cells"][:10]:
        print(
            "  ",
            f"key={row['key']}",
            f"count={row['count']}",
            f"d_self={row['delta_self_thr']}",
            f"d_zone={row['delta_zone_thr']}",
        )
    print(f"\nSaved JSON summary to {out_path}")


if __name__ == "__main__":
    main()
