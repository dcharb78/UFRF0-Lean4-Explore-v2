"""
Q10: Reduced-Core Mining on the Regime-II Bad Frontier

After the Lean reduction showing that, above the target cutoff B, the
bad-frontier survivor condition collapses to the self-threshold side, this
script checks whether the existing observer atlas becomes sufficient when we
only ask for local control of that reduced core.

It tests three increasingly intrinsic families of local cells:

1. single coherent bundle-chart cells
2. pairwise / full coherent joint-atlas cells
3. intrinsic residue-chart cells

It also checks a simple transition-slice core: simultaneous nonincrease of
the self-threshold defect and the radial gap `stateValue - B`.

The point is to see whether the new core reduction revives local descent on
the current atlas, or whether we still need a genuinely transition-level law.
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


def self_threshold_defect(t: int, base: int, eject: int) -> int:
    return base + 1 - base_threshold(state_value(t, base), t, eject)


def radial_gap(t: int, base: int) -> int:
    return state_value(t, base) - B


def residue_chart(base: int, eject: int) -> int:
    return base % (1 << (eject + 1))


def is_bad_state(t: int, base: int, eject: int) -> bool:
    n = state_value(t, base)
    nxt = next_value(t, base, eject)
    return t >= 2 and n <= nxt and B <= nxt


def bundle_state(n: int, eject: int, spec: dict):
    return ((n + 1) % spec["modulus"], eject % spec["dyadic_period"])


def coherent_bundle_names(t: int):
    return sorted(
        name for name, spec in BUNDLES.items() if (t - 1) % spec["period"] == 0
    )


def init_self_stats():
    return {
        "count": 0,
        "max_d_self_thr": -10**18,
        "min_d_self_thr": 10**18,
        "dst_slices": Counter(),
    }


def init_core_stats():
    return {
        "count": 0,
        "max_d_self_thr": -10**18,
        "min_d_self_thr": 10**18,
        "max_d_radial_gap": -10**18,
        "min_d_radial_gap": 10**18,
    }


def update_self(stats: dict, d_self: int, dst_slice):
    stats["count"] += 1
    stats["dst_slices"][dst_slice] += 1
    stats["max_d_self_thr"] = max(stats["max_d_self_thr"], d_self)
    stats["min_d_self_thr"] = min(stats["min_d_self_thr"], d_self)


def update_core(stats: dict, d_self: int, d_radial: int):
    stats["count"] += 1
    stats["max_d_self_thr"] = max(stats["max_d_self_thr"], d_self)
    stats["min_d_self_thr"] = min(stats["min_d_self_thr"], d_self)
    stats["max_d_radial_gap"] = max(stats["max_d_radial_gap"], d_radial)
    stats["min_d_radial_gap"] = min(stats["min_d_radial_gap"], d_radial)


def promising_self(stats: dict) -> bool:
    return (
        stats["count"] > 0
        and stats["max_d_self_thr"] <= 0
        and stats["min_d_self_thr"] < 0
    )


def promising_core(stats: dict) -> bool:
    return (
        stats["count"] > 0
        and stats["max_d_self_thr"] <= 0
        and stats["max_d_radial_gap"] <= 0
        and (
            stats["min_d_self_thr"] < 0
            or stats["min_d_radial_gap"] < 0
        )
    )


def serialize_self_rows(cell_map, limit=25):
    rows = []
    for key, stats in cell_map.items():
        if not promising_self(stats):
            continue
        rows.append(
            {
                "key": key,
                "count": stats["count"],
                "dst_slices": [
                    {"slice": list(s), "count": c}
                    for s, c in stats["dst_slices"].most_common(10)
                ],
                "delta_self_threshold": {
                    "min": stats["min_d_self_thr"],
                    "max": stats["max_d_self_thr"],
                },
            }
        )
    rows.sort(key=lambda row: (-row["count"], str(row["key"])))
    return rows[:limit]


def serialize_core_rows(cell_map, limit=25):
    rows = []
    for key, stats in cell_map.items():
        if not promising_core(stats):
            continue
        rows.append(
            {
                "key": key,
                "count": stats["count"],
                "delta_self_threshold": {
                    "min": stats["min_d_self_thr"],
                    "max": stats["max_d_self_thr"],
                },
                "delta_radial_gap": {
                    "min": stats["min_d_radial_gap"],
                    "max": stats["max_d_radial_gap"],
                },
            }
        )
    rows.sort(key=lambda row: (-row["count"], str(row["key"])))
    return rows[:limit]


def main():
    single_cells = {name: defaultdict(init_self_stats) for name in BUNDLES}
    pair_cells = defaultdict(init_self_stats)
    joint_cells = defaultdict(init_self_stats)
    residue_cells = defaultdict(init_self_stats)
    transition_slice_cells = defaultdict(init_core_stats)
    sample_transitions = []

    for n in range(3, LIMIT + 1, 2):
        t, base, eject = regime_state(n)
        if not is_bad_state(t, base, eject):
            continue

        nxt = next_value(t, base, eject)
        t2, base2, eject2 = regime_state(nxt)
        if not is_bad_state(t2, base2, eject2):
            continue

        src_self = self_threshold_defect(t, base, eject)
        dst_self = self_threshold_defect(t2, base2, eject2)
        d_self = dst_self - src_self
        d_radial = radial_gap(t2, base2) - radial_gap(t, base)
        dst_slice = (t2, eject2)

        for name, spec in BUNDLES.items():
            if (t - 1) % spec["period"] != 0:
                continue
            key = ((t, eject), bundle_state(n, eject, spec))
            update_self(single_cells[name][key], d_self, dst_slice)

        coherent = coherent_bundle_names(t)
        bundle_states = {
            name: bundle_state(n, eject, BUNDLES[name]) for name in coherent
        }
        for pair in combinations(coherent, 2):
            key = (
                (t, eject),
                pair,
                tuple((name, bundle_states[name]) for name in pair),
            )
            update_self(pair_cells[key], d_self, dst_slice)

        joint_key = (
            (t, eject),
            tuple((name, bundle_states[name]) for name in coherent),
        )
        update_self(joint_cells[joint_key], d_self, dst_slice)

        residue_key = ((t, eject), residue_chart(base, eject))
        update_self(residue_cells[residue_key], d_self, dst_slice)

        slice_key = ((t, eject), (t2, eject2))
        update_core(transition_slice_cells[slice_key], d_self, d_radial)

        if len(sample_transitions) < 20:
            sample_transitions.append(
                {
                    "n": n,
                    "src_slice": [t, eject],
                    "dst_slice": [t2, eject2],
                    "src_self_threshold": src_self,
                    "dst_self_threshold": dst_self,
                    "delta_self_threshold": d_self,
                    "src_radial_gap": radial_gap(t, base),
                    "dst_radial_gap": radial_gap(t2, base2),
                    "delta_radial_gap": d_radial,
                }
            )

    summary = {
        "B": B,
        "limit": LIMIT,
        "bundle_self_threshold_promising_cells": {
            name: serialize_self_rows(cell_map)
            for name, cell_map in single_cells.items()
        },
        "pair_atlas_self_threshold_promising_cells": serialize_self_rows(pair_cells),
        "joint_atlas_self_threshold_promising_cells": serialize_self_rows(joint_cells),
        "residue_self_threshold_promising_cells": serialize_self_rows(residue_cells),
        "transition_slice_core_promising_cells": serialize_core_rows(
            transition_slice_cells
        ),
        "samples": sample_transitions,
    }

    out_path = Path(__file__).with_name("q10_results.json")
    out_path.write_text(json.dumps(summary, indent=2))

    print("=" * 60)
    print("Q10: Reduced-Core Mining on the Regime-II Bad Frontier")
    print("=" * 60)
    print(f"B = {B}, odd search limit = {LIMIT}")
    print("\nPromising single-chart cells for self-threshold descent:")
    for name, rows in summary["bundle_self_threshold_promising_cells"].items():
        print(f"  {name}: {len(rows)} cells")
    print(
        "\nPromising pair-atlas cells for self-threshold descent:",
        len(summary["pair_atlas_self_threshold_promising_cells"]),
    )
    print(
        "Promising joint-atlas cells for self-threshold descent:",
        len(summary["joint_atlas_self_threshold_promising_cells"]),
    )
    print(
        "Promising intrinsic residue cells for self-threshold descent:",
        len(summary["residue_self_threshold_promising_cells"]),
    )
    print(
        "Promising transition-slice core cells (self-threshold + radial gap):",
        len(summary["transition_slice_core_promising_cells"]),
    )
    print(f"\nSaved JSON summary to {out_path}")


if __name__ == "__main__":
    main()
