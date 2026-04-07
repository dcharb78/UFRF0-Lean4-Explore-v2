"""
Q11: Projective-Core Mining on the Regime-II Bad Frontier

Q10 showed that additive control of the reduced core still fails:
no current observer-atlas cell forces self-threshold defect descent,
and no simple additive pair with radial gap works either.

This script switches to a projective / cone-direction viewpoint on the
true core, restricting to bad->bad transitions whose source already lies
above the target cutoff B.

For a core state, define the projective slope informally by:

    slope = self_threshold_defect / radial_gap

where radial_gap = stateValue - B > 0.

We compare slopes without division by cross-multiplying:

    dst_slope <= src_slope
      iff
    dst_self * src_gap <= src_self * dst_gap

The goal is to find cells where cone direction is monotone even though the
raw coordinates are not.
"""

import json
from collections import Counter, defaultdict
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


def is_core_state(t: int, base: int, eject: int) -> bool:
    return is_bad_state(t, base, eject) and B <= state_value(t, base)


def bundle_state(n: int, eject: int, spec: dict):
    return ((n + 1) % spec["modulus"], eject % spec["dyadic_period"])


def init_stats():
    return {
        "count": 0,
        "min_sign": 2,
        "max_sign": -2,
        "dst_slices": Counter(),
    }


def update(stats: dict, sign: int, dst_slice):
    stats["count"] += 1
    stats["min_sign"] = min(stats["min_sign"], sign)
    stats["max_sign"] = max(stats["max_sign"], sign)
    stats["dst_slices"][dst_slice] += 1


def promising(stats: dict) -> bool:
    return stats["count"] > 0 and stats["max_sign"] <= 0 and stats["min_sign"] < 0


def serialize_rows(cell_map, limit=25):
    rows = []
    for key, stats in cell_map.items():
        if not promising(stats):
            continue
        rows.append(
            {
                "key": key,
                "count": stats["count"],
                "sign_range": {"min": stats["min_sign"], "max": stats["max_sign"]},
                "dst_slices": [
                    {"slice": list(s), "count": c}
                    for s, c in stats["dst_slices"].most_common(10)
                ],
            }
        )
    rows.sort(key=lambda row: (-row["count"], str(row["key"])))
    return rows[:limit]


def main():
    source_slice_cells = defaultdict(init_stats)
    transition_slice_cells = defaultdict(init_stats)
    residue_cells = defaultdict(init_stats)
    single_chart_cells = {name: defaultdict(init_stats) for name in BUNDLES}
    sample_transitions = []

    for n in range(3, LIMIT + 1, 2):
        t, base, eject = regime_state(n)
        if not is_core_state(t, base, eject):
            continue

        nxt = next_value(t, base, eject)
        t2, base2, eject2 = regime_state(nxt)
        if not is_bad_state(t2, base2, eject2):
            continue

        src_self = self_threshold_defect(t, base, eject)
        src_gap = radial_gap(t, base)
        dst_self = self_threshold_defect(t2, base2, eject2)
        dst_gap = radial_gap(t2, base2)
        lhs = dst_self * src_gap
        rhs = src_self * dst_gap
        sign = 0 if lhs == rhs else (-1 if lhs < rhs else 1)
        dst_slice = (t2, eject2)

        update(source_slice_cells[(t, eject)], sign, dst_slice)
        update(transition_slice_cells[((t, eject), (t2, eject2))], sign, dst_slice)
        update(residue_cells[((t, eject), residue_chart(base, eject))], sign, dst_slice)

        n_value = state_value(t, base)
        for name, spec in BUNDLES.items():
            if (t - 1) % spec["period"] != 0:
                continue
            key = ((t, eject), bundle_state(n_value, eject, spec))
            update(single_chart_cells[name][key], sign, dst_slice)

        if len(sample_transitions) < 20:
            sample_transitions.append(
                {
                    "n": n,
                    "src_slice": [t, eject],
                    "dst_slice": [t2, eject2],
                    "src_self_threshold": src_self,
                    "src_radial_gap": src_gap,
                    "dst_self_threshold": dst_self,
                    "dst_radial_gap": dst_gap,
                    "cross_difference": lhs - rhs,
                    "slope_sign": sign,
                }
            )

    summary = {
        "B": B,
        "limit": LIMIT,
        "promising_source_slices": serialize_rows(source_slice_cells),
        "promising_transition_slices": serialize_rows(transition_slice_cells),
        "promising_residue_cells": serialize_rows(residue_cells),
        "promising_single_chart_cells": {
            name: serialize_rows(cell_map)
            for name, cell_map in single_chart_cells.items()
        },
        "samples": sample_transitions,
    }

    out_path = Path(__file__).with_name("q11_results.json")
    out_path.write_text(json.dumps(summary, indent=2))

    print("=" * 60)
    print("Q11: Projective-Core Mining on the Regime-II Bad Frontier")
    print("=" * 60)
    print(f"B = {B}, odd search limit = {LIMIT}")
    print("\nPromising source slices:")
    for row in summary["promising_source_slices"][:10]:
        print(
            f"  source_slice={tuple(row['key'])} count={row['count']}"
            f" sign_range={row['sign_range']}"
        )
    print("\nPromising transition slices:", len(summary["promising_transition_slices"]))
    for row in summary["promising_transition_slices"][:10]:
        print(
            f"  key={row['key']} count={row['count']}"
            f" sign_range={row['sign_range']}"
        )
    print("\nPromising residue cells:", len(summary["promising_residue_cells"]))
    for row in summary["promising_residue_cells"][:10]:
        print(
            f"  key={row['key']} count={row['count']}"
            f" sign_range={row['sign_range']}"
        )
    print("\nPromising single chart cells:")
    for name, rows in summary["promising_single_chart_cells"].items():
        print(f"  {name}: {len(rows)} cells")
        for row in rows[:5]:
            print(
                f"    key={row['key']} count={row['count']}"
                f" sign_range={row['sign_range']}"
            )
    print(f"\nSaved JSON summary to {out_path}")


if __name__ == "__main__":
    main()
