"""
Q8: Bad-Frontier Multiview Transition Mining

Enumerates intrinsic Regime-II bad-frontier transitions below a search limit and
studies them through several simultaneous readouts:

- source-state slice (time, eject, base)
- residue chart
- threshold defects
- successor defects
- observer-bundle states on coherent slices

The goal is not to privilege any one chart. The goal is to find local chart
cells that might support a glued descent law even though no simple global scalar
or lex rank on the current defect coordinates seems monotone.
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


def residue_chart(base: int, eject: int) -> int:
    return base % (1 << (eject + 1))


def bundle_state(n: int, eject: int, spec: dict):
    return {
        "clock": (n + 1) % spec["modulus"],
        "eject_class": eject % spec["dyadic_period"],
    }


def defects(t: int, base: int, eject: int):
    n = state_value(t, base)
    nxt = next_value(t, base, eject)
    return {
        "self_succ": nxt + 1 - n,
        "zone_succ": nxt + 1 - B,
        "self_thr": base + 1 - base_threshold(n, t, eject),
        "zone_thr": base + 1 - base_threshold(B, t, eject),
    }


def is_bad_state(t: int, base: int, eject: int) -> bool:
    n = state_value(t, base)
    nxt = next_value(t, base, eject)
    return t >= 2 and n <= nxt and B <= nxt


def promising_cell(stats: dict) -> bool:
    return (
        stats["count"] > 0
        and stats["max_dst_self_thr_minus_src"] <= 0
        and stats["max_dst_zone_thr_minus_src"] <= 0
        and (
            stats["min_dst_self_thr_minus_src"] < 0
            or stats["min_dst_zone_thr_minus_src"] < 0
        )
    )


def main():
    bad_count = 0
    bad_to_bad_count = 0
    slice_counts = Counter()
    transition_slices = Counter()

    chart_cells = {
        name: defaultdict(
            lambda: {
                "count": 0,
                "dst_slices": Counter(),
                "max_dst_self_thr_minus_src": -10**18,
                "min_dst_self_thr_minus_src": 10**18,
                "max_dst_zone_thr_minus_src": -10**18,
                "min_dst_zone_thr_minus_src": 10**18,
            }
        )
        for name in BUNDLES
    }

    sample_transitions = []

    for n in range(3, LIMIT + 1, 2):
        t, base, eject = regime_state(n)
        if not is_bad_state(t, base, eject):
            continue

        bad_count += 1
        slice_counts[(t, eject)] += 1

        nxt = next_value(t, base, eject)
        t2, base2, eject2 = regime_state(nxt)
        if not is_bad_state(t2, base2, eject2):
            continue

        bad_to_bad_count += 1
        transition_slices[((t, eject), (t2, eject2))] += 1

        src_def = defects(t, base, eject)
        dst_def = defects(t2, base2, eject2)

        if len(sample_transitions) < 25:
            sample_transitions.append(
                {
                    "n": n,
                    "src": {
                        "time": t,
                        "base": base,
                        "eject": eject,
                        "residue": residue_chart(base, eject),
                        **src_def,
                    },
                    "next_value": nxt,
                    "dst": {
                        "time": t2,
                        "base": base2,
                        "eject": eject2,
                        "residue": residue_chart(base2, eject2),
                        **dst_def,
                    },
                }
            )

        for name, spec in BUNDLES.items():
            if (t - 1) % spec["period"] != 0:
                continue
            src_state = bundle_state(n, eject, spec)
            cell_key = (
                (t, eject),
                (src_state["clock"], src_state["eject_class"]),
            )
            stats = chart_cells[name][cell_key]
            stats["count"] += 1
            stats["dst_slices"][(t2, eject2)] += 1

            d_self = dst_def["self_thr"] - src_def["self_thr"]
            d_zone = dst_def["zone_thr"] - src_def["zone_thr"]
            stats["max_dst_self_thr_minus_src"] = max(
                stats["max_dst_self_thr_minus_src"], d_self
            )
            stats["min_dst_self_thr_minus_src"] = min(
                stats["min_dst_self_thr_minus_src"], d_self
            )
            stats["max_dst_zone_thr_minus_src"] = max(
                stats["max_dst_zone_thr_minus_src"], d_zone
            )
            stats["min_dst_zone_thr_minus_src"] = min(
                stats["min_dst_zone_thr_minus_src"], d_zone
            )

    summary = {
        "B": B,
        "limit": LIMIT,
        "bad_state_count": bad_count,
        "bad_to_bad_transition_count": bad_to_bad_count,
        "top_bad_slices": [
            {"slice": list(k), "count": v} for k, v in slice_counts.most_common(20)
        ],
        "top_transition_slices": [
            {"src_slice": list(k[0]), "dst_slice": list(k[1]), "count": v}
            for k, v in transition_slices.most_common(25)
        ],
        "bundle_promising_cells": {},
        "samples": sample_transitions,
    }

    for name, cell_map in chart_cells.items():
        promising = []
        for key, stats in cell_map.items():
            if promising_cell(stats):
                promising.append(
                    {
                        "src_slice": list(key[0]),
                        "src_bundle_state": {
                            "clock": key[1][0],
                            "eject_class": key[1][1],
                        },
                        "count": stats["count"],
                        "dst_slices": [
                            {"slice": list(s), "count": c}
                            for s, c in stats["dst_slices"].most_common(10)
                        ],
                        "delta_self_thr": {
                            "min": stats["min_dst_self_thr_minus_src"],
                            "max": stats["max_dst_self_thr_minus_src"],
                        },
                        "delta_zone_thr": {
                            "min": stats["min_dst_zone_thr_minus_src"],
                            "max": stats["max_dst_zone_thr_minus_src"],
                        },
                    }
                )
        promising.sort(key=lambda row: (-row["count"], row["src_slice"], row["src_bundle_state"]["clock"]))
        summary["bundle_promising_cells"][name] = promising[:25]

    out_path = Path(__file__).with_name("q8_results.json")
    out_path.write_text(json.dumps(summary, indent=2))

    print("=" * 60)
    print("Q8: Bad-Frontier Multiview Transition Mining")
    print("=" * 60)
    print(f"B = {B}, odd search limit = {LIMIT}")
    print(f"bad states: {bad_count}")
    print(f"bad -> bad transitions: {bad_to_bad_count}")
    print("\nTop bad slices:")
    for row in summary["top_bad_slices"][:10]:
        print(f"  slice={tuple(row['slice'])} count={row['count']}")
    print("\nTop transition slices:")
    for row in summary["top_transition_slices"][:10]:
        print(
            f"  {tuple(row['src_slice'])} -> {tuple(row['dst_slice'])}"
            f" count={row['count']}"
        )
    print("\nPromising local chart cells (threshold defects nonincreasing):")
    for name, rows in summary["bundle_promising_cells"].items():
        print(f"  {name}: {len(rows)} cells")
        for row in rows[:5]:
            print(
                "   ",
                f"slice={tuple(row['src_slice'])}",
                f"state=({row['src_bundle_state']['clock']},"
                f"{row['src_bundle_state']['eject_class']})",
                f"count={row['count']}",
                f"d_self={row['delta_self_thr']}",
                f"d_zone={row['delta_zone_thr']}",
            )
    print(f"\nSaved JSON summary to {out_path}")


if __name__ == "__main__":
    main()
