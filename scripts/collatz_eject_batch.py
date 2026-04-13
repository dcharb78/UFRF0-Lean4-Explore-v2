#!/usr/bin/env python3

from __future__ import annotations

import argparse
import concurrent.futures as cf
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import textwrap
import time
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path


NUMBER_WORDS = {
    15: "fifteen",
    16: "sixteen",
    17: "seventeen",
    18: "eighteen",
    19: "nineteen",
    20: "twenty",
    21: "twenty_one",
    22: "twenty_two",
    23: "twenty_three",
    24: "twenty_four",
    25: "twenty_five",
    26: "twenty_six",
    27: "twenty_seven",
    28: "twenty_eight",
    29: "twenty_nine",
}


@dataclass(frozen=True)
class SeedState:
    exact_eject: int
    exact_coeff: int
    exact_const: int
    zero_tail_const: int
    q_exact: int


@dataclass(frozen=True)
class LayerSpec:
    exact_eject: int
    exact_coeff: int
    exact_const: int
    residual_lower_bound: int
    residual_coeff: int
    residual_const: int
    zero_exact_coeff: int
    zero_exact_const: int
    zero_exact_shift: int
    zero_residual_coeff: int
    zero_residual_const: int
    zero_residual_shift: int
    q_exact: int
    q_residual: int


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def word(n: int) -> str:
    if n not in NUMBER_WORDS:
        raise KeyError(f"missing number-word mapping for {n}")
    return NUMBER_WORDS[n]


def build_specs(seed: SeedState, end_eject: int) -> list[LayerSpec]:
    specs: list[LayerSpec] = []
    exact_eject = seed.exact_eject
    exact_coeff = seed.exact_coeff
    exact_const = seed.exact_const
    zero_tail_const = seed.zero_tail_const
    q_exact = seed.q_exact

    while exact_eject <= end_eject:
        residual_lower_bound = exact_eject + 1
        residual_coeff = exact_coeff
        residual_const = exact_const + exact_coeff // 2
        zero_exact_coeff = 27 * exact_coeff
        zero_residual_coeff = zero_exact_coeff
        zero_even_const = zero_tail_const
        zero_odd_const = zero_tail_const + zero_exact_coeff // 2
        q_residual = (2187 + q_exact) // 2

        candidates = [zero_even_const, zero_odd_const]
        exact_candidates = [cand for cand in candidates if (cand - exact_const) % exact_coeff == 0]
        residual_candidates = [cand for cand in candidates if (cand - residual_const) % exact_coeff == 0]
        if len(exact_candidates) != 1 or len(residual_candidates) != 1:
            raise ValueError(f"could not resolve zero-shell parity split for eject {exact_eject}")
        zero_exact_const = exact_candidates[0]
        zero_residual_const = residual_candidates[0]
        if zero_exact_const == zero_residual_const:
            raise ValueError(f"degenerate zero-shell split for eject {exact_eject}")

        zero_exact_shift_num = zero_exact_const - exact_const
        zero_residual_shift_num = zero_residual_const - residual_const

        specs.append(
            LayerSpec(
                exact_eject=exact_eject,
                exact_coeff=exact_coeff,
                exact_const=exact_const,
                residual_lower_bound=residual_lower_bound,
                residual_coeff=residual_coeff,
                residual_const=residual_const,
                zero_exact_coeff=zero_exact_coeff,
                zero_exact_const=zero_exact_const,
                zero_exact_shift=zero_exact_shift_num // exact_coeff,
                zero_residual_coeff=zero_residual_coeff,
                zero_residual_const=zero_residual_const,
                zero_residual_shift=zero_residual_shift_num // exact_coeff,
                q_exact=q_exact,
                q_residual=q_residual,
            )
        )

        exact_eject += 1
        exact_coeff *= 2
        exact_const = residual_const
        zero_tail_const = zero_residual_const
        q_exact = q_residual

    return specs


def theorem_block(spec: LayerSpec) -> str:
    eject = spec.exact_eject
    residual = spec.residual_lower_bound
    coeff = spec.exact_coeff
    const = spec.exact_const
    resid_const = spec.residual_const
    dst_coeff = 27 * coeff // 32
    m_coeff = coeff // 64
    m_exact = (const - 13) // 64
    m_resid = (resid_const - 13) // 64
    dst_exact_const = 54 * m_exact + 11
    dst_resid_const = 54 * m_resid + 11

    exact_name = f"dst_slice_eq_4_{eject}_of_src_base_eq_{coeff}r_add_{const}"
    residual_name = f"{word(residual)}_le_dst_eject_of_src_base_eq_{coeff}r_add_{resid_const}"
    zero_exact_name = (
        f"dst_slice_eq_4_{eject}_of_src_base_eq_{spec.zero_exact_coeff}r_add_{spec.zero_exact_const}"
    )
    zero_residual_name = (
        f"{word(residual)}_le_dst_eject_of_src_base_eq_{spec.zero_residual_coeff}r_add_{spec.zero_residual_const}"
    )

    return textwrap.dedent(
        f"""
        /-- First exact refinement of the residual `dst.eject ≥ {eject}` time-4 branch:
            `base = {coeff}*r + {const}` lands exactly on destination slice `(4,{eject})`. -/
        theorem {exact_name}
            {{B : ℕ}} (τ : RegimeIIBadFrontierTransition B)
            (ht : τ.src.src.time = 3) (he : τ.src.src.eject = 1)
            {{r : ℕ}} (hr : τ.src.src.base = {coeff} * r + {const}) :
            τ.dst.src.time = 4 ∧ τ.dst.src.eject = {eject} := by
          have hm : τ.src.src.base = 64 * ({m_coeff} * r + {m_exact}) + 13 := by
            calc
              τ.src.src.base = {coeff} * r + {const} := hr
              _ = 64 * ({m_coeff} * r + {m_exact}) + 13 := by ring
          have htime : τ.dst.src.time = 4 :=
            dst_time_eq_four_of_src_base_eq_64m_add_13 τ ht he hm
          have hbase : τ.dst.src.base = {dst_coeff} * r + {dst_exact_const} := by
            calc
              τ.dst.src.base = 54 * ({m_coeff} * r + {m_exact}) + 11 :=
                dst_base_eq_54m_add_11_of_src_base_eq_64m_add_13 τ ht he hm
              _ = {dst_coeff} * r + {dst_exact_const} := by ring
          have heject' : τ.dst.src.eject = {eject} := by
            have hadm : τ.dst.src.eject = v2 (3 ^ τ.dst.src.time * τ.dst.src.base - 1) :=
              τ.dst.admissible.2.2
            rw [htime, hbase] at hadm
            have hodd : ¬ 2 ∣ (4374 * r + {spec.q_exact}) := by
              intro h2
              have hmod : (4374 * r + {spec.q_exact}) % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
              omega
            have hfac : 3 ^ 4 * ({dst_coeff} * r + {dst_exact_const}) - 1 = 2 ^ {eject} * (4374 * r + {spec.q_exact}) := by
              norm_num
              omega
            have hv2 : v2 (3 ^ 4 * ({dst_coeff} * r + {dst_exact_const}) - 1) = {eject} := by
              calc
                v2 (3 ^ 4 * ({dst_coeff} * r + {dst_exact_const}) - 1) =
                    v2 (2 ^ {eject} * (4374 * r + {spec.q_exact})) := by
                      rw [hfac]
                _ = {eject} := by
                    simpa using v2_pow_mul_of_not_two_dvd {eject} (4374 * r + {spec.q_exact}) hodd
            rw [hv2] at hadm
            exact hadm
          exact ⟨htime, heject'⟩

        /-- Residual branch after the exact `(4,{eject})` split:
            `base = {coeff}*r + {resid_const}` still lands at `time = 4`, now with
            destination ejection valuation at least `{residual}`. -/
        theorem {residual_name}
            {{B : ℕ}} (τ : RegimeIIBadFrontierTransition B)
            (ht : τ.src.src.time = 3) (he : τ.src.src.eject = 1)
            {{r : ℕ}} (hr : τ.src.src.base = {coeff} * r + {resid_const}) :
            τ.dst.src.time = 4 ∧ {residual} ≤ τ.dst.src.eject := by
          have hm : τ.src.src.base = 64 * ({m_coeff} * r + {m_resid}) + 13 := by
            calc
              τ.src.src.base = {coeff} * r + {resid_const} := hr
              _ = 64 * ({m_coeff} * r + {m_resid}) + 13 := by ring
          have htime : τ.dst.src.time = 4 :=
            dst_time_eq_four_of_src_base_eq_64m_add_13 τ ht he hm
          have hbase : τ.dst.src.base = {dst_coeff} * r + {dst_resid_const} := by
            calc
              τ.dst.src.base = 54 * ({m_coeff} * r + {m_resid}) + 11 :=
                dst_base_eq_54m_add_11_of_src_base_eq_64m_add_13 τ ht he hm
              _ = {dst_coeff} * r + {dst_resid_const} := by ring
          have heject_ge : {residual} ≤ τ.dst.src.eject := by
            have hadm : τ.dst.src.eject = v2 (3 ^ τ.dst.src.time * τ.dst.src.base - 1) :=
              τ.dst.admissible.2.2
            rw [htime, hbase] at hadm
            have hfac : 3 ^ 4 * ({dst_coeff} * r + {dst_resid_const}) - 1 = 2 ^ {residual} * (2187 * r + {spec.q_residual}) := by
              norm_num
              omega
            have hdiv : 2 ^ {residual} ∣ 3 ^ 4 * ({dst_coeff} * r + {dst_resid_const}) - 1 := by
              refine ⟨2187 * r + {spec.q_residual}, ?_⟩
              exact hfac
            have hpos : 0 < 3 ^ 4 * ({dst_coeff} * r + {dst_resid_const}) - 1 := by
              norm_num
              omega
            have hv2_ge : {residual} ≤ v2 (3 ^ 4 * ({dst_coeff} * r + {dst_resid_const}) - 1) := by
              by_contra hlt
              have hpow : v2 (3 ^ 4 * ({dst_coeff} * r + {dst_resid_const}) - 1) + 1 ≤ {residual} := by
                omega
              have hdiv' :
                  2 ^ (v2 (3 ^ 4 * ({dst_coeff} * r + {dst_resid_const}) - 1) + 1) ∣
                    3 ^ 4 * ({dst_coeff} * r + {dst_resid_const}) - 1 := by
                  exact dvd_trans (Nat.pow_dvd_pow 2 hpow) hdiv
              exact (v2_pow_succ_not_dvd (3 ^ 4 * ({dst_coeff} * r + {dst_resid_const}) - 1) hpos) hdiv'
            rw [hadm]
            exact hv2_ge
          exact ⟨htime, heject_ge⟩

        /-- Zero-shell wrapper of the exact `(4,{eject})` split:
            `base = {spec.zero_exact_coeff}*r + {spec.zero_exact_const}` lands exactly on
            destination slice `(4,{eject})`. -/
        theorem {zero_exact_name}
            {{B : ℕ}} (τ : RegimeIIBadFrontierTransition B)
            (ht : τ.src.src.time = 3) (he : τ.src.src.eject = 1)
            {{r : ℕ}} (hr : τ.src.src.base = {spec.zero_exact_coeff} * r + {spec.zero_exact_const}) :
            τ.dst.src.time = 4 ∧ τ.dst.src.eject = {eject} := by
          have hr' : τ.src.src.base = {coeff} * (27 * r + {spec.zero_exact_shift}) + {const} := by
            calc
              τ.src.src.base = {spec.zero_exact_coeff} * r + {spec.zero_exact_const} := hr
              _ = {coeff} * (27 * r + {spec.zero_exact_shift}) + {const} := by ring
          simpa using
            {exact_name} (r := 27 * r + {spec.zero_exact_shift}) τ ht he hr'

        /-- Zero-shell wrapper of the residual `dst.eject ≥ {residual}` branch:
            `base = {spec.zero_residual_coeff}*r + {spec.zero_residual_const}` still lands at
            `time = 4`, now with destination ejection valuation at least `{residual}`. -/
        theorem {zero_residual_name}
            {{B : ℕ}} (τ : RegimeIIBadFrontierTransition B)
            (ht : τ.src.src.time = 3) (he : τ.src.src.eject = 1)
            {{r : ℕ}} (hr : τ.src.src.base = {spec.zero_residual_coeff} * r + {spec.zero_residual_const}) :
            τ.dst.src.time = 4 ∧ {residual} ≤ τ.dst.src.eject := by
          have hr' : τ.src.src.base = {coeff} * (27 * r + {spec.zero_residual_shift}) + {resid_const} := by
            calc
              τ.src.src.base = {spec.zero_residual_coeff} * r + {spec.zero_residual_const} := hr
              _ = {coeff} * (27 * r + {spec.zero_residual_shift}) + {resid_const} := by ring
          simpa using
            {residual_name} (r := 27 * r + {spec.zero_residual_shift}) τ ht he hr'
        """
    ).strip()


def generated_block(specs: list[LayerSpec]) -> str:
    return "\n\n\n".join(theorem_block(spec) for spec in specs) + "\n\n"


def expand_start_to_attached_doc_comment(source_text: str, theorem_start: int) -> int:
    comment_start = source_text.rfind("/--", 0, theorem_start)
    if comment_start == -1:
        return theorem_start

    comment_end = source_text.find("-/", comment_start, theorem_start)
    if comment_end == -1:
        return theorem_start

    if source_text[comment_end + 2 : theorem_start].strip():
        return theorem_start

    line_start = source_text.rfind("\n", 0, comment_start)
    if line_start == -1:
        return 0
    return line_start + 1


def strip_and_insert_generated_region(source_text: str, start_layer: int, block: str) -> str:
    time5_marker = "/-- First exact refinement of the `time = 5` shell:"
    end = source_text.find(time5_marker)
    if end == -1:
        raise ValueError("could not find time=5 insertion marker")

    existing_start = source_text.find(f"theorem dst_slice_eq_4_{start_layer}_of_src_base_eq_")
    if existing_start == -1:
        existing_start = end
    else:
        existing_start = expand_start_to_attached_doc_comment(source_text, existing_start)

    return source_text[:existing_start] + block + source_text[end:]


def sandbox_copy(base_repo: Path, sandbox_repo: Path) -> None:
    ignore = shutil.ignore_patterns(".git", ".lake", "__pycache__", "*.olean", "*.ilean")
    shutil.copytree(base_repo, sandbox_repo, symlinks=True, ignore=ignore)

    sandbox_lake = sandbox_repo / ".lake"
    sandbox_lake.mkdir(exist_ok=True)
    (sandbox_lake / "packages").symlink_to(base_repo / ".lake" / "packages")
    shutil.copytree(base_repo / ".lake" / "build", sandbox_lake / "build")
    shutil.copytree(base_repo / ".lake" / "config", sandbox_lake / "config")


def run_logged(command: list[str], cwd: Path, log_path: Path) -> int:
    with log_path.open("w") as log_file:
        process = subprocess.run(
            command,
            cwd=cwd,
            stdout=log_file,
            stderr=subprocess.STDOUT,
            text=True,
        )
    return process.returncode


def write_json(path: Path, payload: object) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def verify_target(
    base_repo: Path,
    artifact_root: Path,
    start_layer: int,
    target_layer: int,
    start_stagger_seconds: float,
    specs: list[LayerSpec],
    base_source: str,
) -> dict[str, object]:
    run_root = artifact_root / f"eject-{target_layer}"
    sandbox_repo = run_root / "repo"
    run_root.mkdir(parents=True, exist_ok=False)

    launch_delay_seconds = max(0.0, (target_layer - start_layer) * start_stagger_seconds)
    if launch_delay_seconds > 0:
        time.sleep(launch_delay_seconds)

    started_at = utc_now()
    t0 = time.time()

    sandbox_copy(base_repo, sandbox_repo)

    active_specs = [spec for spec in specs if start_layer <= spec.exact_eject <= target_layer]
    block = generated_block(active_specs)
    patched_source = strip_and_insert_generated_region(base_source, start_layer, block)
    lean_path = sandbox_repo / "UFRF" / "CollatzConcurrentScales.lean"
    lean_path.write_text(patched_source)

    write_json(run_root / "plan.json", {
        "start_layer": start_layer,
        "target_layer": target_layer,
        "launch_delay_seconds": launch_delay_seconds,
        "generated_layers": [asdict(spec) for spec in active_specs],
        "source_sha256": sha256_text(patched_source),
        "started_at": started_at,
    })
    (run_root / "generated_block.lean").write_text(block)

    build_log = run_root / "build.log"
    build_exit = run_logged(["lake", "build", "UFRF.CollatzConcurrentScales"], sandbox_repo, build_log)

    index_exit = None
    if build_exit == 0:
        index_exit = run_logged(
            [
                "python3",
                "scripts/generate_decl_index.py",
                "--input",
                "UFRF/CollatzConcurrentScales.lean",
                "--json",
                "docs/proofs/COLLATZ_CONCURRENT_SYMBOL_INDEX.json",
                "--markdown",
                "docs/proofs/COLLATZ_CONCURRENT_SYMBOL_INDEX.md",
                "--title",
                "Collatz Concurrent Scales Symbol Index",
            ],
            sandbox_repo,
            run_root / "index.log",
        )

    finished_at = utc_now()
    duration_seconds = round(time.time() - t0, 3)

    result = {
        "start_layer": start_layer,
        "target_layer": target_layer,
        "build_exit_code": build_exit,
        "index_exit_code": index_exit,
        "success": build_exit == 0 and (index_exit in (None, 0)),
        "launch_delay_seconds": launch_delay_seconds,
        "started_at": started_at,
        "finished_at": finished_at,
        "duration_seconds": duration_seconds,
        "artifact_dir": str(run_root),
        "source_sha256": sha256_text(patched_source),
    }
    write_json(run_root / "result.json", result)
    return result


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate cumulative eject-tail layers and verify them in isolated "
            "sandboxes with optional parallel builds."
        )
    )
    parser.add_argument("--start-layer", type=int, default=15)
    parser.add_argument("--end-layer", type=int, default=28)
    parser.add_argument("--workers", type=int, default=max(1, min(8, (os.cpu_count() or 4) // 2)))
    parser.add_argument(
        "--start-stagger-seconds",
        type=float,
        default=1.0,
        help="Delay each target start by N seconds relative to the previous target.",
    )
    parser.add_argument("--plan-only", action="store_true")
    parser.add_argument(
        "--artifact-root",
        type=Path,
        default=None,
        help="Directory for telemetry output. Defaults to a fresh temp directory.",
    )
    parser.add_argument("--seed-layer", type=int, default=15)
    parser.add_argument("--seed-exact-coeff", type=int, default=2097152)
    parser.add_argument("--seed-exact-const", type=int, default=526925)
    parser.add_argument(
        "--seed-zero-tail-const",
        type=int,
        default=15206989,
        help="The zero-shell residual constant just before the start layer split.",
    )
    parser.add_argument("--seed-q-exact", type=int, default=1099)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    base_source = (repo_root / "UFRF" / "CollatzConcurrentScales.lean").read_text()

    seed = SeedState(
        exact_eject=args.seed_layer,
        exact_coeff=args.seed_exact_coeff,
        exact_const=args.seed_exact_const,
        zero_tail_const=args.seed_zero_tail_const,
        q_exact=args.seed_q_exact,
    )
    specs = build_specs(seed, args.end_layer)

    summary = {
        "repo_root": str(repo_root),
        "generated_at": utc_now(),
        "start_layer": args.start_layer,
        "end_layer": args.end_layer,
        "workers": args.workers,
        "start_stagger_seconds": args.start_stagger_seconds,
        "seed": asdict(seed),
        "layers": [asdict(spec) for spec in specs if args.start_layer <= spec.exact_eject <= args.end_layer],
    }

    if args.plan_only:
        json.dump(summary, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
        return 0

    if args.artifact_root is None:
        timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        artifact_root = Path(tempfile.gettempdir()) / f"collatz-eject-batch-{timestamp}"
    else:
        artifact_root = args.artifact_root
    artifact_root.mkdir(parents=True, exist_ok=False)
    write_json(artifact_root / "summary.json", summary)

    targets = list(range(args.start_layer, args.end_layer + 1))
    results: list[dict[str, object]] = []

    with cf.ThreadPoolExecutor(max_workers=args.workers) as executor:
        futures = {
            executor.submit(
                verify_target,
                repo_root,
                artifact_root,
                args.start_layer,
                target,
                args.start_stagger_seconds,
                specs,
                base_source,
            ): target
            for target in targets
        }
        for future in cf.as_completed(futures):
            target = futures[future]
            result = future.result()
            results.append(result)
            status = "ok" if result["success"] else "fail"
            print(f"[{status}] eject-{target}: {result['artifact_dir']}")

    results.sort(key=lambda item: int(item["target_layer"]))
    write_json(artifact_root / "results.json", results)

    failures = [result for result in results if not result["success"]]
    if failures:
        print(f"\nFailures: {len(failures)}")
        print(f"Telemetry root: {artifact_root}")
        return 1

    print(f"\nAll targets succeeded: eject-{args.start_layer} through eject-{args.end_layer}")
    print(f"Telemetry root: {artifact_root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
