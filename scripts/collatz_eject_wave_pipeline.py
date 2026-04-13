#!/usr/bin/env python3

from __future__ import annotations

import argparse
import importlib.util
import json
import subprocess
import sys
import tempfile
from dataclasses import asdict
from datetime import datetime, timezone
from pathlib import Path


MAX_WAVE_SIZE = 10


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def load_batch_module(script_path: Path):
    spec = importlib.util.spec_from_file_location("collatz_eject_batch", script_path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run residual/eject telemetry in sequential waves of at most 10 targets, "
            "keeping at most 10 Lean builds active at a time and resetting the "
            "1-second start stagger for each wave."
        )
    )
    parser.add_argument("--start-layer", type=int, default=33)
    parser.add_argument("--end-layer", type=int, default=80)
    parser.add_argument("--batch-size", type=int, default=10)
    parser.add_argument("--workers", type=int, default=10)
    parser.add_argument("--start-stagger-seconds", type=float, default=1.0)
    parser.add_argument("--artifact-root", type=Path, default=None)
    parser.add_argument("--plan-only", action="store_true")
    parser.add_argument(
        "--seed-layer",
        type=int,
        default=None,
        help="First exact eject generated from the supplied seed. Defaults to --start-layer.",
    )
    parser.add_argument(
        "--seed-mode",
        choices=["exact", "residual"],
        default="residual",
        help="Interpret the initial seed as either an exact split or a residual law.",
    )
    parser.add_argument("--seed-exact-coeff", type=int, default=None)
    parser.add_argument("--seed-exact-const", type=int, default=None)
    parser.add_argument("--seed-zero-tail-const", type=int, default=None)
    parser.add_argument("--seed-q-exact", type=int, default=None)
    parser.add_argument("--seed-residual-coeff", type=int, default=None)
    parser.add_argument("--seed-residual-const", type=int, default=None)
    parser.add_argument("--seed-q-residual", type=int, default=None)
    return parser.parse_args()


def ensure_limits(args: argparse.Namespace) -> None:
    if args.batch_size <= 0:
        raise SystemExit("--batch-size must be positive")
    if args.batch_size > MAX_WAVE_SIZE:
        raise SystemExit(f"--batch-size must be at most {MAX_WAVE_SIZE}")
    if args.workers <= 0:
        raise SystemExit("--workers must be positive")
    if args.workers > MAX_WAVE_SIZE:
        raise SystemExit(f"--workers must be at most {MAX_WAVE_SIZE}")
    if args.start_layer > args.end_layer:
        raise SystemExit("--start-layer must be <= --end-layer")


def require_fields(pairs: list[tuple[str, object]]) -> None:
    missing = [name for name, value in pairs if value is None]
    if missing:
        raise SystemExit("missing required seed arguments: " + ", ".join(missing))


def build_full_specs(batch_mod, args: argparse.Namespace, seed_layer: int):
    if args.seed_mode == "exact":
        require_fields([
            ("--seed-exact-coeff", args.seed_exact_coeff),
            ("--seed-exact-const", args.seed_exact_const),
            ("--seed-zero-tail-const", args.seed_zero_tail_const),
            ("--seed-q-exact", args.seed_q_exact),
        ])
        seed = batch_mod.SeedState(
            exact_eject=seed_layer,
            exact_coeff=args.seed_exact_coeff,
            exact_const=args.seed_exact_const,
            zero_tail_const=args.seed_zero_tail_const,
            q_exact=args.seed_q_exact,
        )
        specs = batch_mod.build_specs(seed, args.end_layer)
        return args.seed_mode, asdict(seed), specs

    require_fields([
        ("--seed-residual-coeff", args.seed_residual_coeff),
        ("--seed-residual-const", args.seed_residual_const),
        ("--seed-zero-tail-const", args.seed_zero_tail_const),
        ("--seed-q-residual", args.seed_q_residual),
    ])
    seed = batch_mod.ResidualSeedState(
        next_exact_eject=seed_layer,
        residual_coeff=args.seed_residual_coeff,
        residual_const=args.seed_residual_const,
        zero_tail_const=args.seed_zero_tail_const,
        q_residual=args.seed_q_residual,
    )
    specs = batch_mod.build_specs_from_residual(seed, args.end_layer)
    return args.seed_mode, asdict(seed), specs


def wave_seed_for_start(
    batch_mod,
    start_layer: int,
    initial_seed_layer: int,
    initial_seed_mode: str,
    initial_seed: dict[str, int],
    spec_by_eject: dict[int, object],
) -> tuple[str, dict[str, int]]:
    if start_layer == initial_seed_layer:
        return initial_seed_mode, dict(initial_seed)

    prev = spec_by_eject[start_layer - 1]
    seed = batch_mod.ResidualSeedState(
        next_exact_eject=start_layer,
        residual_coeff=prev.residual_coeff,
        residual_const=prev.residual_const,
        zero_tail_const=prev.zero_residual_const,
        q_residual=prev.q_residual,
    )
    return "residual", asdict(seed)


def build_wave_plan(
    batch_mod,
    args: argparse.Namespace,
    seed_layer: int,
    initial_seed_mode: str,
    initial_seed: dict[str, int],
    specs: list[object],
    artifact_root: Path,
) -> list[dict[str, object]]:
    spec_by_eject = {spec.exact_eject: spec for spec in specs}
    waves: list[dict[str, object]] = []

    for wave_index, start in enumerate(range(args.start_layer, args.end_layer + 1, args.batch_size), start=1):
        end = min(start + args.batch_size - 1, args.end_layer)
        seed_mode, seed = wave_seed_for_start(
            batch_mod,
            start,
            seed_layer,
            initial_seed_mode,
            initial_seed,
            spec_by_eject,
        )
        waves.append(
            {
                "wave_index": wave_index,
                "start_layer": start,
                "end_layer": end,
                "seed_mode": seed_mode,
                "seed": seed,
                "artifact_dir": str(artifact_root / f"eject-{start}-to-{end}"),
            }
        )

    return waves


def batch_command(
    repo_root: Path,
    wave: dict[str, object],
    workers: int,
    start_stagger_seconds: float,
) -> list[str]:
    script_path = repo_root / "scripts" / "collatz_eject_batch.py"
    cmd = [
        sys.executable,
        str(script_path),
        "--start-layer",
        str(wave["start_layer"]),
        "--end-layer",
        str(wave["end_layer"]),
        "--workers",
        str(workers),
        "--start-stagger-seconds",
        str(start_stagger_seconds),
        "--artifact-root",
        str(wave["artifact_dir"]),
        "--seed-mode",
        str(wave["seed_mode"]),
        "--seed-layer",
        str(wave["start_layer"]),
    ]

    seed = wave["seed"]
    if wave["seed_mode"] == "exact":
        cmd.extend([
            "--seed-exact-coeff",
            str(seed["exact_coeff"]),
            "--seed-exact-const",
            str(seed["exact_const"]),
            "--seed-zero-tail-const",
            str(seed["zero_tail_const"]),
            "--seed-q-exact",
            str(seed["q_exact"]),
        ])
    else:
        cmd.extend([
            "--seed-residual-coeff",
            str(seed["residual_coeff"]),
            "--seed-residual-const",
            str(seed["residual_const"]),
            "--seed-zero-tail-const",
            str(seed["zero_tail_const"]),
            "--seed-q-residual",
            str(seed["q_residual"]),
        ])

    return cmd


def write_json(path: Path, payload: object) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def main() -> int:
    args = parse_args()
    ensure_limits(args)

    repo_root = Path(__file__).resolve().parents[1]
    batch_mod = load_batch_module(repo_root / "scripts" / "collatz_eject_batch.py")
    seed_layer = args.seed_layer if args.seed_layer is not None else args.start_layer

    initial_seed_mode, initial_seed, specs = build_full_specs(batch_mod, args, seed_layer)

    if args.artifact_root is None:
        timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        artifact_root = Path(tempfile.gettempdir()) / f"collatz-eject-wave-pipeline-{timestamp}"
    else:
        artifact_root = args.artifact_root
    artifact_root.mkdir(parents=True, exist_ok=False)

    waves = build_wave_plan(
        batch_mod,
        args,
        seed_layer,
        initial_seed_mode,
        initial_seed,
        specs,
        artifact_root,
    )

    summary = {
        "generated_at": utc_now(),
        "repo_root": str(repo_root),
        "start_layer": args.start_layer,
        "end_layer": args.end_layer,
        "batch_size": args.batch_size,
        "workers": args.workers,
        "max_wave_size": MAX_WAVE_SIZE,
        "start_stagger_seconds": args.start_stagger_seconds,
        "initial_seed_mode": initial_seed_mode,
        "initial_seed": initial_seed,
        "artifact_root": str(artifact_root),
        "waves": waves,
    }
    write_json(artifact_root / "pipeline_summary.json", summary)

    if args.plan_only:
        json.dump(summary, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
        return 0

    results: list[dict[str, object]] = []
    for wave in waves:
        cmd = batch_command(repo_root, wave, args.workers, args.start_stagger_seconds)
        print(
            f"[wave {wave['wave_index']}] eject-{wave['start_layer']}..{wave['end_layer']} "
            f"seed={wave['seed_mode']} artifact={wave['artifact_dir']}"
        )
        completed = subprocess.run(cmd, cwd=repo_root)
        result = {
            "wave_index": wave["wave_index"],
            "start_layer": wave["start_layer"],
            "end_layer": wave["end_layer"],
            "artifact_dir": wave["artifact_dir"],
            "returncode": completed.returncode,
            "finished_at": utc_now(),
        }
        results.append(result)
        write_json(artifact_root / "pipeline_results.json", results)
        if completed.returncode != 0:
            print(f"[fail] wave {wave['wave_index']} stopped the pipeline")
            return completed.returncode

    print(f"\nAll waves succeeded through eject-{args.end_layer}")
    print(f"Pipeline root: {artifact_root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
