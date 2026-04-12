#!/usr/bin/env python3

from __future__ import annotations

import json
import subprocess
import sys
from hashlib import sha256
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


def run_git(repo_root: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", *args],
        cwd=repo_root,
        text=True,
    ).strip()


def fmt_ts(path: Path) -> str:
    return datetime.fromtimestamp(path.stat().st_mtime, tz=timezone.utc).strftime(
        "%Y-%m-%dT%H:%M:%SZ"
    )


def file_sha256(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


@dataclass
class WarningFlag:
    label: str
    detail: str


def main() -> int:
    repo_root = Path(__file__).resolve().parents[1]
    declared_git_root = Path(run_git(repo_root, "rev-parse", "--show-toplevel")).resolve()
    branch = run_git(repo_root, "rev-parse", "--abbrev-ref", "HEAD")
    head = run_git(repo_root, "rev-parse", "--short", "HEAD")
    status = run_git(repo_root, "status", "--short")

    lean_path = repo_root / "UFRF" / "CollatzConcurrentScales.lean"
    olean_path = repo_root / ".lake" / "build" / "lib" / "lean" / "UFRF" / "CollatzConcurrentScales.olean"
    frontier_path = repo_root / "docs" / "proofs" / "COLLATZ_CONCURRENT_FRONTIER.md"
    handoff_path = repo_root / "docs" / "proofs" / "COLLATZ_COMPACT_HANDOFF.md"
    index_path = repo_root / "docs" / "proofs" / "COLLATZ_CONCURRENT_SYMBOL_INDEX.json"
    build_status_path = repo_root / "docs" / "proofs" / "COLLATZ_TARGETED_BUILD_STATUS.json"

    with index_path.open() as f:
        index_data = json.load(f)

    index_generated_at = datetime.fromisoformat(index_data["generated_at"])
    if index_generated_at.tzinfo is None:
        index_generated_at = index_generated_at.replace(tzinfo=timezone.utc)
    else:
        index_generated_at = index_generated_at.astimezone(timezone.utc)

    warnings: list[WarningFlag] = []
    source_hash = file_sha256(lean_path)
    build_status = None
    if build_status_path.exists():
        with build_status_path.open() as f:
            build_status = json.load(f)

    source_matches_recorded_green = False
    if build_status is not None:
        source_matches_recorded_green = (
            build_status.get("source") == "UFRF/CollatzConcurrentScales.lean"
            and build_status.get("source_sha256") == source_hash
        )

    if declared_git_root != repo_root:
        warnings.append(
            WarningFlag(
                "repo-root-mismatch",
                f"script repo root {repo_root} != git root {declared_git_root}",
            )
        )

    if olean_path.exists():
        if lean_path.stat().st_mtime > olean_path.stat().st_mtime and not source_matches_recorded_green:
            warnings.append(
                WarningFlag(
                    "source-ahead-of-build",
                    f"{lean_path.name} is newer than the built olean",
                )
            )
    else:
        if not source_matches_recorded_green:
            warnings.append(
                WarningFlag(
                    "missing-olean",
                    f"missing build artifact at {olean_path}",
                )
            )

    lean_mtime = datetime.fromtimestamp(lean_path.stat().st_mtime, tz=timezone.utc)
    if lean_mtime > index_generated_at and not source_matches_recorded_green:
        warnings.append(
            WarningFlag(
                "source-ahead-of-index",
                f"Lean source mtime {lean_mtime.strftime('%Y-%m-%dT%H:%M:%SZ')} > index generated_at {index_generated_at.strftime('%Y-%m-%dT%H:%M:%SZ')}",
            )
        )

    for tracked_doc, label in (
        (frontier_path, "frontier-behind-source"),
        (handoff_path, "handoff-behind-source"),
    ):
        if not tracked_doc.exists():
            warnings.append(
                WarningFlag(
                    label,
                    f"missing tracked doc {tracked_doc}",
                )
            )
        elif lean_path.stat().st_mtime > tracked_doc.stat().st_mtime and not source_matches_recorded_green:
            warnings.append(
                WarningFlag(
                    label,
                    f"{tracked_doc.name} is older than {lean_path.name}",
                )
            )

    if status:
        warnings.append(
            WarningFlag(
                "dirty-worktree",
                "git status --short is non-empty",
            )
        )

    print("Collatz compact status")
    print(f"repo_root: {repo_root}")
    print(f"git_root: {declared_git_root}")
    print(f"branch: {branch}")
    print(f"head: {head}")
    print()
    print("Artifacts")
    print(f"- lean source: {lean_path} ({fmt_ts(lean_path)})")
    print(f"- lean sha256: {source_hash}")
    if olean_path.exists():
        print(f"- built olean: {olean_path} ({fmt_ts(olean_path)})")
    else:
        print(f"- built olean: missing at {olean_path}")
    print(f"- frontier note: {frontier_path} ({fmt_ts(frontier_path)})")
    if handoff_path.exists():
        print(f"- compact handoff: {handoff_path} ({fmt_ts(handoff_path)})")
    else:
        print(f"- compact handoff: missing at {handoff_path}")
    print(
        f"- symbol index: {index_path} ({index_generated_at.strftime('%Y-%m-%dT%H:%M:%SZ')}, declarations={index_data['declaration_count']})"
    )
    if build_status is not None:
        print(
            f"- recorded green hash: {build_status_path} ({build_status.get('verified_at', 'unknown')}, session={build_status.get('session_id', 'unknown')})"
        )
        print(
            f"  matches current source: {'yes' if source_matches_recorded_green else 'no'}"
        )
    else:
        print(f"- recorded green hash: missing at {build_status_path}")
    print()
    print("Worktree")
    if status:
        print(status)
    else:
        print("- clean")
    print()
    if warnings:
        print("Warnings")
        for warning in warnings:
            print(f"- [{warning.label}] {warning.detail}")
        print()
        warning_labels = {warning.label for warning in warnings}
        if warning_labels == {"dirty-worktree"}:
            print(
                "Compact/new-thread status: SAFE ONLY IF YOU KEEP LAST PUSHED CHECKPOINT AND LOCAL GREEN WORKTREE SEPARATE"
            )
        else:
            print(
                "Compact/new-thread status: NOT SAFE TO FLATTEN INTO ONE VERIFIED SUMMARY"
            )
        return 1

    print("Warnings")
    print("- none")
    print()
    print("Compact/new-thread status: SAFE TO SUMMARIZE FROM CURRENT ON-DISK ARTIFACTS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
