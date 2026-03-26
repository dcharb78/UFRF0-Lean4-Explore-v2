#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

mode="${1:-}"
if [[ -n "$mode" && "$mode" != "--certify" ]]; then
    echo "Usage: ./scripts/clean_handoff.sh [--certify]"
    exit 2
fi

echo "Checking that the repository starts clean..."
if ! git diff --quiet --ignore-submodules --exit-code || ! git diff --cached --quiet --ignore-submodules --exit-code; then
    echo "❌ ERROR: clean_handoff requires a clean tracked worktree before validation."
    git status --short
    exit 1
fi

if [[ "$mode" == "--certify" ]]; then
    ./scripts/certify.sh
else
    ./scripts/verify.sh
fi

echo "Checking patch hygiene..."
git diff --check

echo "Checking that validation preserved a clean tracked worktree..."
if ! git diff --quiet --ignore-submodules --exit-code || ! git diff --cached --quiet --ignore-submodules --exit-code; then
    echo "❌ ERROR: validation left tracked changes in the repository."
    git status --short
    exit 1
fi

echo "✅ Repository is validated and worktree-clean."
