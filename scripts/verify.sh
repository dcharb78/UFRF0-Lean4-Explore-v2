#!/usr/bin/env bash
set -e

# Change to the root of the project
cd "$(dirname "$0")/.."

echo "Running sync_modules.py to prevent drift..."
python3 scripts/sync_modules.py

echo "Building UFRF..."
lake build

echo "Checking for executable sorry placeholders..."
SORRIES=$(rg -n '(:=|by|=>).*sorry|^\s*sorry\s*$' UFRF --glob '*.lean' || true)

if [ -n "$SORRIES" ]; then
    echo "❌ ERROR: Found executable 'sorry' placeholders:"
    echo "$SORRIES"
    exit 1
else
    echo "✅ No executable 'sorry' placeholders found. Build verified."
fi
