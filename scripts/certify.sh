#!/usr/bin/env bash
set -e

# Change to the root of the project
cd "$(dirname "$0")/.."

# First run standard verification
./scripts/verify.sh

echo "Running deep axiomatic audit..."

# Look for direct axiom declarations starting at beginning of line or after spaces.
AXIOMS=$(rg -n '^\s*axiom ' UFRF --glob '*.lean' || true)

if [ -n "$AXIOMS" ]; then
    echo "❌ ERROR: Found custom 'axiom' declarations:"
    echo "$AXIOMS"
    exit 1
else
    echo "✅ No custom 'axiom' declarations found."
fi

# Report native_decide usage for manual audit.
NATIVE=$(rg -n '\bnative_decide\b' UFRF --glob '*.lean' || true)

if [ -n "$NATIVE" ]; then
    NATIVE_COUNT=$(printf "%s\n" "$NATIVE" | wc -l | tr -d ' ')
    echo "ℹ Found $NATIVE_COUNT 'native_decide' occurrences."
    echo "ℹ Policy: allowed only on decidable Nat/Fin-style arithmetic and finite case checks."
else
    echo "✅ No 'native_decide' tactics found."
fi

echo "✅ Project is fully certified under the zero-custom-axiom policy."
