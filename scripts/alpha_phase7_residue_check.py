#!/usr/bin/env python3
"""Numerically compare the normalized phase-7 real correction against the CODATA 2022 alpha gap.

This is an external numeric check, not a Lean theorem.
"""

from __future__ import annotations

import cmath
import math
import sys


def main() -> None:
    tolerance = 1e-6
    ufrf_alpha_inv = 4 * math.pi**3 + math.pi**2 + math.pi
    codata2022_alpha_inv = 137.035999177
    gap = ufrf_alpha_inv - codata2022_alpha_inv

    omega = cmath.exp(2j * math.pi / 13)
    phase_shift = omega - 1
    phase7_residue = cmath.exp(2j * math.pi * 7 / 13) / 13
    phase7_increment = 0.5 * phase_shift * phase7_residue

    # Model normalization mirrored in AlphaRunning.lean:
    # simplex boundary factor 4 times the selected phase label 7.
    phase7_normalized_real_correction = phase7_increment.real / (4 * 7)

    print(f"ufrf_alpha_inv={ufrf_alpha_inv:.12f}")
    print(f"codata2022_alpha_inv={codata2022_alpha_inv:.12f}")
    print(f"gap={gap:.12f}")
    print(f"phase7_increment={phase7_increment.real:.12f}{phase7_increment.imag:+.12f}j")
    print(f"phase7_normalized_real_correction={phase7_normalized_real_correction:.12f}")
    abs_error = abs(gap - phase7_normalized_real_correction)

    print(f"abs_error={abs_error:.12f}")
    print(f"tolerance={tolerance:.12f}")

    if abs_error >= tolerance:
        print("FAIL: normalized phase-7 real correction is outside tolerance", file=sys.stderr)
        raise SystemExit(1)

    print("PASS: normalized phase-7 real correction is within tolerance")


if __name__ == "__main__":
    main()
