# Codex Goal: Nested Learning Proof Pass

Use this from the repository root after enabling Codex goals:

```text
/goal Complete the Nested Learning proof pass for UFRF0-Lean4-Explore-v2 without stopping until the new named theorems build cleanly, contain no `sorry`/`admit`/custom `axiom`/hidden trust escape, and the repository verification loop is green.
```

## Objective

Promote the outreach-relevant UFRF claims into named Lean theorems, using only theorem-backed UFRF modules and Lean core concepts already present in the repository. Do not rely on external ML folklore, "known" relationships, assumed physical facts, or semantic placeholders.

## Read First

- `UFRF/Constants.lean`
- `UFRF/BreathingCycle.lean`
- `UFRF/KeplerTriangle.lean`
- `UFRF/DoublingFlip.lean`
- `UFRF/C3Umklapp.lean`
- `UFRF/FibonacciKissing.lean`
- `UFRF/FibonacciPrimeChain.lean`
- `UFRF/KissingHierarchy.lean`
- `UFRF.lean`

## Theorem Targets

- `tau_tier_ceiling`: define the tier ceiling from UFRF cycle length `13` and golden ratio `phi`, with explicit corollaries:
  - `tau_ceiling_M2`: mediator tier. Never call `2` a UFRF prime.
  - `tau_ceiling_M3`: UFRF-prime tier.
  - `tau_ceiling_M5`: UFRF-prime tier.
- `nested_octave_closure`: prove bridge positions of one scale close into seed positions of the next scale in `ZMod 13`, with the transition edge weighted by the Kepler-derived `rest_amplitude = sqrt(phi)`.
- `prime_frequency_separation`: prove the named UFRF frequency set separates the mediator `2` from UFRF primes and keeps the UFRF prime update frequencies pairwise distinct.
- `epsilon_at_flip_position`: prove only the structural residual/flip-position fact available from existing UFRF definitions. Avoid ML claims unless they have a formal predicate in the repo.
- `mobius_closure_at_13`: prove the nested-octave return closes after exactly the 13-position cycle.

## Hard Constraints

- No `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `extern`, `implemented_by`, or `set_option maxHeartbeats 0` in new Lean code.
- No theorem statement may make `2` a UFRF prime. The correct role of `2` is mediator.
- Prefer new top-level names in a focused module, then import that module from `UFRF.lean`.
- Keep proofs small and auditable; split definitions from theorems when it makes the proof kernel easier to inspect.
- If a theorem target is too semantically broad, prove the strongest structural theorem currently supported and leave a clear Lean-level TODO in docs, not in proof code.

## Validation Loop

Run after every checkpoint:

```bash
lake build UFRF.NestedLearning UFRF
./scripts/verify.sh
rg -n "\b(sorry|admit)\b" -g "*.lean"
rg -n '^\s*(axiom|constant|opaque|unsafe)\b|\bimplemented_by\b|\btrustCompiler\b|\bextern\b|^\s*set_option\s+(maxHeartbeats\s+0|autoImplicit\s+true)' -g "*.lean"
```

Before stopping, run a full clean build when practical:

```bash
rm -rf .lake/build
lake build
```

## Stop Condition

Stop only when the new module is imported by `UFRF.lean`, all targeted theorem names that are supportable from existing definitions are present, the validation loop is green, and any remaining unsupported outreach wording is documented as non-formal interpretation rather than hidden inside Lean theorem names.
