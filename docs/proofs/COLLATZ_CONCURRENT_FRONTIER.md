# Collatz Concurrent Frontier

This note records the current proof frontier for the intrinsic concurrent /
multiscale Collatz program centered on
`UFRF/CollatzConcurrentScales.lean`.

Read this note before starting new proof work in a fresh conversation.

## Local Name Workflow

For this frontier file, use two layers together:

- Rover / curated memory for theorem clusters, rationale, and best-next-family
  context.
- The generated declaration index for exact local names and line lookup:
  - `docs/proofs/COLLATZ_CONCURRENT_SYMBOL_INDEX.md`
  - `docs/proofs/COLLATZ_CONCURRENT_SYMBOL_INDEX.json`

Regenerate the index after declaration movement with:

`python3 scripts/generate_decl_index.py --input UFRF/CollatzConcurrentScales.lean --json docs/proofs/COLLATZ_CONCURRENT_SYMBOL_INDEX.json --markdown docs/proofs/COLLATZ_CONCURRENT_SYMBOL_INDEX.md --title "Collatz Concurrent Scales Symbol Index"`

If memory, the index, and source disagree about an exact identifier, Lean
source wins.

## Conceptual Intent To Preserve

- Treat the Collatz/UFRF structure as intrinsically concurrent and multiscale.
- Raw `n` is too flat.
- Observer bundles are useful charts, but they are also too flat by
  themselves.
- The correct ontology is the intrinsic compressed Regime-II source state.
- In UFRF language: source state first, projections second, reconstruction
  afterward.
- `65` is not a privileged scale. It is one tractable observer chart.

## Current Source-State Layer

Key intrinsic objects already in the file include:

- `RegimeIIState`
- `regimeIIStateOf`
- `regimeIIStateToBundleFiberState`
- `bundleFiberStateOf_factors_through_regimeIIState`
- `regimeIIBaseThreshold`
- `regimeIINext_lt_iff_base_lt_threshold`
- `regimeIINext_lt_iff_state_base_lt_threshold`

These theorems moved the project from chart-level observations to source-state
classification.

## Important Observer-Layer Obstructions Already Settled

The project already proved that chart data alone is too coarse:

- `bundle65_constant_state_family`
- `bundle65_constant_state_family_exact_zone_split`
- `bundle65_fiber_state_family`
- `bundle65_fiber_state_family_exact_zone_split`

Interpretation: local chart data can recur while intrinsic radial/source-state
data changes, so the decisive theorems must live on the source-state side.

## Main Remaining Global Gap

The conjecture-critical remaining `sorry` is still the theorem
`orbit_shrinks_W_steps` in
`UFRF/CollatzConcurrentScales.lean`.

At the time of writing, this sits at line 646 in the file. Future edits may
shift the exact line, but this theorem remains the global target.

## Current Checkpoint

Current checkpoint:

- Branch: `codex/collatz-memory-loop`
- Commit: `860e158`
- Message: `Split hard (3,1) bad-frontier branch at 832`

Latest intrinsic gain:

- the hard source slice `(time, eject) = (3, 1)` still has the intrinsic split
  into
  - destination slice `(2, 1)`, or
  - destination time at least `4`, or
  - the thinner residual source branch `base % 64 = 29`
- that split is now sharpened by explicit transport on the first two exits:
  - on `base = 32*k + 21`, the `(2,1)` destination base is exactly
    `108*k + 71`
  - on that same branch, the destination next meta-step hits the exact `832`
    zone exactly when `k < 2`, yielding a direct source shrink theorem for
    that subfamily
  - on `base = 32*k + 13`, the higher-time exit satisfies
    `2^(dst.time - 4) * dst.base = 27*k + 11`, hence
    `dst.base ≤ 27*k + 11`
  - that higher-time branch is now parameterized exactly by
    `dst.time = 4 + v2(27*k + 11)` and
    `dst.base = (27*k + 11) / 2^v2(27*k + 11)`
  - that higher-time parameterization is now split into its first explicit
    dyadic shells:
    - `base = 64*m + 13` gives `dst.time = 4` and `dst.base = 54*m + 11`
    - `base = 128*m + 45` gives `dst.time = 5` and `dst.base = 54*m + 19`
    - `base = 256*m + 109` gives `dst.time = 6` and `dst.base = 54*m + 23`
    - `base = 512*m + 237` gives `dst.time = 7` and `dst.base = 54*m + 25`
    - the residual shell `base = 512*m + 493` gives `dst.time ≥ 8` and
      `2^(dst.time - 8) * dst.base = 27*m + 26`
  - the `time = 4` shell `base = 64*m + 13` is now split by actual
    destination ejection:
    - `base = 128*r + 13` gives destination slice `(4,1)`
    - `base = 256*r + 205` gives destination slice `(4,2)`
    - `base = 512*r + 333` gives destination slice `(4,3)`
    - `base = 1024*r + 77` gives destination slice `(4,4)`
    - `base = 2048*r + 1613` gives destination slice `(4,5)`
    - `base = 4096*r + 589` gives destination slice `(4,6)`
    - the residual shell `base = 4096*r + 2637` still has destination
      `time = 4` with `dst.eject ≥ 7`
  - the `time = 5` shell `base = 128*m + 45` is now split by actual
    destination ejection:
    - `base = 256*r + 173` gives destination slice `(5,1)`
    - `base = 512*r + 301` gives destination slice `(5,2)`
    - `base = 1024*r + 45` gives destination slice `(5,3)`
    - `base = 2048*r + 557` gives destination slice `(5,4)`
    - `base = 4096*r + 1581` gives destination slice `(5,5)`
    - `base = 8192*r + 3629` gives destination slice `(5,6)`
    - `base = 16384*r + 7725` gives destination slice `(5,7)`
    - the residual shell `base = 16384*r + 15917` still has destination
      `time = 5` with `dst.eject ≥ 8`
  - the `time = 6` shell `base = 256*m + 109` is now split by actual
    destination ejection:
    - `base = 512*r + 109` gives destination slice `(6,1)`
    - `base = 1024*r + 365` gives destination slice `(6,2)`
    - `base = 2048*r + 1901` gives destination slice `(6,3)`
    - `base = 4096*r + 877` gives destination slice `(6,4)`
    - `base = 8192*r + 7021` gives destination slice `(6,5)`
    - the residual shell `base = 8192*r + 2925` still has destination
      `time = 6` with `dst.eject ≥ 6`
  - the `time = 7` shell `base = 512*m + 237` is now split by actual
    destination ejection:
    - `base = 1024*r + 237` gives destination slice `(7,1)`
    - `base = 2048*r + 749` gives destination slice `(7,2)`
    - `base = 4096*r + 1773` gives destination slice `(7,3)`
    - `base = 8192*r + 3821` gives destination slice `(7,4)`
    - `base = 16384*r + 7917` gives destination slice `(7,5)`
    - `base = 32768*r + 32493` gives destination slice `(7,6)`
    - the residual shell `base = 32768*r + 16109` still has destination
      `time = 7` with `dst.eject ≥ 7`
  - after those verified time-6 and time-7 ladders, the only remaining
    non-self-return higher-time shell from the `13 mod 32` branch is now
    `base = 512*m + 493`
    - it is now split into its first two exact higher-time cases:
      - `base = 1024*r + 1005` gives `dst.time = 8` and
        `dst.base = 54*r + 53`
      - `base = 2048*r + 493` gives `dst.time = 9` and
        `dst.base = 54*r + 13`
    - the remaining residual shell is now `base = 2048*r + 1517`
      - it satisfies `dst.time ≥ 10`
      - it carries the transport law
        `2^(dst.time - 10) * dst.base = 27*r + 20`
  - these exact destination-slice theorems now feed direct shrink corollaries
    at concrete source bases
    - `src.base = 13`
    - `src.base = 45`
    - `src.base = 77`
    - `src.base = 589`
  - because the destination is still on the `832` bad frontier, this branch
    also starts only at `k ≥ 2`

Meaning: the `(2,1)` and `time >= 4` exits are no longer opaque symbolic
cases; they now carry reusable intrinsic transport laws, and the higher-time
exit is reduced to an explicit shell ladder through exact `time = 9`, leaving
only one thinner non-self-return residual shell `base = 2048*r + 1517`
together with its intrinsic transport law. The `% 64 = 29` branch remains the
only thin self-return branch, while the non-self-return higher-time side is now
almost entirely a finite list of explicit destination slices.

## Best Next Step

The next theorem family should use those verified shell laws to:

- split the last non-self-return higher-time shell `base = 2048*r + 1517` by
  the dyadic valuation of `27*r + 20`
  - the first expected subfamilies are:
    - `base = 4096*r + 3565`, which should give `dst.time = 10` and
      `dst.base = 54*r + 47`
    - `base = 8192*r + 5613`, which should give `dst.time = 11` and
      `dst.base = 54*r + 37`
    - `base = 8192*r + 1517`, which should give `dst.time = 12` and
      `dst.base = 27*r + 5`
- keep composing any concrete destination slices with the existing `832`
  exact-zone / dead-slice theorems whenever the threshold is strong enough to
  produce actual source shrink
- keep thinning the residual higher-time shells together with the source
  self-return branch `base % 64 = 29` until the true global frontier is
  isolated

This keeps the work on the source-state side and avoids sliding back into
bundle-only analysis.

## Memory Workflow

Before substantial Collatz proof work:

- use the `ufrf-memory-loop` skill if available
- query recent curated notes in the local curation directory when available:
  `/Users/dcharb/.codex/tools/ufrf-rover/.ufrf_rover/curations/`
- update durable memory after meaningful theorem movement

When updating memory, keep the note short and record:

- what new theorem was added
- what it means
- what it rules out
- what the best next step is
