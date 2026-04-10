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
    - the remaining residual shell `base = 2048*r + 1517` is now split into
      its first three exact higher-time cases:
      - `base = 4096*r + 3565` gives `dst.time = 10` and
        `dst.base = 54*r + 47`
      - `base = 8192*r + 5613` gives `dst.time = 11` and
        `dst.base = 54*r + 37`
      - `base = 16384*r + 1517` gives `dst.time = 12` and
        `dst.base = 54*r + 5`
    - the remaining residual shell `base = 16384*r + 9709` is now split into
      its first five exact higher-time cases:
      - `base = 32768*r + 26093` gives `dst.time = 13` and
        `dst.base = 54*r + 43`
      - `base = 65536*r + 42477` gives `dst.time = 14` and
        `dst.base = 54*r + 35`
      - `base = 131072*r + 75245` gives `dst.time = 15` and
        `dst.base = 54*r + 31`
      - `base = 262144*r + 140781` gives `dst.time = 16` and
        `dst.base = 54*r + 29`
      - `base = 524288*r + 9709` gives `dst.time = 17` and
        `dst.base = 54*r + 1`
    - the remaining residual shell `base = 524288*r + 271853` is now split
      into its first four exact higher-time cases:
      - `base = 1048576*r + 796141` gives `dst.time = 18` and
        `dst.base = 54*r + 41`
      - `base = 2097152*r + 271853` gives `dst.time = 19` and
        `dst.base = 54*r + 7`
      - `base = 4194304*r + 1320429` gives `dst.time = 20` and
        `dst.base = 54*r + 17`
      - `base = 8388608*r + 7611885` gives `dst.time = 21` and
        `dst.base = 54*r + 49`
    - the remaining residual shell `base = 8388608*r + 3417581` is now split
      into its first four exact higher-time cases:
      - `base = 16777216*r + 3417581` gives `dst.time = 22` and
        `dst.base = 54*r + 11`
      - `base = 33554432*r + 11806189` gives `dst.time = 23` and
        `dst.base = 54*r + 19`
      - `base = 67108864*r + 28583405` gives `dst.time = 24` and
        `dst.base = 54*r + 23`
      - `base = 134217728*r + 62137837` gives `dst.time = 25` and
        `dst.base = 54*r + 25`
    - the remaining residual shell `base = 134217728*r + 129246701` is now
      split into its first two exact higher-time cases:
      - `base = 268435456*r + 263464429` gives `dst.time = 26` and
        `dst.base = 54*r + 53`
      - `base = 536870912*r + 129246701` gives `dst.time = 27` and
        `dst.base = 54*r + 13`
    - the remaining residual shell `base = 536870912*r + 397682157` is now
      split into its first three exact higher-time cases:
      - `base = 1073741824*r + 934553069` gives `dst.time = 28` and
        `dst.base = 54*r + 47`
      - `base = 2147483648*r + 1471423981` gives `dst.time = 29` and
        `dst.base = 54*r + 37`
      - `base = 4294967296*r + 397682157` gives `dst.time = 30` and
        `dst.base = 54*r + 5`
    - the remaining residual shell `base = 4294967296*r + 2545165805` is now
      split into its first five exact higher-time cases:
      - `base = 8589934592*r + 6840133101` gives `dst.time = 31` and
        `dst.base = 54*r + 43`
      - `base = 17179869184*r + 11135100397` gives `dst.time = 32` and
        `dst.base = 54*r + 35`
      - `base = 34359738368*r + 19725034989` gives `dst.time = 33` and
        `dst.base = 54*r + 31`
      - `base = 68719476736*r + 36904904173` gives `dst.time = 34` and
        `dst.base = 54*r + 29`
      - `base = 137438953472*r + 2545165805` gives `dst.time = 35` and
        `dst.base = 54*r + 1`
    - the remaining residual shell `base = 137438953472*r + 71264642541` is
      now split into its first four exact higher-time cases:
      - `base = 274877906944*r + 208703596013` gives `dst.time = 36` and
        `dst.base = 54*r + 41`
      - `base = 549755813888*r + 71264642541` gives `dst.time = 37` and
        `dst.base = 54*r + 7`
      - `base = 1099511627776*r + 346142549485` gives `dst.time = 38` and
        `dst.base = 54*r + 17`
      - `base = 2199023255552*r + 1995409991149` gives `dst.time = 39` and
        `dst.base = 54*r + 49`
    - the remaining residual shell `base = 2199023255552*r + 895898363373` is
      now split into its first four exact higher-time cases:
      - `base = 4398046511104*r + 895898363373` gives `dst.time = 40` and
        `dst.base = 54*r + 11`
      - `base = 8796093022208*r + 3094921618925` gives `dst.time = 41` and
        `dst.base = 54*r + 19`
      - `base = 17592186044416*r + 7492968130029` gives `dst.time = 42` and
        `dst.base = 54*r + 23`
      - `base = 35184372088832*r + 16289061152237` gives `dst.time = 43` and
        `dst.base = 54*r + 25`
    - the remaining residual shell `base = 35184372088832*r + 33881247196653` is
      now split into its first two exact higher-time cases:
      - `base = 70368744177664*r + 69065619285485` gives `dst.time = 44` and
        `dst.base = 54*r + 53`
      - `base = 140737488355328*r + 33881247196653` gives `dst.time = 45` and
        `dst.base = 54*r + 13`
    - the remaining residual shell is now
      `base = 140737488355328*r + 104249991374317`
      - it satisfies `dst.time ≥ 46`
      - it carries the transport law
        `2^(dst.time - 46) * dst.base = 27*r + 20`
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
exit is reduced to an explicit shell ladder through exact `time = 45`, leaving
only one thinner non-self-return residual shell
`base = 140737488355328*r + 104249991374317` together with its intrinsic
transport law. The `% 64 = 29` branch remains the only thin self-return
branch, while the non-self-return higher-time side is now almost entirely a
finite list of explicit destination slices. More structurally, the residual
transport law first returned to the earlier `27*r + 26` shape from the old
`base = 512*r + 493` shell, then re-entered the older `27*r + 20` stage, then
mirrored the older `27*r + 16` stage completely, then mirrored the older
`27*r + 14` stage, then mirrored the older `27*r + 11` stage, and has now
returned again to the older `27*r + 20` stage. This is strong evidence for a
genuine source-state renormalization cycle rather than an endless stream of
novel higher-time obstructions.

## Best Next Step

The next theorem family should use those verified shell laws to:

- exploit the verified return to the older residual transport law
  `2^(dst.time - 46) * dst.base = 27*r + 20` on
  `base = 140737488355328*r + 104249991374317`
  - the first direct mirrored subfamilies should be:
    - `base = 281474976710656*r + 244987479729645`, which should give
      `dst.time = 46` and `dst.base = 54*r + 47`
    - `base = 562949953421312*r + 385724968084973`, which should give
      `dst.time = 47` and `dst.base = 54*r + 37`
    - `base = 1125899906842624*r + 104249991374317`, which should give
      `dst.time = 48` and `dst.base = 54*r + 5`
    - the thinner residual `base = 1125899906842624*r + 667199944795629`
      should satisfy `dst.time ≥ 49` with transport law
      `2^(dst.time - 49) * dst.base = 27*r + 16`
  - after that, formulate the exact source-state recurrence that identifies
    this returning `27*r + 20` law with the earlier verified `time ≥ 28`
    shell, so future shell splits can be reused instead of reproved ad hoc
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
