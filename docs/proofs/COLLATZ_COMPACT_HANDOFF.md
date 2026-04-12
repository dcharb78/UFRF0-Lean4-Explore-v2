# Collatz Compact Handoff

This file is the compact-safe handoff layer for fresh threads on
`/tmp/repo-collatz-memory-loop`.

Refresh it before:

- starting a new thread
- compacting or resuming after compaction
- describing status after source moved ahead of the last green build boundary
- handing work from proof changes back into docs, Rover, or the symbol index

## Mandatory Resume Order

1. Read [AGENTS.md](/tmp/repo-collatz-memory-loop/AGENTS.md).
2. Read this file.
3. Read
   [COLLATZ_CONCURRENT_FRONTIER.md](/tmp/repo-collatz-memory-loop/docs/proofs/COLLATZ_CONCURRENT_FRONTIER.md).
4. Use the
   [$ufrf-memory-loop](/Users/dcharb/.codex/skills/ufrf-memory-loop/SKILL.md)
   workflow before substantial proof work.
5. Run `python3 scripts/collatz_compact_status.py` and resolve any warnings
   before flattening status into a single summary.

## Why Compactions Drift

The recurring failure mode is not usually theorem loss. It is boundary loss:

- the latest chat summary merges verified green work with newer unverified
  source edits
- the active terminal is sitting outside the repo, so a reported build result
  may not correspond to `/tmp/repo-collatz-memory-loop`
- Lean source is ahead of the built `olean`, but conversation memory talks as
  though the new theorem is already green
- a failed build can wipe the direct `olean` artifact even when the source is
  later reverted back to the last known green content
- the symbol index and Rover are synced to one boundary while the source file
  has already moved to another

Trust order when artifacts disagree:

1. Lean source plus the latest confirmed green build boundary
2. this handoff file and the frontier note if they explicitly preserve that
   separation
3. Rover curated memory and the generated declaration index
4. compacted chat summaries

## Current Snapshot

This snapshot is intentionally split into the last committed checkpoint and the
current local green worktree.

### Repo Identity

- repo: `/tmp/repo-collatz-memory-loop`
- branch: `codex/collatz-memory-loop`
- last pushed checkpoint: `054e0b3`
- pushed message: `Package affine five-step return-machine self-map`

### Last Green Boundary In The Current Worktree

The current worktree is now green by targeted
`lake build UFRF.CollatzConcurrentScales` through:

- the finite observer-gap package on the higher-time `base ≡ 13 (mod 32)`
  branch
- the normalization bridge from `observerGap9387_832` into the older repeat
  normalization coordinates
- the pure-phase transport law
  `sixteen_mul_dst_observerGap9387_832_eq_twentySeven_mul_src_observerGap9387_832_of_src_repeatThresholdSeedResidue832_eq_zero`
- the chain wrapper
  `sixteen_mul_dst_observerGap9387_832_eq_twentySeven_mul_src_observerGap9387_832_of_repeatCore832Transition_chain`
- the carrier theorem
  `exists_observerGap9387_832_carrier_of_repeatCore832Transition_chain`

The last pushed commit is still:

- `054e0b3`
- `Package affine five-step return-machine self-map`

So the carrier theorem is green in the current worktree, but still lives in
local uncommitted proof state rather than a pushed checkpoint.

The generated declaration index currently on disk reports:

- `generated_at = 2026-04-12T05:53:18.982127+00:00`
- `declaration_count = 1262`

### Local Delta Beyond The Last Pushed Checkpoint

Lean source contains one newer green observer-gap carrier theorem beyond the
last pushed checkpoint:

- [UFRF/CollatzConcurrentScales.lean:9479](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L9479)
  `exists_observerGap9387_832_carrier_of_repeatCore832Transition_chain`

Interpret it as:

- on a two-step repeat-core chain, the shared observer gap already factors as
  one common integer carrier `u`
- source gap = `16 * u`
- destination gap = `27 * u`

This theorem is now green in the local worktree, but it should still be kept
separate from the pushed checkpoint until docs, index, Rover, and git history
have been advanced together.

### Active Verification State

The targeted verification run for the carrier theorem completed successfully:

- session id: `58830`
- command: `lake build UFRF.CollatzConcurrentScales`
- result: success with the familiar pre-existing warnings only
- exact green-source hash is recorded in
  [COLLATZ_TARGETED_BUILD_STATUS.json](/tmp/repo-collatz-memory-loop/docs/proofs/COLLATZ_TARGETED_BUILD_STATUS.json)

### Most Recent Failed Probe

The first attempted deeper observer-gap shell lift was:

- `exists_observerGap9387_832_thirdCarrier_of_repeatCore832Transition_chain3`

That attempt failed the later targeted build and was intentionally removed from
source before this handoff was prepared. It is not part of the current
on-disk theorem boundary and should be rederived fresh rather than assumed to
exist.

### Artifact Sync State

As of this snapshot:

- the direct `olean` artifact may be absent because the later failed build
  cleaned it, but the recorded green source hash in
  [COLLATZ_TARGETED_BUILD_STATUS.json](/tmp/repo-collatz-memory-loop/docs/proofs/COLLATZ_TARGETED_BUILD_STATUS.json)
  matches the current source boundary
- the frontier note and this handoff file should describe the carrier theorem
  as local green work beyond commit `054e0b3`
- the symbol index has been regenerated after the green carrier theorem build
- Rover is now synced through the carrier theorem via
  `20260412T055457Z-verified-by-targeted-lake-build-ufrf-collatzconc.md`

That means the repo is still in a compact-risk state, but a better one than
before:

- the local green boundary is known
- the pushed checkpoint is behind it
- docs and memory must still not flatten those two layers together

## Immediate Next Step

1. confirm the regenerated symbol index now includes the carrier theorem
2. write one short Rover note for the carrier theorem if missing
3. keep the carrier theorem classified as local green work beyond
   `054e0b3` until a new checkpoint is committed
4. continue the structural observer-gap lift by overlapping consecutive carrier
   facts toward a deeper shell pattern `256*v -> 432*v -> 729*v`

## Practical Monitoring Rule

Before any compact or new thread, run:

```bash
python3 scripts/collatz_compact_status.py
```

If it reports warnings, do not describe the state as one merged checkpoint.
Instead explicitly state:

- last green boundary
- current unverified source delta
- sync status of frontier/index/Rover
- whether a targeted build is still running or pending confirmation

## Suggested New-Thread Opener

Continue from `/tmp/repo-collatz-memory-loop` on branch
`codex/collatz-memory-loop`.

Before proof work:

- read `/tmp/repo-collatz-memory-loop/AGENTS.md`
- read `/tmp/repo-collatz-memory-loop/docs/proofs/COLLATZ_COMPACT_HANDOFF.md`
- read `/tmp/repo-collatz-memory-loop/docs/proofs/COLLATZ_CONCURRENT_FRONTIER.md`
- use [$ufrf-memory-loop](/Users/dcharb/.codex/skills/ufrf-memory-loop/SKILL.md)
- run `python3 scripts/collatz_compact_status.py`

Current split state:

- last pushed checkpoint is `054e0b3`
- current local green worktree now includes
  `sixteen_mul_dst_observerGap9387_832_eq_twentySeven_mul_src_observerGap9387_832_of_repeatCore832Transition_chain`
  and
  `exists_observerGap9387_832_carrier_of_repeatCore832Transition_chain`
  at
  [UFRF/CollatzConcurrentScales.lean:9479](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L9479)
- targeted build session `58830` completed green in the actual repo; keep that
  theorem marked as local green work beyond the pushed checkpoint until git,
  docs, index, and Rover are all synced

Immediate objective after confirmation:

- sync frontier/index/Rover to the carrier theorem
- then retry the deeper observer-gap shell lift by overlapping consecutive
  carrier facts, aiming for a `256*v -> 432*v -> 729*v` observer-gap pattern,
  but do not assume the first abandoned theorem statement or proof shape was
  the right one
