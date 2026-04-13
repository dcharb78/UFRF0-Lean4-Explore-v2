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

This snapshot is intentionally split into the older pushed checkpoint and the
current green branch boundary.

### Repo Identity

- repo: `/tmp/repo-collatz-memory-loop`
- branch: `codex/collatz-memory-loop`
- older pushed checkpoint before this boundary: `054e0b3`
- older pushed message: `Package affine five-step return-machine self-map`

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
- the three-step observer-gap shell lift
  `exists_observerGap9387_832_thirdCarrier_of_repeatCore832Transition_chain3`
- the four-step observer-gap shell lift
  `exists_observerGap9387_832_fourthCarrier_of_repeatCore832Transition_chain4`
- the continuation gate theorem
  `exists_observerGap9387_832_fourthCarrier_with_gate_of_repeatCore832Transition_chain5`
- the five-step observer-gap zero theorem
  `observerGap9387_832_eq_zero_of_repeatCore832Transition_chain5`
- the five-step short zero block
  `observerGap9387_832_zero_block_of_repeatCore832Transition_chain5`
- the higher-time affine zero-shell equivalence
  `observerGap9387_832_eq_zero_of_src_base_eq_864m_add_589`
  and
  `exists_src_base_eq_864m_add_589_of_observerGap9387_832_eq_zero_of_src_base_mod32_eq13`
- the higher-time zero-shell transport family
  `two_pow_dst_time_sub_four_mul_dst_base_eq_729m_add_497_of_src_base_eq_864m_add_589`
- the first exact destination-shell split of that family through:
  `dst_time_eq_four_of_src_base_eq_1728m_add_589`,
  `dst_base_eq_1458m_add_497_of_src_base_eq_1728m_add_589`,
  `dst_time_eq_five_of_src_base_eq_3456m_add_1453`,
  `dst_base_eq_1458m_add_613_of_src_base_eq_3456m_add_1453`,
  `dst_time_eq_six_of_src_base_eq_6912m_add_3181`,
  `dst_base_eq_1458m_add_671_of_src_base_eq_6912m_add_3181`,
  `seven_le_dst_time_of_src_base_eq_6912m_add_6637`,
  `two_pow_dst_time_sub_seven_mul_dst_base_eq_729m_add_700_of_src_base_eq_6912m_add_6637`,
  `dst_time_eq_seven_of_src_base_eq_13824m_add_13549`,
  and
  `dst_base_eq_1458m_add_1429_of_src_base_eq_13824m_add_13549`
- the theorem-level reindexing bridge from those zero-shell outputs back into
  the established `54*k + 11/19/23/25` higher-time families via
  `exists_dst_time4_base_eq_54k_add_11_of_src_base_eq_1728m_add_589`,
  `exists_dst_time5_base_eq_54k_add_19_of_src_base_eq_3456m_add_1453`,
  `exists_dst_time6_base_eq_54k_add_23_of_src_base_eq_6912m_add_3181`, and
  `exists_dst_time7_base_eq_54k_add_25_of_src_base_eq_13824m_add_13549`
- the first destination-eject split inside the zero-shell `time = 4` case via
  `dst_slice_eq_4_1_of_src_base_eq_3456r_add_2317`,
  `dst_slice_eq_4_2_of_src_base_eq_6912r_add_4045`,
  `dst_slice_eq_4_3_of_src_base_eq_13824r_add_7501`,
  `dst_slice_eq_4_4_of_src_base_eq_27648r_add_14413`, and the residual
  theorem `five_le_dst_eject_of_src_base_eq_55296r_add_589`
- the parity split of that zero-shell `time = 4` residual via
  `dst_slice_eq_4_6_of_src_base_eq_110592r_add_589` and
  `seven_le_dst_eject_of_src_base_eq_110592r_add_55885`
- the next exact refinement of that odd zero-shell `time = 4` residual via
  `dst_slice_eq_4_7_of_src_base_eq_221184r_add_55885` and
  `eight_le_dst_eject_of_src_base_eq_221184r_add_166477`
- the next exact refinement of the remaining zero-shell `time = 4` residual
  via `dst_slice_eq_4_8_of_src_base_eq_442368r_add_387661` and
  `nine_le_dst_eject_of_src_base_eq_442368r_add_166477`
- the next exact refinement of that remaining zero-shell `time = 4`
  residual via `dst_slice_eq_4_9_of_src_base_eq_884736r_add_608845` and
  `ten_le_dst_eject_of_src_base_eq_884736r_add_166477`
- the next exact refinement of that remaining zero-shell `time = 4`
  residual via the generic split
  `dst_slice_eq_4_10_of_src_base_eq_65536r_add_35405` and
  `eleven_le_dst_eject_of_src_base_eq_65536r_add_2637`, and its zero-shell
  wrappers
  `dst_slice_eq_4_10_of_src_base_eq_1769472r_add_166477` and
  `eleven_le_dst_eject_of_src_base_eq_1769472r_add_1051213`
- the next exact refinement of that remaining zero-shell `time = 4`
  residual via the generic split
  `dst_slice_eq_4_11_of_src_base_eq_131072r_add_68173` and
  `twelve_le_dst_eject_of_src_base_eq_131072r_add_2637`, and its zero-shell
  wrappers
  `dst_slice_eq_4_11_of_src_base_eq_3538944r_add_2820685` and
  `twelve_le_dst_eject_of_src_base_eq_3538944r_add_1051213`
- the next exact refinement of that remaining zero-shell `time = 4`
  residual via the generic split
  `dst_slice_eq_4_12_of_src_base_eq_262144r_add_133709` and
  `thirteen_le_dst_eject_of_src_base_eq_262144r_add_2637`, and its
  zero-shell wrappers
  `dst_slice_eq_4_12_of_src_base_eq_7077888r_add_4590157` and
  `thirteen_le_dst_eject_of_src_base_eq_7077888r_add_1051213`
- the next exact refinement of that remaining zero-shell `time = 4`
  residual via the generic split
  `dst_slice_eq_4_13_of_src_base_eq_524288r_add_264781` and
  `fourteen_le_dst_eject_of_src_base_eq_524288r_add_2637`, and its
  zero-shell wrappers
  `dst_slice_eq_4_13_of_src_base_eq_14155776r_add_8129101` and
  `fourteen_le_dst_eject_of_src_base_eq_14155776r_add_1051213`

The older pushed checkpoint before this boundary was:

- `054e0b3`
- `Package affine five-step return-machine self-map`

So the newer observer-gap carrier / vanishing package is green in the current
worktree and sits on the current branch beyond that older pushed checkpoint.

The generated declaration index currently on disk reports:

- `generated_at = 2026-04-13T02:05:10.397126+00:00`
- `declaration_count = 1325`

### Local Delta Beyond The Last Pushed Checkpoint

Lean source now contains a newer green observer-gap vanishing package beyond
the last pushed checkpoint:

- [UFRF/CollatzConcurrentScales.lean:9479](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L9479)
  `exists_observerGap9387_832_carrier_of_repeatCore832Transition_chain`
- [UFRF/CollatzConcurrentScales.lean:9514](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L9514)
  `exists_observerGap9387_832_thirdCarrier_of_repeatCore832Transition_chain3`
- [UFRF/CollatzConcurrentScales.lean:9558](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L9558)
  `exists_observerGap9387_832_fourthCarrier_of_repeatCore832Transition_chain4`
- [UFRF/CollatzConcurrentScales.lean:9608](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L9608)
  `exists_observerGap9387_832_fourthCarrier_with_gate_of_repeatCore832Transition_chain5`
- [UFRF/CollatzConcurrentScales.lean:11232](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L11232)
  `observerGap9387_832_eq_zero_of_repeatCore832Transition_chain5`
- [UFRF/CollatzConcurrentScales.lean:11267](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L11267)
  `observerGap9387_832_zero_block_of_repeatCore832Transition_chain5`
- [UFRF/CollatzConcurrentScales.lean:12735](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L12735)
  `observerGap9387_832_eq_zero_of_src_base_eq_864m_add_589`
- [UFRF/CollatzConcurrentScales.lean:12754](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L12754)
  `exists_src_base_eq_864m_add_589_of_observerGap9387_832_eq_zero_of_src_base_mod32_eq13`
- [UFRF/CollatzConcurrentScales.lean:12989](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L12989)
  `two_pow_dst_time_sub_four_mul_dst_base_eq_729m_add_497_of_src_base_eq_864m_add_589`
- [UFRF/CollatzConcurrentScales.lean:13043](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13043)
  `dst_time_eq_four_of_src_base_eq_1728m_add_589`
- [UFRF/CollatzConcurrentScales.lean:13068](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13068)
  `dst_base_eq_1458m_add_497_of_src_base_eq_1728m_add_589`
- [UFRF/CollatzConcurrentScales.lean:13096](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13096)
  `five_le_dst_time_of_src_base_eq_1728m_add_1453`
- [UFRF/CollatzConcurrentScales.lean:13130](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13130)
  `two_pow_dst_time_sub_five_mul_dst_base_eq_729m_add_613_of_src_base_eq_1728m_add_1453`
- [UFRF/CollatzConcurrentScales.lean:13165](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13165)
  `dst_time_eq_five_of_src_base_eq_3456m_add_1453`
- [UFRF/CollatzConcurrentScales.lean:13191](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13191)
  `dst_base_eq_1458m_add_613_of_src_base_eq_3456m_add_1453`
- [UFRF/CollatzConcurrentScales.lean:13219](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13219)
  `six_le_dst_time_of_src_base_eq_3456m_add_3181`
- [UFRF/CollatzConcurrentScales.lean:13253](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13253)
  `two_pow_dst_time_sub_six_mul_dst_base_eq_729m_add_671_of_src_base_eq_3456m_add_3181`
- [UFRF/CollatzConcurrentScales.lean:13288](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13288)
  `dst_time_eq_six_of_src_base_eq_6912m_add_3181`
- [UFRF/CollatzConcurrentScales.lean:13314](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13314)
  `dst_base_eq_1458m_add_671_of_src_base_eq_6912m_add_3181`
- [UFRF/CollatzConcurrentScales.lean:13341](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13341)
  `seven_le_dst_time_of_src_base_eq_6912m_add_6637`
- [UFRF/CollatzConcurrentScales.lean:13375](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13375)
  `two_pow_dst_time_sub_seven_mul_dst_base_eq_729m_add_700_of_src_base_eq_6912m_add_6637`
- [UFRF/CollatzConcurrentScales.lean:13410](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13410)
  `dst_time_eq_seven_of_src_base_eq_13824m_add_13549`
- [UFRF/CollatzConcurrentScales.lean:13436](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13436)
  `dst_base_eq_1458m_add_1429_of_src_base_eq_13824m_add_13549`
- [UFRF/CollatzConcurrentScales.lean:13467](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13467)
  `exists_dst_time4_base_eq_54k_add_11_of_src_base_eq_1728m_add_589`
- [UFRF/CollatzConcurrentScales.lean:13481](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13481)
  `exists_dst_time5_base_eq_54k_add_19_of_src_base_eq_3456m_add_1453`
- [UFRF/CollatzConcurrentScales.lean:13495](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13495)
  `exists_dst_time6_base_eq_54k_add_23_of_src_base_eq_6912m_add_3181`
- [UFRF/CollatzConcurrentScales.lean:13509](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L13509)
  `exists_dst_time7_base_eq_54k_add_25_of_src_base_eq_13824m_add_13549`
- [UFRF/CollatzConcurrentScales.lean:24339](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L24339)
  `dst_slice_eq_4_1_of_src_base_eq_3456r_add_2317`
- [UFRF/CollatzConcurrentScales.lean:24380](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L24380)
  `dst_slice_eq_4_2_of_src_base_eq_6912r_add_4045`
- [UFRF/CollatzConcurrentScales.lean:24421](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L24421)
  `dst_slice_eq_4_3_of_src_base_eq_13824r_add_7501`
- [UFRF/CollatzConcurrentScales.lean:24462](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L24462)
  `dst_slice_eq_4_4_of_src_base_eq_27648r_add_14413`
- [UFRF/CollatzConcurrentScales.lean:24503](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L24503)
  `five_le_dst_eject_of_src_base_eq_55296r_add_589`
- [UFRF/CollatzConcurrentScales.lean:24860](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L24860)
  `dst_slice_eq_4_6_of_src_base_eq_110592r_add_589`
- [UFRF/CollatzConcurrentScales.lean:24873](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L24873)
  `seven_le_dst_eject_of_src_base_eq_110592r_add_55885`
- [UFRF/CollatzConcurrentScales.lean:25045](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25045)
  `dst_slice_eq_4_7_of_src_base_eq_221184r_add_55885`
- [UFRF/CollatzConcurrentScales.lean:25058](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25058)
  `eight_le_dst_eject_of_src_base_eq_221184r_add_166477`
- [UFRF/CollatzConcurrentScales.lean:24965](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L24965)
  `dst_slice_eq_4_8_of_src_base_eq_16384r_add_10829`
- [UFRF/CollatzConcurrentScales.lean:25003](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25003)
  `nine_le_dst_eject_of_src_base_eq_16384r_add_2637`
- [UFRF/CollatzConcurrentScales.lean:25070](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25070)
  `dst_slice_eq_4_8_of_src_base_eq_442368r_add_387661`
- [UFRF/CollatzConcurrentScales.lean:25083](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25083)
  `nine_le_dst_eject_of_src_base_eq_442368r_add_166477`
- [UFRF/CollatzConcurrentScales.lean:25095](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25095)
  `dst_slice_eq_4_9_of_src_base_eq_32768r_add_19021`
- [UFRF/CollatzConcurrentScales.lean:25135](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25135)
  `ten_le_dst_eject_of_src_base_eq_32768r_add_2637`
- [UFRF/CollatzConcurrentScales.lean:25179](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25179)
  `dst_slice_eq_4_9_of_src_base_eq_884736r_add_608845`
- [UFRF/CollatzConcurrentScales.lean:25194](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25194)
  `ten_le_dst_eject_of_src_base_eq_884736r_add_166477`
- [UFRF/CollatzConcurrentScales.lean:25208](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25208)
  `dst_slice_eq_4_10_of_src_base_eq_65536r_add_35405`
- [UFRF/CollatzConcurrentScales.lean:25248](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25248)
  `eleven_le_dst_eject_of_src_base_eq_65536r_add_2637`
- [UFRF/CollatzConcurrentScales.lean:25292](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25292)
  `dst_slice_eq_4_10_of_src_base_eq_1769472r_add_166477`
- [UFRF/CollatzConcurrentScales.lean:25307](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25307)
  `eleven_le_dst_eject_of_src_base_eq_1769472r_add_1051213`
- [UFRF/CollatzConcurrentScales.lean:25321](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25321)
  `dst_slice_eq_4_11_of_src_base_eq_131072r_add_68173`
- [UFRF/CollatzConcurrentScales.lean:25362](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25362)
  `twelve_le_dst_eject_of_src_base_eq_131072r_add_2637`
- [UFRF/CollatzConcurrentScales.lean:25406](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25406)
  `dst_slice_eq_4_11_of_src_base_eq_3538944r_add_2820685`
- [UFRF/CollatzConcurrentScales.lean:25421](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25421)
  `twelve_le_dst_eject_of_src_base_eq_3538944r_add_1051213`
- [UFRF/CollatzConcurrentScales.lean:25435](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25435)
  `dst_slice_eq_4_12_of_src_base_eq_262144r_add_133709`
- [UFRF/CollatzConcurrentScales.lean:25476](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25476)
  `thirteen_le_dst_eject_of_src_base_eq_262144r_add_2637`
- [UFRF/CollatzConcurrentScales.lean:25520](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25520)
  `dst_slice_eq_4_12_of_src_base_eq_7077888r_add_4590157`
- [UFRF/CollatzConcurrentScales.lean:25535](/tmp/repo-collatz-memory-loop/UFRF/CollatzConcurrentScales.lean#L25535)
  `thirteen_le_dst_eject_of_src_base_eq_7077888r_add_1051213`

Interpret them as:

- on a two-step repeat-core chain, the shared observer gap already factors as
  one common integer carrier `u`
- source gap = `16 * u`
- destination gap = `27 * u`
- on a three-step repeat-core chain, overlapping consecutive carrier facts
  forces a deeper carrier `v`
- `σ.src` gap = `256 * v`
- `σ.dst` gap = `432 * v`
- `ρ.dst` gap = `729 * v`
- one more overlap lifts that same package to a fourth carrier `w` with exact
  orbit `4096*w -> 6912*w -> 11664*w -> 19683*w`, and five-step persistence
  forces the continuation gate `16 ∣ w`
- five-step persistence already collapses the observer gap to zero on the
  middle source state, and therefore on the short block
  `σ.src, σ.dst, ρ.dst, ups.dst`
- on the higher-time `(time,eject) = (3,1)` branch with `base ≡ 13 (mod 32)`,
  observer gap zero is no longer just a bounded possibility: it is exactly the
  affine shell `base = 864*m + 589`
- on that zero shell, the higher-time transport law specializes to
  `2^(dst.time - 4) * dst.base = 729*m + 497`
- the first green destination-shell ladder now splits that family into exact
  `time = 4, 5, 6, 7` slices with destination bases
  `1458*m + 497`, `1458*m + 613`, `1458*m + 671`, and `1458*m + 1429`
- those destination bases land on the already-familiar higher-time shell
  residues `11, 19, 23, 25 mod 54`, so this branch is rejoining the older
  shell tree rather than creating a disconnected observer-only arithmetic
- the current source now packages that re-entry at theorem level: each exact
  zero-shell case is reindexed directly into the established
  `54*k + 11/19/23/25` destination-shell families with explicit affine
  parameter maps
  `k = 27*m + 9`, `27*m + 11`, `27*m + 12`, and `27*m + 26`
- the zero-shell `time = 4` case is no longer a single undifferentiated
  branch: it now splits into exact destination slices `(4,1)`, `(4,2)`,
  `(4,3)`, `(4,4)` on the source families
  `3456*r + 2317`, `6912*r + 4045`, `13824*r + 7501`, and
  `27648*r + 14413`, with the residual family `55296*r + 589` forcing
  destination eject at least `5`
- that residual is now split one layer further by parity:
  `110592*r + 589` lands exactly on destination slice `(4,6)`, while
  `110592*r + 55885` stays at `time = 4` with destination eject at least `7`
- the odd `eject ≥ 7` branch now splits one layer further:
  `221184*r + 55885` lands exactly on destination slice `(4,7)`, while
  `221184*r + 166477` remains on the time-4 residual with destination eject
  at least `8`
- that remaining `eject ≥ 8` branch now splits one layer further as well:
  `442368*r + 387661` lands exactly on destination slice `(4,8)`, while
  `442368*r + 166477` remains on the time-4 residual with destination eject
  at least `9`
- that remaining `eject ≥ 9` branch now splits one layer further as well:
  `884736*r + 608845` lands exactly on destination slice `(4,9)`, while
  `884736*r + 166477` remains on the time-4 residual with destination eject
  at least `10`
- that remaining `eject ≥ 10` branch now splits one layer further as well:
  `65536*r + 35405` lands exactly on destination slice `(4,10)`, while
  `65536*r + 2637` remains on the time-4 residual with destination eject at
  least `11`; on the zero-shell side these appear as
  `1769472*r + 166477` and `1769472*r + 1051213`
- that remaining `eject ≥ 11` branch now splits one layer further as well:
  `131072*r + 68173` lands exactly on destination slice `(4,11)`, while
  `131072*r + 2637` remains on the time-4 residual with destination eject at
  least `12`; on the zero-shell side these appear as
  `3538944*r + 2820685` and `3538944*r + 1051213`
- that remaining `eject ≥ 12` branch now splits one layer further as well:
  `262144*r + 133709` lands exactly on destination slice `(4,12)`, while
  `262144*r + 2637` remains on the time-4 residual with destination eject at
  least `13`; on the zero-shell side these appear as
  `7077888*r + 4590157` and `7077888*r + 1051213`
- the abandoned shortcut “`base = 6912*m + 6637` gives uniform `time = 9`”
  is not part of the verified story; the green theorem there is only the
  residual `dst.time ≥ 7` transport law, whose odd sub-shell
  `base = 13824*m + 13549` is exactly the `time = 7` case

These theorems are now green in the current worktree and synced across
frontier/index/Rover, with no newer unverified source delta beyond them at
the moment.

### Current Newer Source Delta Beyond That Green Boundary

Lean source currently matches the recorded green hash for this boundary.

- there is no newer unverified theorem cluster beyond the recorded green
  boundary at this moment
- the next live target is the zero-shell `time = 4` residual family
  `base = 14155776*r + 1051213`, aiming to refine the current
  eject-`≥ 14` tail into an exact eject-14 case and a thinner
  residual eject-`≥ 15` tail

### Active Verification State

The targeted verification run for the current observer-gap vanishing package
completed successfully:

- session id: `86196`
- command: `lake build UFRF.CollatzConcurrentScales`
- result: success with the familiar pre-existing warnings only
- exact green-source hash is recorded in
  [COLLATZ_TARGETED_BUILD_STATUS.json](/tmp/repo-collatz-memory-loop/docs/proofs/COLLATZ_TARGETED_BUILD_STATUS.json)

### Recovered Failed Probe

The first attempted deeper observer-gap shell lift used the same theorem name:

- `exists_observerGap9387_832_thirdCarrier_of_repeatCore832Transition_chain3`

That earlier draft failed a targeted build and was intentionally removed from
source before this handoff layer was prepared. The theorem has now been
rederived fresh and verified green using a new proof that overlaps consecutive
carrier facts; do not conflate the current proof with the discarded script.

### Artifact Sync State

As of this snapshot:

- the recorded green source hash in
  [COLLATZ_TARGETED_BUILD_STATUS.json](/tmp/repo-collatz-memory-loop/docs/proofs/COLLATZ_TARGETED_BUILD_STATUS.json)
  now matches the current source boundary, including the exact `(4,13)` /
  residual `≥ 14` quartet
- the frontier note and this handoff file now describe the observer-gap
  carrier / vanishing package through theorem-level reindexing of the
  zero-shell time-4/5/6/7 cases into the established `54*k` shell families,
  and through the first destination-eject split of the zero-shell `time = 4`
  case, through the parity split of its residual eject-`≥ 5` family, and now
  through the exact eject-7 / residual eject-`≥ 8` refinement of its odd
  tail, through the exact eject-8 / residual eject-`≥ 9` refinement of
  the remaining tail, through the exact eject-9 / residual eject-`≥ 10`
  refinement of the remaining tail, through the exact eject-10 /
  residual eject-`≥ 11` refinement of the remaining tail, through the exact
  eject-11 / residual eject-`≥ 12` refinement of the remaining tail, and
  through the exact eject-12 / residual eject-`≥ 13` refinement of the
  remaining tail, and through the exact eject-13 / residual eject-`≥ 14`
  refinement of the remaining tail
- the symbol index has been regenerated after the latest green targeted build
  and now reports `1325` declarations, matching the current green source
- Rover is now synced through the exact eject-13 / residual eject-`≥ 14`
  refinement of the zero-shell `time = 4` odd residual via
  `20260413T021847Z-green-boundary-update-the-zero-shell-time-4-odd-residual-reaches-eject-13.md`

That means the repo is back in a compact-safe state at this boundary:

- the local green boundary is known and freshly rebuilt
- source, status JSON, frontier, handoff, symbol index, and Rover agree on
  the same boundary
- the next proof step can start from
  `base = 14155776*r + 1051213` without carrying an unverified theorem delta

## Immediate Next Step

1. treat the exact `(4,13)` / residual `≥ 14` quartet as part of the
   recorded green boundary
2. keep using the bridge theorems and inherited time-4 eject tree as the
   default interface for exact zero-shell cases instead of reopening the
   arithmetic each time
3. continue from the residual family
   `base = 14155776*r + 1051213`, aiming for an exact eject-14 case and a
   thinner eject-`≥ 15` tail before opening a different shell branch
4. only continue the zero-shell dyadic split after those existing slice
   interfaces are fully exploited, so the observer package stays attached to
   intrinsic source-state transport rather than drifting into standalone
   observer arithmetic

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

- older pushed checkpoint before this boundary is `054e0b3`
- current local green worktree now includes the observer-gap carrier hierarchy
  through
  `exists_observerGap9387_832_fourthCarrier_with_gate_of_repeatCore832Transition_chain5`,
  the chain-5 zero package
  `observerGap9387_832_eq_zero_of_repeatCore832Transition_chain5` and
  `observerGap9387_832_zero_block_of_repeatCore832Transition_chain5`, and the
  higher-time affine zero-shell equivalence
  `observerGap9387_832_eq_zero_of_src_base_eq_864m_add_589` /
  `exists_src_base_eq_864m_add_589_of_observerGap9387_832_eq_zero_of_src_base_mod32_eq13`,
  its transport family
  `two_pow_dst_time_sub_four_mul_dst_base_eq_729m_add_497_of_src_base_eq_864m_add_589`,
  and the first exact destination-shell ladder through
  `dst_time_eq_seven_of_src_base_eq_13824m_add_13549` /
  `dst_base_eq_1458m_add_1429_of_src_base_eq_13824m_add_13549`, together
  with the theorem-level reindexing bridge
  `exists_dst_time4_base_eq_54k_add_11_of_src_base_eq_1728m_add_589` through
  `exists_dst_time7_base_eq_54k_add_25_of_src_base_eq_13824m_add_13549`, and
  the zero-shell `time = 4` eject split through
  `dst_slice_eq_4_13_of_src_base_eq_14155776r_add_8129101` with residual
  `fourteen_le_dst_eject_of_src_base_eq_14155776r_add_1051213`
- targeted build session `86196` completed green in the actual repo for that
  boundary
- current source currently matches the recorded green hash, so there is no
  newer unverified source delta yet

Immediate objective from this boundary:

- consume the new zero-shell `time = 4` residual
  `base = 14155776*r + 1051213` using the existing time-4 residual tree
  before opening another shell branch, aiming to refine the current
  eject-`≥ 14` tail to an exact eject-14 case and a thinner
  eject-`≥ 15` residual
