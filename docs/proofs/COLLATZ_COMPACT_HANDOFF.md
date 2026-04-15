# Collatz Compact Handoff

This file is the compact-safe handoff layer for fresh threads on
`/private/tmp/repo-collatz-memory-loop`.

Refresh it before:

- starting a new thread
- compacting or resuming after compaction
- describing status after source moved ahead of the last green build boundary
- handing work from proof changes back into docs, Rover, or the symbol index

## Mandatory Resume Order

1. Read [AGENTS.md](/private/tmp/repo-collatz-memory-loop/AGENTS.md).
2. Read this file.
3. Read
   [COLLATZ_CONCURRENT_FRONTIER.md](/private/tmp/repo-collatz-memory-loop/docs/proofs/COLLATZ_CONCURRENT_FRONTIER.md).
4. Use the
   [$ufrf-memory-loop](/Users/dcharb/.codex/skills/ufrf-memory-loop/SKILL.md)
   workflow before substantial proof work.
5. First verify repo identity with a repo-anchored check, even if the desktop
   thread reopened outside the repo:
   `python3 /private/tmp/repo-collatz-memory-loop/scripts/collatz_compact_status.py`.
   Resolve any warnings before flattening status into a single summary.
6. When refreshing the declaration index, serialize the step:
   run `python3 scripts/generate_decl_index.py ...`, wait for it to finish,
   then read `generated_at`, `declaration_count`, or compact status.
   Do not read the index in parallel with regenerating it.

## Build-Finish Handshake

For this proof thread, Lean builds use a human-in-the-loop completion signal:

- Codex may start targeted Lean or `lake build` runs when useful.
- The user monitors the live build and sends the completion message.
- Treat that user message as the authoritative signal that the build is done.
- Do not inspect a running build session as if it were final before that user
  signal arrives.
- After the user sends the completion signal, inspect that exact session,
  record the result, and then continue.

## Why Compactions Drift

The recurring failure mode is not usually theorem loss. It is boundary loss:

- the latest chat summary merges verified green work with newer unverified
  source edits
- the active terminal is sitting outside the repo, so a reported build result
  may not correspond to `/tmp/repo-collatz-memory-loop`
- the first post-compaction shell checks trust the terminal cwd instead of a
  repo-anchored status command, so the thread briefly reasons about the wrong
  checkout before recovering
- Lean source is ahead of the built `olean`, but conversation memory talks as
  though the new theorem is already green
- a build session gets polled or summarized before the user's completion
  signal, so the thread starts treating an in-flight run as if it were final
- a failed build can wipe the direct `olean` artifact even when the source is
  later reverted back to the last known green content
- the symbol index and Rover are synced to one boundary while the source file
  has already moved to another
- the index generator is started in parallel with a metadata read, so the
  reader sees the previous `generated_at` / `declaration_count` and the
  checkpoint falsely looks out of sync even though the new index is still
  being written

Trust order when artifacts disagree:

1. Lean source plus the latest confirmed green build boundary
2. this handoff file and the frontier note if they explicitly preserve that
   separation
3. Rover curated memory and the generated declaration index
4. compacted chat summaries

## Serialized Artifact Rule

For this repo, declaration-index refresh is a write step and compact status is
a read step. They must not be collapsed into one parallel probe.

Safe order:

1. finish the Lean build
2. regenerate the declaration index
3. read the refreshed index metadata
4. update handoff/frontier/status docs
5. run `python3 scripts/collatz_compact_status.py`

Unsafe order:

- starting `generate_decl_index.py` in the same parallel batch as a command
  that reads `COLLATZ_CONCURRENT_SYMBOL_INDEX.json`
- starting `generate_decl_index.py` in parallel with
  `python3 scripts/collatz_compact_status.py`

If a mismatch appears immediately after a regenerate step, first check whether
the read happened before the generator finished. In this repo that has been the
recurring cause; it is not evidence that `generate_decl_index.py` wrote bad
metadata.

## Current Snapshot

This snapshot is intentionally split into the live-source green boundary and
the farther generated telemetry frontier beyond it.

### Repo Identity

- repo: `/private/tmp/repo-collatz-memory-loop`
- branch: `codex/collatz-memory-loop`
- older pushed checkpoint before this boundary: `13cc195`
- older pushed message: `Checkpoint eject-32 source and eject-80 telemetry frontier`

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
- the next exact refinement of that remaining zero-shell `time = 4`
  residual via the generic split
  `dst_slice_eq_4_14_of_src_base_eq_1048576r_add_2637` and
  `fifteen_le_dst_eject_of_src_base_eq_1048576r_add_526925`, and its
  zero-shell wrappers
  `dst_slice_eq_4_14_of_src_base_eq_28311552r_add_1051213` and
  `fifteen_le_dst_eject_of_src_base_eq_28311552r_add_15206989`
- the next six exact refinements of that remaining zero-shell `time = 4`
  residual now continue generically through
  `dst_slice_eq_4_15_of_src_base_eq_2097152r_add_526925` /
  `sixteen_le_dst_eject_of_src_base_eq_2097152r_add_1575501`,
  `dst_slice_eq_4_16_of_src_base_eq_4194304r_add_1575501` /
  `seventeen_le_dst_eject_of_src_base_eq_4194304r_add_3672653`,
  `dst_slice_eq_4_17_of_src_base_eq_8388608r_add_3672653` /
  `eighteen_le_dst_eject_of_src_base_eq_8388608r_add_7866957`,
  `dst_slice_eq_4_18_of_src_base_eq_16777216r_add_7866957` /
  `nineteen_le_dst_eject_of_src_base_eq_16777216r_add_16255565`,
  `dst_slice_eq_4_19_of_src_base_eq_33554432r_add_16255565` /
  `twenty_le_dst_eject_of_src_base_eq_33554432r_add_33032781`, and
  `dst_slice_eq_4_20_of_src_base_eq_67108864r_add_33032781` /
  `twenty_one_le_dst_eject_of_src_base_eq_67108864r_add_66587213`
- on the zero-shell side those same refinements now continue through
  `dst_slice_eq_4_15_of_src_base_eq_56623104r_add_15206989` /
  `sixteen_le_dst_eject_of_src_base_eq_56623104r_add_43518541`,
  `dst_slice_eq_4_16_of_src_base_eq_113246208r_add_43518541` /
  `seventeen_le_dst_eject_of_src_base_eq_113246208r_add_100141645`,
  `dst_slice_eq_4_17_of_src_base_eq_226492416r_add_213387853` /
  `eighteen_le_dst_eject_of_src_base_eq_226492416r_add_100141645`,
  `dst_slice_eq_4_18_of_src_base_eq_452984832r_add_326634061` /
  `nineteen_le_dst_eject_of_src_base_eq_452984832r_add_100141645`,
  `dst_slice_eq_4_19_of_src_base_eq_905969664r_add_553126477` /
  `twenty_le_dst_eject_of_src_base_eq_905969664r_add_100141645`, and
  `dst_slice_eq_4_20_of_src_base_eq_1811939328r_add_100141645` /
  `twenty_one_le_dst_eject_of_src_base_eq_1811939328r_add_1006111309`
- the first exact refinement after the repaired eject-21 branch flip now
  continues generically through
  `dst_slice_eq_4_21_of_src_base_eq_134217728r_add_133696077` /
  `twenty_two_le_dst_eject_of_src_base_eq_134217728r_add_66587213`
- on the zero-shell side that same repaired split now appears as
  `dst_slice_eq_4_21_of_src_base_eq_3623878656r_add_2818050637` /
  `twenty_two_le_dst_eject_of_src_base_eq_3623878656r_add_1006111309`
- the next eleven exact refinements of that same residual-seeded time-4 tail
  now continue live through exact eject-22 / residual eject-`≥ 23`, exact
  eject-23 / residual eject-`≥ 24`, exact eject-24 / residual eject-`≥ 25`,
  exact eject-25 / residual eject-`≥ 26`, exact eject-26 /
  residual eject-`≥ 27`, exact eject-27 / residual eject-`≥ 28`, exact
  eject-28 / residual eject-`≥ 29`, exact eject-29 / residual eject-`≥ 30`,
  exact eject-30 / residual eject-`≥ 31`, exact eject-31 /
  residual eject-`≥ 32`, and exact eject-32 / residual eject-`≥ 33`
- at the generic frontier this now ends on
  `dst_slice_eq_4_32_of_src_base_eq_274877906944r_add_160188336717` /
  `thirty_three_le_dst_eject_of_src_base_eq_274877906944r_add_22749383245`
- on the zero-shell side it ends on
  `dst_slice_eq_4_32_of_src_base_eq_7421703487488r_add_3733601126989` /
  `thirty_three_le_dst_eject_of_src_base_eq_7421703487488r_add_22749383245`

The older pushed checkpoint before this boundary was:

- `13cc195`
- `Checkpoint eject-32 source and eject-80 telemetry frontier`

So the newer observer-gap carrier / vanishing package is green in the current
worktree and sits on the current branch beyond that older pushed checkpoint.

The generated declaration index currently on disk reports:

- `generated_at = 2026-04-14T19:42:02.492536+00:00`
- `declaration_count = 1627`

### Scaled Telemetry Beyond The Live Boundary

The residual-seeded wave pipeline has now also run cleanly beyond the live
Lean source boundary:

- pipeline root:
  `/private/tmp/collatz-eject-wave-pipeline-post32-20260413T045249Z`
- waves `eject-33..42`, `43..52`, `53..62`, `63..72`, and `73..80` all
  returned code `0`
- the final wave finished at `2026-04-13T05:35:19Z`
- every per-target `result.json` in `eject-73..80` reports
  `success = true`, `build_exit_code = 0`, and `index_exit_code = 0`
- this is durable batch evidence that the corrected residual-law harness
  scales cleanly through eject-80
- important separation: the live repo source is still targeted-build verified
  only through exact eject-32 / residual eject-`≥ 33`; eject-33 through
  eject-80 is telemetry support beyond that live source boundary

### Latest Recorded Green Refactor State

The theorem frontier above now includes the earlier eject-32 zero-shell work
and the much deeper higher-time return ladder that was just rebuilt green in
the live repo.

- the shared helper layer
  `dst_slice_eq_4_exact_of_src_base_eq_64m_add_13_of_factorization`,
  `dst_time_eq_four_and_dst_eject_ge_of_src_base_eq_64m_add_13_of_factorization`,
  `dst_slice_eq_4_exact_of_src_base_eq_64m_add_13_of_dst_factorization`, and
  `dst_time_eq_four_and_dst_eject_ge_of_src_base_eq_64m_add_13_of_dst_factorization`
  is now green through the entire live `time = 4` eject ladder, ending on
  exact eject-32 / residual eject-`≥ 33`
- that completed `time = 4` refactor boundary was confirmed by targeted build
  session `65450`
- the shared helper layer
  `dst_slice_eq_5_exact_of_src_base_eq_128m_add_45_of_factorization`,
  `dst_time_eq_five_and_dst_eject_ge_of_src_base_eq_128m_add_45_of_factorization`,
  `dst_slice_eq_5_exact_of_src_base_eq_128m_add_45_of_dst_factorization`, and
  `dst_time_eq_five_and_dst_eject_ge_of_src_base_eq_128m_add_45_of_dst_factorization`
  is now green through the initial live `time = 5` eject ladder, ending on
  exact eject-7 / residual eject-`≥ 8`
- that initial `time = 5` refactor boundary was confirmed by targeted build
  session `40265`
- the shared helper layer
  `dst_slice_eq_6_exact_of_src_base_eq_256m_add_109_of_factorization`,
  `dst_time_eq_six_and_dst_eject_ge_of_src_base_eq_256m_add_109_of_factorization`,
  `dst_slice_eq_6_exact_of_src_base_eq_256m_add_109_of_dst_factorization`, and
  `dst_time_eq_six_and_dst_eject_ge_of_src_base_eq_256m_add_109_of_dst_factorization`
  is now green through the initial live `time = 6` eject ladder, ending on
  exact eject-5 / residual eject-`≥ 6`
- that initial `time = 6` refactor boundary was confirmed by targeted build
  session `68178`
- the shared helper layer
  `dst_slice_eq_7_exact_of_src_base_eq_512m_add_237_of_factorization`,
  `dst_time_eq_seven_and_dst_eject_ge_of_src_base_eq_512m_add_237_of_factorization`,
  `dst_slice_eq_7_exact_of_src_base_eq_512m_add_237_of_dst_factorization`, and
  `dst_time_eq_seven_and_dst_eject_ge_of_src_base_eq_512m_add_237_of_dst_factorization`
  is now green through the initial live `time = 7` eject ladder, ending on
  exact eject-6 / residual eject-`≥ 7`
- that initial `time = 7` refactor boundary was confirmed by targeted build
  session `22759`
- the shared higher-time helper layer
  `dst_time_eq_eight_add_and_dst_base_eq_of_src_base_eq_512m_add_493_of_factorization`
  and
  `dst_time_ge_eight_add_and_scaled_base_eq_of_src_base_eq_512m_add_493_of_factorization`
  is now green through the initial live higher-time seam on
  `base = 512*m + 493`, ending on exact `time = 8`, exact `time = 9`, and
  residual `time ≥ 10`
- that initial `time ≥ 8` refactor boundary was confirmed by targeted build
  session `15275`
- the shared higher-time helper layer
  `dst_time_eq_ten_add_and_dst_base_eq_of_src_base_eq_2048m_add_1517_of_factorization`
  and
  `dst_time_ge_ten_add_and_scaled_base_eq_of_src_base_eq_2048m_add_1517_of_factorization`
  is now green through the next live higher-time seam on
  `base = 2048*m + 1517`, ending on exact `time = 10`, exact `time = 11`,
  exact `time = 12`, and residual `time ≥ 13`
- that initial `time ≥ 10` refactor boundary was confirmed by targeted build
  session `19932`
- the shared higher-time helper layer
  `dst_time_eq_thirteen_add_and_dst_base_eq_of_src_base_eq_16384m_add_9709_of_factorization`
  and
  `dst_time_ge_thirteen_add_and_scaled_base_eq_of_src_base_eq_16384m_add_9709_of_factorization`
  is now green through the next live higher-time seam on
  `base = 16384*m + 9709`, ending on exact `time = 13`, exact `time = 14`,
  exact `time = 15`, exact `time = 16`, exact `time = 17`, and residual
  `time ≥ 18`
- that initial `time ≥ 13` refactor boundary was confirmed by targeted build
  session `1280`
- the same higher-time ladder now continues green through exact `time = 135`
  with residual `time ≥ 136`, including the returned-shell transport wrappers
  that route the live residual back into the older `time ≥ 28/31/36/44`
  shells and the `VerifiedHigherTimeReturnClock` machine packaging already in
  source
- that deeper higher-time continuation was confirmed by targeted build session
  `46483`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_thirty_six_add_and_dst_base_eq_of_src_base_eq_174224571863520493293247799005065324265472m_add_129055238417422587624627999263011351307757_of_factorization`
  and
  `dst_time_ge_one_hundred_thirty_six_add_and_scaled_base_eq_of_src_base_eq_174224571863520493293247799005065324265472m_add_129055238417422587624627999263011351307757_of_factorization`
  is now green through the next live higher-time seam on
  `base = 174224571863520493293247799005065324265472*m + 129055238417422587624627999263011351307757`,
  ending on exact `time = 136`, exact `time = 137`, exact `time = 138`, and
  residual `time ≥ 139`
- that `time ≥ 136` helper-refactor seam was confirmed by targeted build
  session `44643`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_thirty_nine_add_and_dst_base_eq_of_src_base_eq_1393796574908163946345982392040522594123776m_add_825953525871504560797619195283272648369645_of_factorization`
  and
  `dst_time_ge_one_hundred_thirty_nine_add_and_scaled_base_eq_of_src_base_eq_1393796574908163946345982392040522594123776m_add_825953525871504560797619195283272648369645_of_factorization`
  is now green through the next live higher-time seam on
  `base = 1393796574908163946345982392040522594123776*m + 825953525871504560797619195283272648369645`,
  ending on exact `time = 139`, exact `time = 140`, exact `time = 141`,
  exact `time = 142`, exact `time = 143`, and residual `time ≥ 144`
- that `time ≥ 139` helper-refactor seam was confirmed by targeted build
  session `6009`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_forty_four_add_and_dst_base_eq_of_src_base_eq_44601490397061246283071436545296723011960832m_add_23126698724402127702333337467931634154350061_of_factorization`
  and
  `dst_time_ge_one_hundred_forty_four_add_and_scaled_base_eq_of_src_base_eq_44601490397061246283071436545296723011960832m_add_23126698724402127702333337467931634154350061_of_factorization`
  is now green through the next live higher-time seam on
  `base = 44601490397061246283071436545296723011960832*m + 23126698724402127702333337467931634154350061`,
  ending on exact `time = 144`, exact `time = 145`, exact `time = 146`,
  exact `time = 147`, and residual `time ≥ 148`
- that `time ≥ 144` helper-refactor seam was confirmed by targeted build
  session `64428`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_forty_eight_add_and_dst_base_eq_of_src_base_eq_713623846352979940529142984724747568191373312m_add_290735641106769605400761956739711972226115053_of_factorization`
  and
  `dst_time_ge_one_hundred_forty_eight_add_and_scaled_base_eq_of_src_base_eq_713623846352979940529142984724747568191373312m_add_290735641106769605400761956739711972226115053_of_factorization`
  is now green through the next live higher-time seam on
  `base = 713623846352979940529142984724747568191373312*m + 290735641106769605400761956739711972226115053`,
  ending on exact `time = 148`, exact `time = 149`, exact `time = 150`,
  exact `time = 151`, and residual `time ≥ 152`
- that `time ≥ 148` helper-refactor seam was confirmed by targeted build
  session `11441`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_fifty_two_add_and_dst_base_eq_of_src_base_eq_11417981541647679048466287755595961091061972992m_add_10995093336401468713337906727610925495096714733_of_factorization`
  and
  `dst_time_ge_one_hundred_fifty_two_add_and_scaled_base_eq_of_src_base_eq_11417981541647679048466287755595961091061972992m_add_10995093336401468713337906727610925495096714733_of_factorization`
  is now green through the next live higher-time seam on
  `base = 11417981541647679048466287755595961091061972992*m + 10995093336401468713337906727610925495096714733`,
  ending on exact `time = 152`, exact `time = 153`, and residual `time ≥ 154`
- that `time ≥ 152` helper-refactor seam was confirmed by targeted build
  session `27586`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_fifty_four_add_and_dst_base_eq_of_src_base_eq_45671926166590716193865151022383844364247891968m_add_33831056419696826810270482238802847677220660717_of_factorization`
  and
  `dst_time_ge_one_hundred_fifty_four_add_and_scaled_base_eq_of_src_base_eq_45671926166590716193865151022383844364247891968m_add_33831056419696826810270482238802847677220660717_of_factorization`
  is now green through the next live higher-time seam on
  `base = 45671926166590716193865151022383844364247891968*m + 33831056419696826810270482238802847677220660717`,
  ending on exact `time = 154`, exact `time = 155`, exact `time = 156`, and
  residual `time ≥ 157`
- that `time ≥ 154` helper-refactor seam was confirmed by targeted build
  session `19103`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_fifty_seven_add_and_dst_base_eq_of_src_base_eq_365375409332725729550921208179070754913983135744m_add_216518761086059691585731086328338225134212228589_of_factorization`
  and
  `dst_time_ge_one_hundred_fifty_seven_add_and_scaled_base_eq_of_src_base_eq_365375409332725729550921208179070754913983135744m_add_216518761086059691585731086328338225134212228589_of_factorization`
  is now green through the next live higher-time seam on
  `base = 365375409332725729550921208179070754913983135744*m + 216518761086059691585731086328338225134212228589`,
  ending on exact `time = 157`, exact `time = 158`, exact `time = 159`,
  exact `time = 160`, exact `time = 161`, and residual `time ≥ 162`
- that `time ≥ 157` helper-refactor seam was confirmed by targeted build
  session `15712`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_sixty_two_add_and_dst_base_eq_of_src_base_eq_11692013098647223345629478661730264157247460343808m_add_6062525310409671364400470417193470303757942400493_of_factorization`
  and
  `dst_time_ge_one_hundred_sixty_two_add_and_scaled_base_eq_of_src_base_eq_11692013098647223345629478661730264157247460343808m_add_6062525310409671364400470417193470303757942400493_of_factorization`
  is now green through the next live higher-time seam on
  `base = 11692013098647223345629478661730264157247460343808*m + 6062525310409671364400470417193470303757942400493`,
  ending on exact `time = 162`, exact `time = 163`, exact `time = 164`,
  exact `time = 165`, and residual `time ≥ 166`
- that `time ≥ 162` helper-refactor seam was confirmed by targeted build
  session `51385`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_sixty_six_add_and_dst_base_eq_of_src_base_eq_187072209578355573530071658587684226515959365500928m_add_76214603902293011438177342387575055247242704463341_of_factorization`
  and
  `dst_time_ge_one_hundred_sixty_six_add_and_scaled_base_eq_of_src_base_eq_187072209578355573530071658587684226515959365500928m_add_76214603902293011438177342387575055247242704463341_of_factorization`
  is now green through the next live higher-time seam on
  `base = 187072209578355573530071658587684226515959365500928*m + 76214603902293011438177342387575055247242704463341`,
  ending on exact `time = 166`, exact `time = 167`, exact `time = 168`,
  exact `time = 169`, and residual `time ≥ 170`
- that `time ≥ 166` helper-refactor seam was confirmed by targeted build
  session `34519`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_seventy_add_and_dst_base_eq_of_src_base_eq_2993155353253689176481146537402947624255349848014848m_add_2882297747577626614389252221202838452986633186977261_of_factorization`
  and
  `dst_time_ge_one_hundred_seventy_add_and_scaled_base_eq_of_src_base_eq_2993155353253689176481146537402947624255349848014848m_add_2882297747577626614389252221202838452986633186977261_of_factorization`
  is now green through the next live higher-time seam on
  `base = 2993155353253689176481146537402947624255349848014848*m + 2882297747577626614389252221202838452986633186977261`
  ending on exact `time = 170`, exact `time = 171`, and residual `time ≥ 172`
- that seam rewires the live branch through the exact shells
  `dst_time_eq_one_hundred_seventy_of_src_base_eq_5986310706507378352962293074805895248510699696029696m_add_5875453100831315790870398758605786077241983034992109` /
  `dst_base_eq_54m_add_53_of_src_base_eq_5986310706507378352962293074805895248510699696029696m_add_5875453100831315790870398758605786077241983034992109`,
  `dst_time_eq_one_hundred_seventy_one_of_src_base_eq_11972621413014756705924586149611790497021399392059392m_add_2882297747577626614389252221202838452986633186977261` /
  `dst_base_eq_54m_add_13_of_src_base_eq_11972621413014756705924586149611790497021399392059392m_add_2882297747577626614389252221202838452986633186977261`,
  and the residual `one_hundred_seventy_two_le_dst_time_of_src_base_eq_11972621413014756705924586149611790497021399392059392m_add_8868608454085004967351545296008733701497332883006957` /
  `two_pow_dst_time_sub_one_hundred_seventy_two_mul_dst_base_eq_27m_add_20_of_src_base_eq_11972621413014756705924586149611790497021399392059392m_add_8868608454085004967351545296008733701497332883006957`
- that `time ≥ 170` helper-refactor seam was confirmed by targeted build
  session `70979`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_seventy_two_add_and_dst_base_eq_of_src_base_eq_11972621413014756705924586149611790497021399392059392m_add_8868608454085004967351545296008733701497332883006957_of_factorization`
  and
  `dst_time_ge_one_hundred_seventy_two_add_and_scaled_base_eq_of_src_base_eq_11972621413014756705924586149611790497021399392059392m_add_8868608454085004967351545296008733701497332883006957_of_factorization`
  is now green through the next live higher-time seam on
  `base = 11972621413014756705924586149611790497021399392059392*m + 8868608454085004967351545296008733701497332883006957`
  ending on exact `time = 172`, exact `time = 173`, exact `time = 174`, and
  residual `time ≥ 175`
- that seam rewires the live branch through the exact shells
  `dst_time_eq_one_hundred_seventy_two_of_src_base_eq_23945242826029513411849172299223580994042798784118784m_add_20841229867099761673276131445620524198518732275066349` /
  `dst_base_eq_54m_add_47_of_src_base_eq_23945242826029513411849172299223580994042798784118784m_add_20841229867099761673276131445620524198518732275066349`,
  `dst_time_eq_one_hundred_seventy_three_of_src_base_eq_47890485652059026823698344598447161988085597568237568m_add_32813851280114518379200717595232314695540131667125741` /
  `dst_base_eq_54m_add_37_of_src_base_eq_47890485652059026823698344598447161988085597568237568m_add_32813851280114518379200717595232314695540131667125741`,
  `dst_time_eq_one_hundred_seventy_four_of_src_base_eq_95780971304118053647396689196894323976171195136475136m_add_8868608454085004967351545296008733701497332883006957` /
  `dst_base_eq_54m_add_5_of_src_base_eq_95780971304118053647396689196894323976171195136475136m_add_8868608454085004967351545296008733701497332883006957`,
  and the residual `one_hundred_seventy_five_le_dst_time_of_src_base_eq_95780971304118053647396689196894323976171195136475136m_add_56759094106144031791049889894455895689582930451244525` /
  `two_pow_dst_time_sub_one_hundred_seventy_five_mul_dst_base_eq_27m_add_16_of_src_base_eq_95780971304118053647396689196894323976171195136475136m_add_56759094106144031791049889894455895689582930451244525`
- that `time ≥ 172` helper-refactor seam was confirmed by targeted build
  session `1430`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_seventy_five_add_and_dst_base_eq_of_src_base_eq_95780971304118053647396689196894323976171195136475136m_add_56759094106144031791049889894455895689582930451244525_of_factorization`
  and
  `dst_time_ge_one_hundred_seventy_five_add_and_scaled_base_eq_of_src_base_eq_95780971304118053647396689196894323976171195136475136m_add_56759094106144031791049889894455895689582930451244525_of_factorization`
  is now green through the next live higher-time seam on
  `base = 95780971304118053647396689196894323976171195136475136*m + 56759094106144031791049889894455895689582930451244525`
  ending on exact `time = 175`, exact `time = 176`, exact `time = 177`,
  exact `time = 178`, exact `time = 179`, and residual `time ≥ 180`
- that seam rewires the live branch through the exact shells
  `dst_time_eq_one_hundred_seventy_five_of_src_base_eq_191561942608236107294793378393788647952342390272950272m_add_152540065410262085438446579091350219665754125587719661` /
  `dst_base_eq_54m_add_43_of_src_base_eq_191561942608236107294793378393788647952342390272950272m_add_152540065410262085438446579091350219665754125587719661`,
  `dst_time_eq_one_hundred_seventy_six_of_src_base_eq_383123885216472214589586756787577295904684780545900544m_add_248321036714380139085843268288244543641925320724194797` /
  `dst_base_eq_54m_add_35_of_src_base_eq_383123885216472214589586756787577295904684780545900544m_add_248321036714380139085843268288244543641925320724194797`,
  `dst_time_eq_one_hundred_seventy_seven_of_src_base_eq_766247770432944429179173513575154591809369561091801088m_add_439882979322616246380636646682033191594267710997145069` /
  `dst_base_eq_54m_add_31_of_src_base_eq_766247770432944429179173513575154591809369561091801088m_add_439882979322616246380636646682033191594267710997145069`,
  `dst_time_eq_one_hundred_seventy_eight_of_src_base_eq_1532495540865888858358347027150309183618739122183602176m_add_823006864539088460970223403469610487498952491543045613` /
  `dst_base_eq_54m_add_29_of_src_base_eq_1532495540865888858358347027150309183618739122183602176m_add_823006864539088460970223403469610487498952491543045613`,
  `dst_time_eq_one_hundred_seventy_nine_of_src_base_eq_3064991081731777716716694054300618367237478244367204352m_add_56759094106144031791049889894455895689582930451244525` /
  `dst_base_eq_54m_add_1_of_src_base_eq_3064991081731777716716694054300618367237478244367204352m_add_56759094106144031791049889894455895689582930451244525`,
  and the residual `one_hundred_eighty_le_dst_time_of_src_base_eq_3064991081731777716716694054300618367237478244367204352m_add_1589254634972032890149396917044765079308322052634846701` /
  `two_pow_dst_time_sub_one_hundred_eighty_mul_dst_base_eq_27m_add_14_of_src_base_eq_3064991081731777716716694054300618367237478244367204352m_add_1589254634972032890149396917044765079308322052634846701`
- that `time ≥ 175` helper-refactor seam was confirmed by targeted build
  session `92506`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_eighty_add_and_dst_base_eq_of_src_base_eq_3064991081731777716716694054300618367237478244367204352m_add_1589254634972032890149396917044765079308322052634846701_of_factorization`
  and
  `dst_time_ge_one_hundred_eighty_add_and_scaled_base_eq_of_src_base_eq_3064991081731777716716694054300618367237478244367204352m_add_1589254634972032890149396917044765079308322052634846701_of_factorization`
  is now green through the next live higher-time seam on
  `base = 3064991081731777716716694054300618367237478244367204352*m + 1589254634972032890149396917044765079308322052634846701`
  ending on exact `time = 180`, exact `time = 181`, exact `time = 182`,
  exact `time = 183`, exact `time = 184`, and residual `time ≥ 185`
- that seam rewires the live branch through the exact shells
  `dst_time_eq_one_hundred_eighty_of_src_base_eq_6129982163463555433433388108601236734474956488734408704m_add_4654245716703810606866090971345383446545800297002051053` /
  `dst_base_eq_54m_add_41_of_src_base_eq_6129982163463555433433388108601236734474956488734408704m_add_4654245716703810606866090971345383446545800297002051053`,
  `dst_time_eq_one_hundred_eighty_one_of_src_base_eq_12259964326927110866866776217202473468949912977468817408m_add_1589254634972032890149396917044765079308322052634846701` /
  `dst_base_eq_54m_add_7_of_src_base_eq_12259964326927110866866776217202473468949912977468817408m_add_1589254634972032890149396917044765079308322052634846701`,
  `dst_time_eq_one_hundred_eighty_two_of_src_base_eq_24519928653854221733733552434404946937899825954937634816m_add_7719236798435588323582785025646001813783278541369255405` /
  `dst_base_eq_54m_add_17_of_src_base_eq_24519928653854221733733552434404946937899825954937634816m_add_7719236798435588323582785025646001813783278541369255405`,
  `dst_time_eq_one_hundred_eighty_three_of_src_base_eq_49039857307708443467467104868809893875799651909875269632m_add_44499129779216920924183113677253422220633017473775707629` /
  `dst_base_eq_54m_add_49_of_src_base_eq_49039857307708443467467104868809893875799651909875269632m_add_44499129779216920924183113677253422220633017473775707629`,
  `dst_time_eq_one_hundred_eighty_four_of_src_base_eq_98079714615416886934934209737619787751599303819750539264m_add_19979201125362699190449561242848475282733191518838072813` /
  `dst_base_eq_54m_add_11_of_src_base_eq_98079714615416886934934209737619787751599303819750539264m_add_19979201125362699190449561242848475282733191518838072813`,
  and the residual `one_hundred_eighty_five_le_dst_time_of_src_base_eq_98079714615416886934934209737619787751599303819750539264m_add_69019058433071142657916666111658369158532843428713342445` /
  `two_pow_dst_time_sub_one_hundred_eighty_five_mul_dst_base_eq_27m_add_19_of_src_base_eq_98079714615416886934934209737619787751599303819750539264m_add_69019058433071142657916666111658369158532843428713342445`
- that `time ≥ 180` helper-refactor seam was confirmed by targeted build
  session `14054`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_eighty_five_add_and_dst_base_eq_of_src_base_eq_98079714615416886934934209737619787751599303819750539264m_add_69019058433071142657916666111658369158532843428713342445_of_factorization`
  and
  `dst_time_ge_one_hundred_eighty_five_add_and_scaled_base_eq_of_src_base_eq_98079714615416886934934209737619787751599303819750539264m_add_69019058433071142657916666111658369158532843428713342445_of_factorization`
  is now green through the next live higher-time seam on
  `base = 98079714615416886934934209737619787751599303819750539264*m + 69019058433071142657916666111658369158532843428713342445`
  ending on exact `time = 185`, exact `time = 186`, exact `time = 187`, and
  residual `time ≥ 188`
- that seam rewires the live branch through the exact shells
  `dst_time_eq_one_hundred_eighty_five_of_src_base_eq_196159429230833773869868419475239575503198607639501078528m_add_69019058433071142657916666111658369158532843428713342445` /
  `dst_base_eq_54m_add_19_of_src_base_eq_196159429230833773869868419475239575503198607639501078528m_add_69019058433071142657916666111658369158532843428713342445`,
  `dst_time_eq_one_hundred_eighty_six_of_src_base_eq_392318858461667547739736838950479151006397215279002157056m_add_167098773048488029592850875849278156910132147248463881709` /
  `dst_base_eq_54m_add_23_of_src_base_eq_392318858461667547739736838950479151006397215279002157056m_add_167098773048488029592850875849278156910132147248463881709`,
  `dst_time_eq_one_hundred_eighty_seven_of_src_base_eq_784637716923335095479473677900958302012794430558004314112m_add_363258202279321803462719295324517732413330754887964960237` /
  `dst_base_eq_54m_add_25_of_src_base_eq_784637716923335095479473677900958302012794430558004314112m_add_363258202279321803462719295324517732413330754887964960237`,
  and the residual `one_hundred_eighty_eight_le_dst_time_of_src_base_eq_784637716923335095479473677900958302012794430558004314112m_add_755577060740989351202456134274996883419727970166967117293` /
  `two_pow_dst_time_sub_one_hundred_eighty_eight_mul_dst_base_eq_27m_add_26_of_src_base_eq_784637716923335095479473677900958302012794430558004314112m_add_755577060740989351202456134274996883419727970166967117293`
- that `time ≥ 185` helper-refactor seam was confirmed by targeted build
  session `8161`
- the next higher-time helper layer
  `dst_time_eq_one_hundred_eighty_eight_add_and_dst_base_eq_of_src_base_eq_784637716923335095479473677900958302012794430558004314112m_add_755577060740989351202456134274996883419727970166967117293_of_factorization`
  and
  `dst_time_ge_one_hundred_eighty_eight_add_and_scaled_base_eq_of_src_base_eq_784637716923335095479473677900958302012794430558004314112m_add_755577060740989351202456134274996883419727970166967117293_of_factorization`
  is now green through the next live higher-time seam on
  `base = 784637716923335095479473677900958302012794430558004314112*m + 755577060740989351202456134274996883419727970166967117293`
  ending on exact `time = 188`, exact `time = 189`, exact `time = 190`,
  exact `time = 191`, exact `time = 192`, and residual `time ≥ 193`
- that seam rewires the live branch through the exact shells
  `dst_time_eq_one_hundred_eighty_eight_of_src_base_eq_1569275433846670190958947355801916604025588861116008628224m_add_1540214777664324446681929812175955185432522400724971431405` /
  `dst_base_eq_54m_add_53_of_src_base_eq_1569275433846670190958947355801916604025588861116008628224m_add_1540214777664324446681929812175955185432522400724971431405`,
  `dst_time_eq_one_hundred_eighty_nine_of_src_base_eq_3138550867693340381917894711603833208051177722232017256448m_add_755577060740989351202456134274996883419727970166967117293` /
  `dst_base_eq_54m_add_13_of_src_base_eq_3138550867693340381917894711603833208051177722232017256448m_add_755577060740989351202456134274996883419727970166967117293`,
  `dst_time_eq_one_hundred_ninety_of_src_base_eq_6277101735386680763835789423207666416102355444464034512896m_add_5463403362280999924079298201680746695496494553514993001965` /
  `dst_base_eq_54m_add_47_of_src_base_eq_6277101735386680763835789423207666416102355444464034512896m_add_5463403362280999924079298201680746695496494553514993001965`,
  `dst_time_eq_one_hundred_ninety_one_of_src_base_eq_12554203470773361527671578846415332832204710888928069025792m_add_8601954229974340305997192913284579903547672275747010258413` /
  `dst_base_eq_54m_add_37_of_src_base_eq_12554203470773361527671578846415332832204710888928069025792m_add_8601954229974340305997192913284579903547672275747010258413`,
  `dst_time_eq_one_hundred_ninety_two_of_src_base_eq_25108406941546723055343157692830665664409421777856138051584m_add_2324852494587659542161403490076913487445316831282975745517` /
  `dst_base_eq_54m_add_5_of_src_base_eq_25108406941546723055343157692830665664409421777856138051584m_add_2324852494587659542161403490076913487445316831282975745517`,
  and the residual `one_hundred_ninety_three_le_dst_time_of_src_base_eq_25108406941546723055343157692830665664409421777856138051584m_add_14879055965361021069832982336492246319650027720211044771309` /
  `two_pow_dst_time_sub_one_hundred_ninety_three_mul_dst_base_eq_27m_add_16_of_src_base_eq_25108406941546723055343157692830665664409421777856138051584m_add_14879055965361021069832982336492246319650027720211044771309`
- that `time ≥ 188` helper-refactor seam was confirmed by targeted build
  session `55611`

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

These theorems are the current recorded green boundary in the worktree. The
current source hash, built `olean`, frontier note, handoff file, and
declaration index are intended to agree on that boundary.

### Active Verification State

The live targeted verification run for the current observer-gap vanishing
package completed successfully:

- session id: `43657`
- command: `lake build UFRF.CollatzConcurrentScales`
- result: success with the familiar pre-existing warnings only
- exact green-source hash is recorded in
  [COLLATZ_TARGETED_BUILD_STATUS.json](/tmp/repo-collatz-memory-loop/docs/proofs/COLLATZ_TARGETED_BUILD_STATUS.json)
- supporting cumulative sandbox telemetry in
  `/private/tmp/collatz-eject-batch-20260413T031238Z` is green through
  eject-20 and first fails at eject-21; that failure is now resolved in the
  live source by the repaired manual split
- a corrected residual-seeded rerun at
  `/private/tmp/collatz-eject-batch-038923a-eject22-32-rerun-20260413T042552Z`
  is green through eject-32
- the prepared residual-seeded wave pipeline at
  `/private/tmp/collatz-eject-wave-pipeline-post32-20260413T045249Z`
  then completed green through eject-80 in five waves of at most 10 builds
  each with the same 1-second stagger

### Recovered Failed Probe

The first attempted deeper observer-gap shell lift used the same theorem name:

- `exists_observerGap9387_832_thirdCarrier_of_repeatCore832Transition_chain3`

That earlier draft failed a targeted build and was intentionally removed from
source before this handoff layer was prepared. The theorem has now been
rederived fresh and verified green using a new proof that overlaps consecutive
carrier facts; do not conflate the current proof with the discarded script.

The same caution now applies at the current frontier: the first batch-generated
exact `(4,21)` template is not a theorem just because the split idea is
natural. Its old odd-factor proof shape fails at eject-21 and should not be
trusted without fresh single-eject analysis.

### Artifact Sync State

As of this snapshot:

- the recorded green source hash in
  [COLLATZ_TARGETED_BUILD_STATUS.json](/tmp/repo-collatz-memory-loop/docs/proofs/COLLATZ_TARGETED_BUILD_STATUS.json)
  now matches the current source boundary through exact eject-32 with residual
  `dst.eject ≥ 33`, through the initial helper-normalized `time = 5/6/7`
  shells, and through the higher-time helper-normalized ladder ending on
  exact `time = 192` with residual `time ≥ 193`
- that same recorded green boundary also includes the returned-shell transport
  wrappers
  `returned_twenty_eight_shell_transport_of_src_base_eq_174224571863520493293247799005065324265472m_add_129055238417422587624627999263011351307757`,
  `returned_forty_four_shell_transport_of_src_base_eq_43556142965880123323311949751266331066368m_add_41942952485662340978004099760478689175021`,
  `returned_thirty_one_shell_transport_of_src_base_eq_5316911983139663491615228241121378304m_add_3150762656675356143179394513257113069`,
  and
  `returned_thirty_six_shell_transport_of_src_base_eq_170141183460469231731687303715884105728m_add_88221354386909972009023046371199165933`,
  together with the `VerifiedHigherTimeReturnClock` closure/dispatcher layer
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
  refinement of the remaining tail, through the exact eject-14 /
  residual eject-`≥ 15` refinement of the remaining tail, and now through the
  exact eject-15 / residual eject-`≥ 16`, exact eject-16 /
  residual eject-`≥ 17`, exact eject-17 / residual eject-`≥ 18`, exact
  eject-18 / residual eject-`≥ 19`, exact eject-19 / residual eject-`≥ 20`,
  exact eject-20 / residual eject-`≥ 21`, exact eject-21 /
  residual eject-`≥ 22`, exact eject-22 / residual eject-`≥ 23`, exact
  eject-23 / residual eject-`≥ 24`, exact eject-24 / residual eject-`≥ 25`,
  exact eject-25 / residual eject-`≥ 26`, exact eject-26 /
  residual eject-`≥ 27`, exact eject-27 / residual eject-`≥ 28`, exact
  eject-28 / residual eject-`≥ 29`, exact eject-29 / residual eject-`≥ 30`,
  exact eject-30 / residual eject-`≥ 31`, exact eject-31 /
  residual eject-`≥ 32`, and exact eject-32 / residual eject-`≥ 33`
  refinements of that same tail
- the same frontier summary now also records the first helper-normalized
  higher-time seam on `base = 512*m + 493`, including exact `time = 8`,
  exact `time = 9`, and residual `time ≥ 10`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on `base = 2048*m + 1517`, including exact `time = 10`,
  exact `time = 11`, exact `time = 12`, and residual `time ≥ 13`
- the same frontier summary now also records the continuing higher-time ladder
  through exact `time = 174` with residual `time ≥ 175`, plus the returned
  shell / `VerifiedHigherTimeReturnClock` packaging at that same boundary
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 44601490397061246283071436545296723011960832*m + 23126698724402127702333337467931634154350061`,
  including exact `time = 144`, exact `time = 145`, exact `time = 146`,
  exact `time = 147`, and residual `time ≥ 148`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 713623846352979940529142984724747568191373312*m + 290735641106769605400761956739711972226115053`,
  including exact `time = 148`, exact `time = 149`, exact `time = 150`,
  exact `time = 151`, and residual `time ≥ 152`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 11417981541647679048466287755595961091061972992*m + 10995093336401468713337906727610925495096714733`,
  including exact `time = 152`, exact `time = 153`, and residual `time ≥ 154`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 45671926166590716193865151022383844364247891968*m + 33831056419696826810270482238802847677220660717`,
  including exact `time = 154`, exact `time = 155`, exact `time = 156`, and
  residual `time ≥ 157`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 365375409332725729550921208179070754913983135744*m + 216518761086059691585731086328338225134212228589`,
  including exact `time = 157`, exact `time = 158`, exact `time = 159`,
  exact `time = 160`, exact `time = 161`, and residual `time ≥ 162`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 11692013098647223345629478661730264157247460343808*m + 6062525310409671364400470417193470303757942400493`,
  including exact `time = 162`, exact `time = 163`, exact `time = 164`,
  exact `time = 165`, and residual `time ≥ 166`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 187072209578355573530071658587684226515959365500928*m + 76214603902293011438177342387575055247242704463341`,
  including exact `time = 166`, exact `time = 167`, exact `time = 168`,
  exact `time = 169`, and residual `time ≥ 170`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 2993155353253689176481146537402947624255349848014848*m + 2882297747577626614389252221202838452986633186977261`,
  including exact `time = 170`, exact `time = 171`, and residual
  `time ≥ 172`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 11972621413014756705924586149611790497021399392059392*m + 8868608454085004967351545296008733701497332883006957`,
  including exact `time = 172`, exact `time = 173`, exact `time = 174`, and
  residual `time ≥ 175`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 95780971304118053647396689196894323976171195136475136*m + 56759094106144031791049889894455895689582930451244525`,
  including exact `time = 175`, exact `time = 176`, exact `time = 177`,
  exact `time = 178`, exact `time = 179`, and residual `time ≥ 180`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 3064991081731777716716694054300618367237478244367204352*m + 1589254634972032890149396917044765079308322052634846701`,
  including exact `time = 180`, exact `time = 181`, exact `time = 182`,
  exact `time = 183`, exact `time = 184`, and residual `time ≥ 185`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 98079714615416886934934209737619787751599303819750539264*m + 69019058433071142657916666111658369158532843428713342445`,
  including exact `time = 185`, exact `time = 186`, exact `time = 187`, and
  residual `time ≥ 188`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 784637716923335095479473677900958302012794430558004314112*m + 755577060740989351202456134274996883419727970166967117293`,
  including exact `time = 188`, exact `time = 189`, exact `time = 190`,
  exact `time = 191`, exact `time = 192`, and residual `time ≥ 193`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 25108406941546723055343157692830665664409421777856138051584*m + 14879055965361021069832982336492246319650027720211044771309`,
  including exact `time = 193`, exact `time = 194`, exact `time = 195`,
  exact `time = 196`, exact `time = 197`, and residual `time ≥ 198`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 803469022129495137770981046170581301261101496891396417650688*m + 416613567030108589955323505421782896950200776165909253596653`,
  including exact `time = 198`, exact `time = 199`, exact `time = 200`,
  exact `time = 201`, exact `time = 202`, and residual `time ≥ 203`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 205688069665150755269371147819668813122841983204197482918576128*m + 198069993010885912481616660863384783007181169011449427995665901`,
  including exact `time = 206`, exact `time = 207`, exact `time = 208`,
  exact `time = 209`, exact `time = 210`, and residual `time ≥ 211`
- the same frontier summary now also records the next helper-normalized
  higher-time seam on
  `base = 6582018229284824168619876730229402019930943462534319453394436096*m + 3900455246983599507330297321617423419218336866687004120530036205`,
  including exact `time = 211`, exact `time = 212`, exact `time = 213`,
  exact `time = 214`, exact `time = 215`, and residual `time ≥ 216`
- the symbol index has been regenerated after the latest green targeted build
  and now reports `1665` declarations
- Rover is now synced through the higher-time ladder ending on exact
  `time = 215` with residual `time ≥ 216`, including the new
  `time ≥ 211` seam together with `time ≥ 206`, `time ≥ 203`, `time ≥ 198`, `time ≥ 193`, `time ≥ 188`,
  `time ≥ 185`, `time ≥ 180`,
  `time ≥ 175`, `time ≥ 172`, `time ≥ 170`,
  `time ≥ 166`, `time ≥ 162`, `time ≥ 157`,
  `time ≥ 154`, `time ≥ 152`, and `time ≥ 148` factorization seams, the earlier
  `time ≥ 144` and `time ≥ 139` seams, and the older returned-shell
  transport / return-clock boundary
- Rover also records the larger residual-seeded telemetry result through
  eject-80 via
  `20260413T053628Z-residual-seeded-batch-telemetry-update-the-ejec.md`

That means the repo is back in the expected compact-safe posture:

- the local green boundary is known and freshly rebuilt
- the current source matches that recorded boundary
- docs, status, Rover, and the symbol index are aligned to the same source
  checkpoint
- the farther wave telemetry is also recorded, but it remains explicitly
  separate from the live-source green boundary
- the current compact-status warning set is back to `dirty-worktree` only, so
  keep the last pushed checkpoint separate from this local green worktree
  until the boundary is committed

Current source state beyond that banked posture:

- there is no higher-time source-only delta right now; the live source,
  status file, frontier note, symbol index, and Rover note are being banked
  together on session `25387`
- the recorded green boundary is now session `25387`, source hash
  `5b71b1d6af1cb42a6d7455ba1a9a57ec3ca784cb6f2d26d80ef3185444476d28`,
  exact `time = 215`, residual `time ≥ 216`
- the helper-normalized `time ≥ 211` shell has now been promoted into the
  verified boundary rather than kept as source-only WIP
- the next source-side theorem target starts from the new residual
  `two_pow_dst_time_sub_two_hundred_sixteen_mul_dst_base_eq_27m_add_14_of_src_base_eq_210624583337114373395836055367340864637790190801098222508621955072m_add_109212746915540786205248325005287855738113432267236115374841013741`
  and should stay separate from the green boundary until its own targeted
  build is confirmed

## Immediate Next Step

1. treat session `25387` as the last confirmed green source boundary:
   exact eject-32 / residual eject-`≥ 33` on the `time = 4` side, plus the
   helper-normalized higher-time ladder through exact `time = 215` with
   residual `time ≥ 216`, including the returned-shell transport wrappers and
   `VerifiedHigherTimeReturnClock`
2. keep the next theorem family explicitly separate from that checkpoint:
   the next seam should start from the now-green residual
   `time ≥ 216` law on
   `base = 210624583337114373395836055367340864637790190801098222508621955072*m + 109212746915540786205248325005287855738113432267236115374841013741`
   with transport `2^(dst.time - 216) * dst.base = 27*m + 14`
3. only after the next source-side theorem block is written should another
   targeted `lake build UFRF.CollatzConcurrentScales` be started
4. keep the generated eject-wave telemetry explicitly separate from the live
   source checkpoint until more of that continuation is promoted into source
   and rebuilt here
5. do not touch `scripts/collatz_eject_batch.py` as part of proof bookkeeping;
   it already carries user-side harness edits outside the Lean proof boundary

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

Current checkpoint state:

- last pushed checkpoint before this local boundary is `13cc195`
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
  the zero-shell `time = 4` eject split now through
  `dst_slice_eq_4_32_of_src_base_eq_7421703487488r_add_3733601126989` with
  residual `thirty_three_le_dst_eject_of_src_base_eq_7421703487488r_add_22749383245`,
  plus the initial shared `time = 5` helper seam through
  `dst_slice_eq_5_7_of_src_base_eq_16384r_add_7725` with residual
  `eight_le_dst_eject_of_src_base_eq_16384r_add_15917`, and the initial shared
  `time = 6` helper seam through
  `dst_slice_eq_6_5_of_src_base_eq_8192r_add_7021` with residual
  `six_le_dst_eject_of_src_base_eq_8192r_add_2925`, and the initial shared
  `time = 7` helper seam through
  `dst_slice_eq_7_6_of_src_base_eq_32768r_add_32493` with residual
  `seven_le_dst_eject_of_src_base_eq_32768r_add_16109`, and the initial
  higher-time helper seam on `base = 512*m + 493` through
  `dst_time_eq_eight_add_and_dst_base_eq_of_src_base_eq_512m_add_493_of_factorization`,
  `dst_time_ge_eight_add_and_scaled_base_eq_of_src_base_eq_512m_add_493_of_factorization`,
  the exact cases
  `dst_time_eq_eight_of_src_base_eq_1024m_add_1005` /
  `dst_base_eq_54m_add_53_of_src_base_eq_1024m_add_1005`,
  `dst_time_eq_nine_of_src_base_eq_2048m_add_493` /
  `dst_base_eq_54m_add_13_of_src_base_eq_2048m_add_493`, and the residual
  `ten_le_dst_time_of_src_base_eq_2048m_add_1517` /
  `two_pow_dst_time_sub_ten_mul_dst_base_eq_27m_add_20_of_src_base_eq_2048m_add_1517`,
  and the next higher-time helper seam on `base = 2048*m + 1517` through
  `dst_time_eq_ten_add_and_dst_base_eq_of_src_base_eq_2048m_add_1517_of_factorization`,
  `dst_time_ge_ten_add_and_scaled_base_eq_of_src_base_eq_2048m_add_1517_of_factorization`,
  the exact cases
  `dst_time_eq_ten_of_src_base_eq_4096m_add_3565` /
  `dst_base_eq_54m_add_47_of_src_base_eq_4096m_add_3565`,
  `dst_time_eq_eleven_of_src_base_eq_8192m_add_5613` /
  `dst_base_eq_54m_add_37_of_src_base_eq_8192m_add_5613`,
  `dst_time_eq_twelve_of_src_base_eq_16384m_add_1517` /
  `dst_base_eq_54m_add_5_of_src_base_eq_16384m_add_1517`, and the residual
  `thirteen_le_dst_time_of_src_base_eq_16384m_add_9709` /
  `two_pow_dst_time_sub_thirteen_mul_dst_base_eq_27m_add_16_of_src_base_eq_16384m_add_9709`,
  and the next higher-time helper seam on `base = 16384*m + 9709` through
  `dst_time_eq_thirteen_add_and_dst_base_eq_of_src_base_eq_16384m_add_9709_of_factorization`,
  `dst_time_ge_thirteen_add_and_scaled_base_eq_of_src_base_eq_16384m_add_9709_of_factorization`,
  the exact cases
  `dst_time_eq_thirteen_of_src_base_eq_32768m_add_26093` /
  `dst_base_eq_54m_add_43_of_src_base_eq_32768m_add_26093`,
  `dst_time_eq_fourteen_of_src_base_eq_65536m_add_42477` /
  `dst_base_eq_54m_add_35_of_src_base_eq_65536m_add_42477`,
  `dst_time_eq_fifteen_of_src_base_eq_131072m_add_75245` /
  `dst_base_eq_54m_add_31_of_src_base_eq_131072m_add_75245`,
  `dst_time_eq_sixteen_of_src_base_eq_262144m_add_140781` /
  `dst_base_eq_54m_add_29_of_src_base_eq_262144m_add_140781`,
  `dst_time_eq_seventeen_of_src_base_eq_524288m_add_9709` /
  `dst_base_eq_54m_add_1_of_src_base_eq_524288m_add_9709`, and the residual
  `eighteen_le_dst_time_of_src_base_eq_524288m_add_271853` /
  `two_pow_dst_time_sub_eighteen_mul_dst_base_eq_27m_add_14_of_src_base_eq_524288m_add_271853`,
  and the continuing higher-time ladder through exact `time = 174` /
  residual `time ≥ 175`, including the returned-shell transports,
  `VerifiedHigherTimeReturnClock` packaging, and the newly green
  `time ≥ 139`, `time ≥ 144`, `time ≥ 148`, `time ≥ 152`, `time ≥ 154`,
  `time ≥ 157`, `time ≥ 162`, `time ≥ 166`, `time ≥ 170`, and `time ≥ 172`
  factorization seams
- targeted build session `1430` completed green in the actual repo for that
  current local boundary
- targeted build session `92506` then completed green in the actual repo for
  the next helper-normalized higher-time seam through exact `time = 179` /
  residual `time ≥ 180`
- targeted build session `14054` then completed green in the actual repo for
  the next helper-normalized higher-time seam through exact `time = 184` /
  residual `time ≥ 185`
- targeted build session `8161` then completed green in the actual repo for
  the next helper-normalized higher-time seam through exact `time = 187` /
  residual `time ≥ 188`
- targeted build session `55611` then completed green in the actual repo for
  the next helper-normalized higher-time seam through exact `time = 192` /
  residual `time ≥ 193`
- targeted build session `81576` then completed green in the actual repo for
  the next helper-normalized higher-time seam through exact `time = 197` /
  residual `time ≥ 198`
- targeted build session `43657` then completed green in the actual repo for
  the next helper-normalized higher-time seam through exact `time = 202` /
  residual `time ≥ 203`
- targeted build session `45924` then completed green in the actual repo for
  the next helper-normalized higher-time seam through exact `time = 205` /
  residual `time ≥ 206`
- targeted build session `80271` then completed green in the actual repo for
  the next helper-normalized higher-time seam through exact `time = 210` /
  residual `time ≥ 211`
- targeted build session `25387` then completed green in the actual repo for
  the next helper-normalized higher-time seam through exact `time = 215` /
  residual `time ≥ 216`
- supporting batch telemetry in `/private/tmp/collatz-eject-batch-20260413T031238Z`
  is cumulatively green through eject-20 and first fails at eject-21, which is
  why eject-22 must now be derived from the actual residual law rather than
  extrapolated blindly
- the corrected residual-seeded rerun in
  `/private/tmp/collatz-eject-batch-038923a-eject22-32-rerun-20260413T042552Z`
  is green through eject-32
- the prepared wave runner
  `scripts/collatz_eject_wave_pipeline.py` is ready to continue from eject-33
  through eject-80 in waves of at most 10 builds with a 1-second stagger

Immediate objective from this boundary:

- helper-normalize the live `time ≥ 216` shell next, starting from the
  residual
  `base = 210624583337114373395836055367340864637790190801098222508621955072*m + 109212746915540786205248325005287855738113432267236115374841013741`
  transport and pushing that new `27*m + 14` branch into the next shared
  factorization-helper seam
- keep the larger eject-wave harness as telemetry support, not as a substitute
  for the live-source targeted-build boundary
