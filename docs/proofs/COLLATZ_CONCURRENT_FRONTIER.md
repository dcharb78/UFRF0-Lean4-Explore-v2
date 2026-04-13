# Collatz Concurrent Frontier

This note records the current proof frontier for the intrinsic concurrent /
multiscale Collatz program centered on
`UFRF/CollatzConcurrentScales.lean`.

Read this note before starting new proof work in a fresh conversation.

For compact-safe resume on fresh threads, also read
`docs/proofs/COLLATZ_COMPACT_HANDOFF.md` first. That file is the short
operational layer that must keep the last green boundary separate from any
newer unverified source edits, active build sessions, or unsynced
index/Rover state.

## Local Name Workflow

For this frontier file, use two layers together:

- Rover / curated memory for theorem clusters, rationale, and best-next-family
  context.
- The generated declaration index for exact local names and line lookup:
  - `docs/proofs/COLLATZ_CONCURRENT_SYMBOL_INDEX.md`
  - `docs/proofs/COLLATZ_CONCURRENT_SYMBOL_INDEX.json`

Regenerate the index after declaration movement with:

`python3 scripts/generate_decl_index.py --input UFRF/CollatzConcurrentScales.lean --json docs/proofs/COLLATZ_CONCURRENT_SYMBOL_INDEX.json --markdown docs/proofs/COLLATZ_CONCURRENT_SYMBOL_INDEX.md --title "Collatz Concurrent Scales Symbol Index"`

Before compacting or opening a new thread, run:

`python3 scripts/collatz_compact_status.py`

If that script reports warnings, do not flatten the current state into one
verified summary. Report the `last green checkpoint` and `current WIP in
source` separately.

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
- Older pushed checkpoint before this boundary: `054e0b3`
- Older pushed message: `Package affine five-step return-machine self-map`
- Current worktree state: targeted `lake build UFRF.CollatzConcurrentScales`
  is green after adding the higher-time `32*k + 13` source self-threshold /
  value / radial package, the shared `9387` observer-line bridge to the older
  repeat-core package, the bounded observer-gap coordinate on that common
  line, the immediate two-step observer-gap chain wrapper, and the new carrier
  theorem
  `exists_observerGap9387_832_carrier_of_repeatCore832Transition_chain`, and
  the three-step shell-lift theorem
  `exists_observerGap9387_832_thirdCarrier_of_repeatCore832Transition_chain3`,
  the fourth-carrier / gate package
  `exists_observerGap9387_832_fourthCarrier_of_repeatCore832Transition_chain4`
  and
  `exists_observerGap9387_832_fourthCarrier_with_gate_of_repeatCore832Transition_chain5`,
  the early vanishing theorems
  `observerGap9387_832_eq_zero_of_repeatCore832Transition_chain5` and
  `observerGap9387_832_zero_block_of_repeatCore832Transition_chain5`, and the
  higher-time affine zero-shell equivalence
  `observerGap9387_832_eq_zero_of_src_base_eq_864m_add_589` /
  `exists_src_base_eq_864m_add_589_of_observerGap9387_832_eq_zero_of_src_base_mod32_eq13`,
  the specialized transport law
  `two_pow_dst_time_sub_four_mul_dst_base_eq_729m_add_497_of_src_base_eq_864m_add_589`,
  and its first exact destination-shell split through
  `dst_time_eq_seven_of_src_base_eq_13824m_add_13549` /
  `dst_base_eq_1458m_add_1429_of_src_base_eq_13824m_add_13549`, together
  with the theorem-level reindexing bridge back into the established
  `54*k + 11/19/23/25` shell families, and the first destination-eject split
  of the zero-shell `time = 4` case, the parity split of its residual
  eject-`≥ 5` family, the next exact refinement of that odd residual into an
  exact eject-7 branch plus a residual eject-`≥ 8` tail, and the next exact
  refinement of the remaining tail into an exact eject-8 branch plus a
  residual eject-`≥ 9` tail, and the next exact refinement of that remaining
  tail into an exact eject-9 branch plus a residual eject-`≥ 10` tail, and
  the next exact refinement of that remaining tail into an exact eject-10
  branch plus a residual eject-`≥ 11` tail, and the next exact refinement of
  that remaining tail into an exact eject-11 branch plus a residual
  eject-`≥ 12` tail, and the next exact refinement of that remaining tail
  into an exact eject-12 branch plus a residual eject-`≥ 13` tail, and the
  next exact refinement of that remaining tail into an exact eject-13 branch
  plus a residual eject-`≥ 14` tail

## Resume State

On fresh or compacted threads, separate the verified checkpoint from any newer
source edits before describing the frontier.

- Last green checkpoint:
  - targeted `lake build UFRF.CollatzConcurrentScales` is green through exact
    `time = 135`
  - the verified exact shell family immediately beyond the old
    `133 / ≥134` boundary is now:
    `dst_time_eq_one_hundred_thirty_four_of_src_base_eq_87112285931760246646623899502532662132736m_add_85499095451542464301316049511745020241389`,
    `dst_base_eq_54m_add_53_of_src_base_eq_87112285931760246646623899502532662132736m_add_85499095451542464301316049511745020241389`,
    `dst_time_eq_one_hundred_thirty_five_of_src_base_eq_174224571863520493293247799005065324265472m_add_41942952485662340978004099760478689175021`,
    and
    `dst_base_eq_54m_add_13_of_src_base_eq_174224571863520493293247799005065324265472m_add_41942952485662340978004099760478689175021`
  - the verified residual shell is
    `base = 174224571863520493293247799005065324265472*r + 129055238417422587624627999263011351307757`
  - the verified residual transport law is
    `dst.time ≥ 136` together with
    `2^(dst.time - 136) * dst.base = 27*r + 20`
  - the verified recurrence theorem is now also
    `returned_twenty_eight_shell_transport_of_src_base_eq_174224571863520493293247799005065324265472m_add_129055238417422587624627999263011351307757`,
    packaging that returned `27*r + 20` residual as an explicit re-entry into
    `VerifiedHigherTimeReturnClock.c20` via the affine source rewrite
    `m ↦ 262144*m + 194180`
  - the verified source now also contains two clock-namespace packaging
    theorems for that same re-entry:
    `VerifiedHigherTimeReturnClock.c26_residual_reenters_c20_of_src_base_eq_174224571863520493293247799005065324265472m_add_129055238417422587624627999263011351307757`
    states it directly against the `c20` clock data, and
    `VerifiedHigherTimeReturnClock.c26_residual_reenters_next_of_src_base_eq_174224571863520493293247799005065324265472m_add_129055238417422587624627999263011351307757`
    packages the same fact in machine-internal form using `next .c26`
  - the verified recurrence theorem is
    `returned_forty_four_shell_transport_of_src_base_eq_43556142965880123323311949751266331066368m_add_41942952485662340978004099760478689175021`
    identifying that returned `27*r + 26` law with the older `time ≥ 44`
    shell after renormalization
    `m ↦ 1237940039285380274899124224*m + 1192090408200736561013971474`
  - the verified source now also contains the explicit finite-state wrapper
    `VerifiedHigherTimeReturnClock` with clock cycle
    `20 → 16 → 14 → 11 → 26 → 20`
  - the dispatcher theorem
    `VerifiedHigherTimeReturnClock.transport_of_eq_src_base`
    packages the five verified scale-`2^90` return transports as one source
    machine instead of five isolated shell facts
  - the green source now also contains explicit live-residual machine data
    `VerifiedHigherTimeReturnClock.residualCoeff`,
    `VerifiedHigherTimeReturnClock.residualConst`,
    `VerifiedHigherTimeReturnClock.residualParamScale`, and
    `VerifiedHigherTimeReturnClock.residualParamShift`, together with the
    affine identification theorem
    `VerifiedHigherTimeReturnClock.residual_eq_next_reindexed`
  - the new structural gain is the uniform closure theorem
    `VerifiedHigherTimeReturnClock.residual_reenters_next_of_eq_src_base`:
    for any verified return clock `clk`, the currently live residual family
    beyond `clk` already re-enters `next clk` after the canonical affine
    parameter rewrite
  - for `c20/c16/c14/c11` that rewrite is the identity, so the live residual
    is exactly the next verified family; for `c26` it specializes to the
    previously verified nontrivial closure `q = 262144*r + 194180` back into
    `c20`
  - the verified source now also contains the explicit one-step and full-cycle
    parameter machine:
    `VerifiedHigherTimeReturnClock.nextParam`,
    `VerifiedHigherTimeReturnClock.step`,
    `VerifiedHigherTimeReturnClock.step_five_eq`, and
    `VerifiedHigherTimeReturnClock.nextParam_five_eq`
  - in particular, after one full verified cycle
    `20 → 16 → 14 → 11 → 26 → 20`, the clock label returns to itself and the
    canonical parameter is renormalized by the single affine law
    `m ↦ 262144*m + 194180`
  - the current green source also contains the explicitly exploratory
    namespace `ExploratoryPrimeVoice`, which calibrates a prime-root shell
    chart on small examples such as prime `5`, its first doubling shell, and
    the relation of `11` to that chart
  - that exploratory layer now also contains a candidate canonical
    prime-local state `ExploratoryPrimeVoice.canonicalState`, a joint
    `5/7/11/13` signature `ExploratoryPrimeVoice.JointState`, and exact
    theorems computing that signature on the five verified return residues
    `20, 16, 14, 11, 26`
  - it now also proves the bridge facts
    `ExploratoryPrimeVoice.value_returnJointState_agrees` and
    `ExploratoryPrimeVoice.value_returnJointState_next_agrees_add_delta`:
    all four prime-local views represent the same return residue value, and
    one step of the verified return machine adds the same signed residue delta
    in every prime-local view even though the shell coordinates reorganize
    differently
  - the exploratory bridge is now sharper than raw signature tables:
    `ExploratoryPrimeVoice.returnJointUpdate_p*_correction_eq_anchor_diff`
    proves that the residual offset correction is exactly the difference of
    old and new shell anchors, and
    `ExploratoryPrimeVoice.returnJointUpdate_p*_levelDelta_eq_shellShift`
    proves that the shell-level change is governed by a threshold-crossing
    law `ExploratoryPrimeVoice.shellShift` on the common next value, clipped
    at base level
  - the exploratory bridge is now also packaged as an actual update rule:
    `ExploratoryPrimeVoice.predictedLocalUpdate` and
    `ExploratoryPrimeVoice.predictedJointUpdate` define the local and joint
    reanchoring update from the current canonical state plus the common next
    residue value alone, and
    `ExploratoryPrimeVoice.returnJointUpdate_p*_eq_predictedLocalUpdate`
    together with
    `ExploratoryPrimeVoice.returnJointUpdate_eq_predictedJointUpdate`
    prove that the verified five-state return machine exactly matches that
    packaged common-next-value law on the exploratory `5/7/11/13` views
  - the exploratory source now also contains a first exact local-zero probe:
    `ExploratoryPrimeVoice.atAnchor`,
    `ExploratoryPrimeVoice.anchorSignature`, and
    `ExploratoryPrimeVoice.returnAnchorSignature_eq`
    prove that, on the sampled `5/7/11/13` views of the verified return cycle,
    exact shell-anchor occupancy rotates as
    `p5 → none → p7 → p11 → p13`
    across the residues `20 → 16 → 14 → 11 → 26`
  - this is still exploratory: it gives a kernel-checked candidate bridge
    object from the verified return machine to concurrent prime-local views,
    but it does not yet prove that this packaged update admits a monotone
    shrink-producing defect functional or extends beyond the verified return
    cycle without further source-state work
  - the exploratory source now also contains a general dyadic-shell / local-zero
    bridge:
    `ExploratoryPrimeVoice.anchorLevel_eq_of_eq_anchor`,
    `ExploratoryPrimeVoice.canonicalState_eq_anchor_state_of_eq_anchor`, and
    `ExploratoryPrimeVoice.atAnchor_canonicalState_of_eq_anchor`
    prove that for any positive `p`, the canonical prime-local state of
    `p * 2^k` is exactly `⟨k, 0⟩`, so dyadic shells of a prime are exact local
    zeros in this exploratory chart
  - that local-zero law is now sharpened to an exact characterization in the
    canonical prime chart:
    `ExploratoryPrimeVoice.eq_anchor_of_atAnchor_canonicalState`,
    `ExploratoryPrimeVoice.exists_eq_anchor_of_atAnchor_canonicalState`, and
    `ExploratoryPrimeVoice.atAnchor_canonicalState_iff_exists_eq_anchor`
    prove that a number sits exactly at local zero for `p` in this chart iff
    it is a dyadic shell `p * 2^k`
  - that characterization is now lifted to the actual sampled joint state:
    `ExploratoryPrimeVoice.atAnchor_jointState_p5_iff_exists_eq_anchor`,
    `ExploratoryPrimeVoice.atAnchor_jointState_p7_iff_exists_eq_anchor`,
    `ExploratoryPrimeVoice.atAnchor_jointState_p11_iff_exists_eq_anchor`, and
    `ExploratoryPrimeVoice.atAnchor_jointState_p13_iff_exists_eq_anchor`
    identify exact local zero on the `jointState` coordinates with membership
    in the corresponding dyadic prime shell
  - that joint-state shell criterion is now also packaged at tuple level:
    `ExploratoryPrimeVoice.shellSignature` and
    `ExploratoryPrimeVoice.anchorSignature_jointState_eq_shellSignature`
    identify the whole sampled local-zero signature
    `anchorSignature (jointState n)` with dyadic shell membership for
    `5/7/11/13`
  - Rover curated memory is synced through that checkpoint
  - the generated declaration index has been regenerated to reflect the
    current Lean source, including any active WIP beyond the checkpoint
- Active WIP beyond the checkpoint:
  - local green WIP beyond commit `054e0b3` now includes the source-state
    theorem
    `regimeIIState_selfThresholdDefect_eq_14k_add_6_sub_div27_of_time3_eject1_of_base_eq_32k_add_13`
    and its transition wrapper
    `src_selfThresholdDefect_eq_14k_add_6_sub_div27_of_src_base_eq_32k_add_13`
  - local green WIP beyond that now also includes the `32*k + 13` branch
    value/radial package
    `src_stateValue_eq_256k_add_103_of_src_base_eq_32k_add_13`,
    `src_radialGap_832_eq_256k_sub_729_of_src_base_eq_32k_add_13`,
    `dst_radialGap_832_eq_432k_sub_657_of_src_base_eq_32k_add_13`,
    and `src_radialGap_832_lt_dst_radialGap_832_of_src_base_eq_32k_add_13`
  - most importantly, local green WIP now includes the first explicit
    recurrence-style transport laws on that branch:
    `sixteen_mul_dst_stateValue_eq_twentySeven_mul_src_stateValue_add_19_of_src_base_eq_32k_add_13`
    and the guarded radial-gap analogue
    `sixteen_mul_dst_radialGap_832_eq_twentySeven_mul_src_radialGap_832_add_9171_of_src_base_eq_32k_add_13`
  - local green WIP now also includes the intrinsic congruence-form wrappers
    that the global `(3,1)` split will actually want to consume:
    `sixteen_mul_dst_stateValue_eq_twentySeven_mul_src_stateValue_add_19_of_src_base_mod32_eq13`,
    `src_radialGap_832_lt_dst_radialGap_832_of_src_base_mod32_eq13`, and
    `sixteen_mul_dst_radialGap_832_eq_twentySeven_mul_src_radialGap_832_add_9171_of_src_base_mod32_eq13`
  - local green WIP now also includes a bounded self-threshold/source-value
    ray package on that same higher-time source branch:
    `twoHundredSixteen_mul_src_selfThresholdDefect_eq_eleven_mul_src_stateValue_add_twentySeven_add_eight_mul_residue_of_src_base_eq_32k_add_13`,
    `twoHundredSixteen_mul_src_selfThresholdDefect_le_eleven_mul_src_stateValue_add_235_of_src_base_eq_32k_add_13`,
    and the intrinsic wrapper
    `twoHundredSixteen_mul_src_selfThresholdDefect_le_eleven_mul_src_stateValue_add_235_of_src_base_mod32_eq13`
  - local green WIP now also includes the target-facing `832` radial version of
    that same bounded ray:
    `twoHundredSixteen_mul_src_selfThresholdDefect_eq_eleven_mul_src_radialGap_832_add_9179_add_eight_mul_residue_of_src_base_eq_32k_add_13`,
    `twoHundredSixteen_mul_src_selfThresholdDefect_le_eleven_mul_src_radialGap_832_add_9387_of_src_base_eq_32k_add_13`,
    and the intrinsic wrapper
    `twoHundredSixteen_mul_src_selfThresholdDefect_le_eleven_mul_src_radialGap_832_add_9387_of_src_base_mod32_eq13`
  - local green WIP now also includes the first explicit bridge back into the
    older repeat-core observer package:
    `twoHundredSixteen_mul_src_selfThresholdDefect_eq_eleven_mul_src_radialGap_832_add_9387_of_repeatCore832Transition_chain10`
    showing that the first true cycle-return state lies on the exact same
    `832`-radial affine observer constant `9387` as the newer `32*k + 13`
    higher-time branch bound
  - local green WIP now also includes the exact finite gap-to-line package on
    the newer higher-time branch above `832`:
    `eleven_mul_src_radialGap_832_add_9387_eq_twoHundredSixteen_mul_src_selfThresholdDefect_add_eight_mul_twentySix_sub_residue_of_src_base_eq_32k_add_13`
    and
    `eleven_mul_src_radialGap_832_add_9387_le_twoHundredSixteen_mul_src_selfThresholdDefect_add_208_of_src_base_eq_32k_add_13`
    showing that the newer branch misses the shared `9387` line by an exact
    bounded finite residue, uniformly at most `208`
  - local green WIP now also includes the actual common observer coordinate
    `RegimeIIBadFrontierState.observerGap9387_832` together with theorems
    `observerGap9387_832_eq_zero_of_repeatCore832Transition_chain10`,
    `observerGap9387_832_eq_eight_mul_twentySix_sub_residue_of_src_base_eq_32k_add_13`,
    `zero_le_observerGap9387_832_of_src_base_eq_32k_add_13`,
    `observerGap9387_832_le_208_of_src_base_mod32_eq13`, and
    `exists_observerGap9387_832_eq_eight_mul_of_src_base_mod32_eq13`
    packaging the shared `9387` line as a genuine finite observer-gap
    coordinate with values in `8 * {0, ..., 26}`
  - local green WIP now also includes the normalization bridge
    `observerGap9387_832_eq_normalizedRepeatRadialGap832_sub_twoHundredSixteen_mul_normalizedRepeatSelfThresholdDefect832`,
    its target-facing value form
    `observerGap9387_832_eq_normalizedRepeatValue832_sub_twoHundredSixteen_mul_normalizedRepeatSelfThresholdDefect832_of_target_le`,
    and the inherited pure-phase transport law
    `sixteen_mul_dst_observerGap9387_832_eq_twentySeven_mul_src_observerGap9387_832_of_src_repeatThresholdSeedResidue832_eq_zero`
    so the older repeat-core normalization machinery now acts on the new
    common observer-gap coordinate directly on the pure affine phase
  - current source WIP beyond that green observer-gap normalization checkpoint
    now includes the immediate two-step persistence wrapper
    `sixteen_mul_dst_observerGap9387_832_eq_twentySeven_mul_src_observerGap9387_832_of_repeatCore832Transition_chain`
    so the observer-gap transport is available directly on repeat-core
    persistence chains without reopening the pure-phase gate by hand
  - local green WIP now also includes the carrier form
    `exists_observerGap9387_832_carrier_of_repeatCore832Transition_chain`
    packaging the same two-step observer-gap transport through one common
    integer `u` with source gap `16*u` and destination gap `27*u`
  - local green WIP now also includes the three-step shell lift
    `exists_observerGap9387_832_thirdCarrier_of_repeatCore832Transition_chain3`
    packaging the overlapped observer-gap carrier as one deeper integer
    `v` with `σ.src = 256*v`, `σ.dst = 432*v`, and `ρ.dst = 729*v`
  - local green WIP now also includes the four-step shell lift
    `exists_observerGap9387_832_fourthCarrier_of_repeatCore832Transition_chain4`
    packaging one more overlap as the exact orbit
    `4096*w -> 6912*w -> 11664*w -> 19683*w`
  - local green WIP now also includes the five-step continuation gate
    `exists_observerGap9387_832_fourthCarrier_with_gate_of_repeatCore832Transition_chain5`
    forcing `16 ∣ w` on that fourth carrier
  - local green WIP now also includes the early observer-gap vanishing package
    `observerGap9387_832_eq_zero_of_repeatCore832Transition_chain5` and
    `observerGap9387_832_zero_block_of_repeatCore832Transition_chain5`,
    showing five-step persistence already kills the short observer-gap block
    `σ.src, σ.dst, ρ.dst, ups.dst`
  - local green WIP now also includes the higher-time affine zero-shell
    equivalence
    `observerGap9387_832_eq_zero_of_src_base_eq_864m_add_589` and
    `exists_src_base_eq_864m_add_589_of_observerGap9387_832_eq_zero_of_src_base_mod32_eq13`,
    so on the `(time,eject) = (3,1)` branch with `base ≡ 13 (mod 32)` the zero
    locus of the bounded observer gap is exactly `base = 864*m + 589`
  - local green WIP now also includes the specialized zero-shell transport
    family
    `two_pow_dst_time_sub_four_mul_dst_base_eq_729m_add_497_of_src_base_eq_864m_add_589`,
    its exact parameterizations
    `dst_time_eq_four_add_v2_729m_add_497_of_src_base_eq_864m_add_589` and
    `dst_base_eq_div_pow_v2_729m_add_497_of_src_base_eq_864m_add_589`, and
    the first exact destination-shell ladder through
    `dst_time_eq_four_of_src_base_eq_1728m_add_589`,
    `dst_time_eq_five_of_src_base_eq_3456m_add_1453`,
    `dst_time_eq_six_of_src_base_eq_6912m_add_3181`,
    `seven_le_dst_time_of_src_base_eq_6912m_add_6637`,
    `two_pow_dst_time_sub_seven_mul_dst_base_eq_729m_add_700_of_src_base_eq_6912m_add_6637`,
    `dst_time_eq_seven_of_src_base_eq_13824m_add_13549`, and their
    destination-base companions
  - local green WIP now also includes theorem-level bridge lemmas
    `exists_dst_time4_base_eq_54k_add_11_of_src_base_eq_1728m_add_589`,
    `exists_dst_time5_base_eq_54k_add_19_of_src_base_eq_3456m_add_1453`,
    `exists_dst_time6_base_eq_54k_add_23_of_src_base_eq_6912m_add_3181`, and
    `exists_dst_time7_base_eq_54k_add_25_of_src_base_eq_13824m_add_13549`,
    which reindex the exact zero-shell outputs directly into the established
    `54*k + 11/19/23/25` destination-shell interfaces with explicit affine
    parameter maps
  - local green WIP now also includes the first destination-eject split of
    the zero-shell `time = 4` branch:
    `dst_slice_eq_4_1_of_src_base_eq_3456r_add_2317`,
    `dst_slice_eq_4_2_of_src_base_eq_6912r_add_4045`,
    `dst_slice_eq_4_3_of_src_base_eq_13824r_add_7501`,
    `dst_slice_eq_4_4_of_src_base_eq_27648r_add_14413`, and the residual
    theorem `five_le_dst_eject_of_src_base_eq_55296r_add_589`
  - local green WIP now also includes the next parity handoff of that
    residual:
    `dst_slice_eq_4_6_of_src_base_eq_110592r_add_589` and
    `seven_le_dst_eject_of_src_base_eq_110592r_add_55885`
  - local green WIP now also includes the next exact refinement of that odd
    residual:
    `dst_slice_eq_4_7_of_src_base_eq_221184r_add_55885` and
    `eight_le_dst_eject_of_src_base_eq_221184r_add_166477`
  - local green WIP now also includes the next exact refinement of the
    remaining tail:
    `dst_slice_eq_4_8_of_src_base_eq_442368r_add_387661` and
    `nine_le_dst_eject_of_src_base_eq_442368r_add_166477`
  - local green WIP now also includes the next exact refinement of that
    remaining tail:
    `dst_slice_eq_4_9_of_src_base_eq_884736r_add_608845` and
    `ten_le_dst_eject_of_src_base_eq_884736r_add_166477`
  - local green WIP now also includes the next exact refinement of that
    remaining tail, first as the generic time-4 split
    `dst_slice_eq_4_10_of_src_base_eq_65536r_add_35405` and
    `eleven_le_dst_eject_of_src_base_eq_65536r_add_2637`, and on the
    zero-shell side as
    `dst_slice_eq_4_10_of_src_base_eq_1769472r_add_166477` and
    `eleven_le_dst_eject_of_src_base_eq_1769472r_add_1051213`
  - local green WIP now also includes the next exact refinement of that
    remaining tail, first as the generic time-4 split
    `dst_slice_eq_4_11_of_src_base_eq_131072r_add_68173` and
    `twelve_le_dst_eject_of_src_base_eq_131072r_add_2637`, and on the
    zero-shell side as
    `dst_slice_eq_4_11_of_src_base_eq_3538944r_add_2820685` and
    `twelve_le_dst_eject_of_src_base_eq_3538944r_add_1051213`
  - local green WIP now also includes the next exact refinement of that
    remaining tail, first as the generic time-4 split
    `dst_slice_eq_4_12_of_src_base_eq_262144r_add_133709` and
    `thirteen_le_dst_eject_of_src_base_eq_262144r_add_2637`, and on the
    zero-shell side as
    `dst_slice_eq_4_12_of_src_base_eq_7077888r_add_4590157` and
    `thirteen_le_dst_eject_of_src_base_eq_7077888r_add_1051213`
  - local green WIP now also includes the next exact refinement of that
    remaining tail, first as the generic time-4 split
    `dst_slice_eq_4_13_of_src_base_eq_524288r_add_264781` and
    `fourteen_le_dst_eject_of_src_base_eq_524288r_add_2637`, and on the
    zero-shell side as
    `dst_slice_eq_4_13_of_src_base_eq_14155776r_add_8129101` and
    `fourteen_le_dst_eject_of_src_base_eq_14155776r_add_1051213`
  - these new destination bases are not arbitrary arithmetic byproducts:
    `1458*m + 497`, `1458*m + 613`, `1458*m + 671`, and `1458*m + 1429`
    match the pre-existing higher-time shell residues `11, 19, 23, 25 mod 54`
  - an abandoned shortcut that treated `base = 6912*m + 6637` as a uniform
    `time = 9` case is not part of the verified frontier; the green theorem
    there is only the residual `dst.time ≥ 7` transport law, with exact
    `time = 7` recovered on the odd sub-shell `base = 13824*m + 13549`
  - current source currently matches that green build boundary, so there is
    no newer unverified source delta at this moment
- Resume rule:
  - when chat memory, Rover, and source disagree, trust Lean source plus the
    latest green build boundary
  - when reporting status, name both boundaries explicitly:
    `last green checkpoint` and `current WIP in source`

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
  - on that same higher-time source chart, the source self-threshold defect is
    now packaged intrinsically as
    `regimeIISelfThresholdDefect src = 14*k + 6 - (26*k + 17)/27`
  - that same source chart now also has intrinsic value/radial readouts:
    `src.value = 256*k + 103`,
    `src.radialGap_832 = 256*k - 729`,
    `dst.radialGap_832 = 432*k - 657`
  - combining those two source-side formulas now yields a bounded projective
    source ray on the same higher-time branch:
    `216 * src.selfThresholdDefect =
      11 * src.value + 27 + 8 * ((26*k + 17) % 27)`,
    hence uniformly
    `216 * src.selfThresholdDefect ≤ 11 * src.value + 235`
  - once that same source branch is itself already above `832`, the bounded
    residue package can now be read directly in target-facing radial form:
    `216 * src.selfThresholdDefect =
      11 * src.radialGap_832 + 9179 + 8 * ((26*k + 17) % 27)`,
    hence uniformly
    `216 * src.selfThresholdDefect ≤ 11 * src.radialGap_832 + 9387`
  - the older repeat-core return package now also has an explicit chain-level
    target-facing radial ray theorem on the first true cycle-return state:
    `216 * src.selfThresholdDefect = 11 * src.radialGap_832 + 9387`
    so the newer higher-time branch and the older repeat-core package are now
    provably meeting in the same `832`-radial observer coordinate, not merely
    displaying numerically similar affine behavior
  - the newer higher-time branch now goes one notch beyond that comparison:
    relative to the same shared `9387` observer line, its exact miss is
    itself a bounded finite residue
    `8 * (26 - ((26*k + 17) % 27))`,
    hence the shared line sits at most `208` above the actual branch readout
  - that same comparison is now packaged as an actual source-state coordinate
    `RegimeIIBadFrontierState.observerGap9387_832`:
    it is already exactly `0` on five-step repeat-core persistence and its
    short transported block, and on the higher-time `base ≡ 13 (mod 32)`
    branch above `832` it lies in the finite set `8 * {0, ..., 26}` with zero
    occurring exactly on the affine shell `base = 864*m + 589`, so in
    particular `0 ≤ observerGap ≤ 208`
  - on that exact zero shell, the higher-time transport law is now specialized
    to `2^(dst.time - 4) * dst.base = 729*m + 497`
  - the first green split of that family now yields exact destination shells
    `time = 4, 5, 6, 7` with destination bases
    `1458*m + 497`, `1458*m + 613`, `1458*m + 671`, and `1458*m + 1429`
  - those destination bases line up with the already-verified shell residues
    `11, 19, 23, 25 mod 54`, so the observer-gap zero shell is feeding back
    into the existing higher-time shell tree rather than drifting into a
    disconnected observer-only branch
  - that attachment is now theorem-level, not just interpretive: the new
    bridge lemmas hand the exact `time = 4/5/6/7` zero-shell cases back to
    the established `54*k + 11/19/23/25` families with explicit reindexings
    `k = 27*m + 9`, `27*m + 11`, `27*m + 12`, and `27*m + 26`
  - the zero-shell `time = 4` branch is now also split by destination eject
    through exact slices `(4,1)`, `(4,2)`, `(4,3)`, `(4,4)` and a residual
    family with `dst.eject ≥ 5`, so this branch is entering the same exact
    slice language used elsewhere in the higher-time tree
  - that residual is now split one layer further by parity: the even branch
    lands exactly on the existing `(4,6)` slice, while the odd branch stays
    in the same `time = 4` residual language with `dst.eject ≥ 7`
  - the failed shortcut “`6912*m + 6637` gives uniform `time = 9`” has now
    been explicitly ruled out by the verified residual statement:
    only `dst.time ≥ 7` is green there, and the exact odd sub-shell is
    `base = 13824*m + 13549` with `dst.time = 7`
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
    - the remaining residual shell `base = 140737488355328*r + 104249991374317`
      is now split into its first three exact higher-time cases:
      - `base = 281474976710656*r + 244987479729645` gives `dst.time = 46`
        and `dst.base = 54*r + 47`
      - `base = 562949953421312*r + 385724968084973` gives `dst.time = 47`
        and `dst.base = 54*r + 37`
      - `base = 1125899906842624*r + 104249991374317` gives `dst.time = 48`
        and `dst.base = 54*r + 5`
    - the remaining residual shell `base = 1125899906842624*r + 667199944795629`
      is now split into its first five exact higher-time cases:
      - `base = 2251799813685248*r + 1793099851638253` gives `dst.time = 49`
        and `dst.base = 54*r + 43`
      - `base = 4503599627370496*r + 2918999758480877` gives `dst.time = 50`
        and `dst.base = 54*r + 35`
      - `base = 9007199254740992*r + 5170799572166125` gives `dst.time = 51`
        and `dst.base = 54*r + 31`
      - `base = 18014398509481984*r + 9674399199536621` gives `dst.time = 52`
        and `dst.base = 54*r + 29`
      - `base = 36028797018963968*r + 667199944795629` gives `dst.time = 53`
        and `dst.base = 54*r + 1`
    - the remaining residual shell `base = 36028797018963968*r + 18681598454277613`
      is now split into its first four exact higher-time cases:
      - `base = 72057594037927936*r + 54710395473241581` gives `dst.time = 54`
        and `dst.base = 54*r + 41`
      - `base = 144115188075855872*r + 18681598454277613` gives `dst.time = 55`
        and `dst.base = 54*r + 7`
      - `base = 288230376151711744*r + 90739192492205549` gives `dst.time = 56`
        and `dst.base = 54*r + 17`
      - `base = 576460752303423488*r + 523084756719773165` gives `dst.time = 57`
        and `dst.base = 54*r + 49`
    - the remaining residual shell is now
      `base = 576460752303423488*r + 234854380568061421`
      is now split into its first four exact higher-time cases:
      - `base = 1152921504606846976*r + 234854380568061421` gives
        `dst.time = 58` and `dst.base = 54*r + 11`
      - `base = 2305843009213693952*r + 811315132871484909` gives
        `dst.time = 59` and `dst.base = 54*r + 19`
      - `base = 4611686018427387904*r + 1964236637478331885` gives
        `dst.time = 60` and `dst.base = 54*r + 23`
      - `base = 9223372036854775808*r + 4270079646692025837` gives
        `dst.time = 61` and `dst.base = 54*r + 25`
    - the remaining residual shell is now
      `base = 9223372036854775808*r + 8881765665119413741`
      is now split into its first two exact higher-time cases:
      - `base = 18446744073709551616*r + 18105137701974189549` gives
        `dst.time = 62` and `dst.base = 54*r + 53`
      - `base = 36893488147419103232*r + 8881765665119413741` gives
        `dst.time = 63` and `dst.base = 54*r + 13`
    - the remaining residual shell is now
      `base = 36893488147419103232*r + 27328509738828965357`
      is now split into its first three exact higher-time cases:
      - `base = 73786976294838206464*r + 64221997886248068589` gives
        `dst.time = 64` and `dst.base = 54*r + 47`
      - `base = 147573952589676412928*r + 101115486033667171821` gives
        `dst.time = 65` and `dst.base = 54*r + 37`
      - `base = 295147905179352825856*r + 27328509738828965357` gives
        `dst.time = 66` and `dst.base = 54*r + 5`
    - the remaining residual shell is now
      `base = 295147905179352825856*r + 174902462328505378285`
      is now split into its first five exact higher-time cases:
      - `base = 590295810358705651712*r + 470050367507858204141` gives
        `dst.time = 67` and `dst.base = 54*r + 43`
      - `base = 1180591620717411303424*r + 765198272687211029997` gives
        `dst.time = 68` and `dst.base = 54*r + 35`
      - `base = 2361183241434822606848*r + 1355494083045916681709` gives
        `dst.time = 69` and `dst.base = 54*r + 31`
      - `base = 4722366482869645213696*r + 2536085703763327985133` gives
        `dst.time = 70` and `dst.base = 54*r + 29`
      - `base = 9444732965739290427392*r + 174902462328505378285` gives
        `dst.time = 71` and `dst.base = 54*r + 1`
    - the remaining residual shell is now
      `base = 9444732965739290427392*r + 4897268945198150591981`
      is now split into its first four exact higher-time cases:
      - `base = 18889465931478580854784*r + 14342001910937441019373` gives
        `dst.time = 72` and `dst.base = 54*r + 41`
      - `base = 37778931862957161709568*r + 4897268945198150591981` gives
        `dst.time = 73` and `dst.base = 54*r + 7`
      - `base = 75557863725914323419136*r + 23786734876676731446765` gives
        `dst.time = 74` and `dst.base = 54*r + 17`
      - `base = 151115727451828646838272*r + 137123530465548216575469` gives
        `dst.time = 75` and `dst.base = 54*r + 49`
    - the remaining residual shell is now
      `base = 151115727451828646838272*r + 61565666739633893156333`
      is now split into its first four exact higher-time cases:
      - `base = 302231454903657293676544*r + 61565666739633893156333` gives
        `dst.time = 76` and `dst.base = 54*r + 11`
      - `base = 604462909807314587353088*r + 212681394191462539994605` gives
        `dst.time = 77` and `dst.base = 54*r + 19`
      - `base = 1208925819614629174706176*r + 514912849095119833671149` gives
        `dst.time = 78` and `dst.base = 54*r + 23`
      - `base = 2417851639229258349412352*r + 1119375758902434421024237` gives
        `dst.time = 79` and `dst.base = 54*r + 25`
    - the remaining residual shell is now
      `base = 2417851639229258349412352*r + 2328301578517063595730413`
      is now split into its first two exact higher-time cases:
      - `base = 4835703278458516698824704*r + 4746153217746321945142765` gives
        `dst.time = 80` and `dst.base = 54*r + 53`
      - `base = 9671406556917033397649408*r + 2328301578517063595730413` gives
        `dst.time = 81` and `dst.base = 54*r + 13`
    - the remaining residual shell is now
      `base = 9671406556917033397649408*r + 7164004856975580294555117`
      is now split into its first three exact higher-time cases:
      - `base = 19342813113834066795298816*r + 16835411413892613692204525` gives
        `dst.time = 82` and `dst.base = 54*r + 47`
      - `base = 38685626227668133590597632*r + 26506817970809647089853933` gives
        `dst.time = 83` and `dst.base = 54*r + 37`
      - `base = 77371252455336267181195264*r + 7164004856975580294555117` gives
        `dst.time = 84` and `dst.base = 54*r + 5`
    - the remaining residual shell is now
      `base = 77371252455336267181195264*r + 45849631084643713885152749`
      is now split into its first five exact higher-time cases:
      - `base = 154742504910672534362390528*r + 123220883539979981066348013` gives
        `dst.time = 85` and `dst.base = 54*r + 43`
      - `base = 309485009821345068724781056*r + 200592135995316248247543277` gives
        `dst.time = 86` and `dst.base = 54*r + 35`
      - `base = 618970019642690137449562112*r + 355334640905988782609933805` gives
        `dst.time = 87` and `dst.base = 54*r + 31`
      - `base = 1237940039285380274899124224*r + 664819650727333851334714861` gives
        `dst.time = 88` and `dst.base = 54*r + 29`
      - `base = 2475880078570760549798248448*r + 45849631084643713885152749` gives
        `dst.time = 89` and `dst.base = 54*r + 1`
    - the remaining residual shell is now
      `base = 2475880078570760549798248448*r + 1283789670370023988784276973`
      is now split into its first four exact higher-time cases:
      - `base = 4951760157141521099596496896*r + 3759669748940784538582525421` gives
        `dst.time = 90` and `dst.base = 54*r + 41`
      - `base = 9903520314283042199192993792*r + 1283789670370023988784276973` gives
        `dst.time = 91` and `dst.base = 54*r + 7`
      - `base = 19807040628566084398385987584*r + 6235549827511545088380773869` gives
        `dst.time = 92` and `dst.base = 54*r + 17`
      - `base = 39614081257132168796771975168*r + 35946110770360671685959755245` gives
        `dst.time = 93` and `dst.base = 54*r + 49`
    - the remaining residual shell is now
      `base = 39614081257132168796771975168*r + 16139070141794587287573767661`
      is now split into its first four exact higher-time cases:
      - `base = 79228162514264337593543950336*r + 16139070141794587287573767661` gives
        `dst.time = 94` and `dst.base = 54*r + 11`
      - `base = 158456325028528675187087900672*r + 55753151398926756084345742829` gives
        `dst.time = 95` and `dst.base = 54*r + 19`
      - `base = 316912650057057350374175801344*r + 134981313913191093677889693165` gives
        `dst.time = 96` and `dst.base = 54*r + 23`
      - `base = 633825300114114700748351602688*r + 293437638941719768864977593837` gives
        `dst.time = 97` and `dst.base = 54*r + 25`
    - the remaining residual shell is now
      `base = 633825300114114700748351602688*r + 610350288998777119239153395181`
      - it satisfies `dst.time ≥ 98`
      - it carries the transport law
        `2^(dst.time - 98) * dst.base = 27*r + 26`
      - `base = 1267650600228229401496703205376*r + 1244175589112891819987504997869` gives
        `dst.time = 98` and `dst.base = 54*r + 53`
      - `base = 2535301200456458802993406410752*r + 610350288998777119239153395181` gives
        `dst.time = 99` and `dst.base = 54*r + 13`
    - the remaining residual shell is now
      `base = 2535301200456458802993406410752*r + 1878000889227006520735856600557`
      - it satisfies `dst.time ≥ 100`
      - it carries the transport law
        `2^(dst.time - 100) * dst.base = 27*r + 20`
      - `base = 5070602400912917605986812821504*r + 4413302089683465323729263011309` gives
        `dst.time = 100` and `dst.base = 54*r + 47`
      - `base = 10141204801825835211973625643008*r + 6948603290139924126722669422061` gives
        `dst.time = 101` and `dst.base = 54*r + 37`
      - `base = 20282409603651670423947251286016*r + 1878000889227006520735856600557` gives
        `dst.time = 102` and `dst.base = 54*r + 5`
    - the remaining residual shell is now
      `base = 20282409603651670423947251286016*r + 12019205691052841732709482243565`
      - it satisfies `dst.time ≥ 103`
      - it carries the transport law
        `2^(dst.time - 103) * dst.base = 27*r + 16`
      - `base = 40564819207303340847894502572032*r + 32301615294704512156656733529581` gives
        `dst.time = 103` and `dst.base = 54*r + 43`
      - `base = 81129638414606681695789005144064*r + 52584024898356182580603984815597` gives
        `dst.time = 104` and `dst.base = 54*r + 35`
      - `base = 162259276829213363391578010288128*r + 93148844105659523428498487387629` gives
        `dst.time = 105` and `dst.base = 54*r + 31`
      - `base = 324518553658426726783156020576256*r + 174278482520266205124287492531693` gives
        `dst.time = 106` and `dst.base = 54*r + 29`
      - `base = 649037107316853453566312041152512*r + 12019205691052841732709482243565` gives
        `dst.time = 107` and `dst.base = 54*r + 1`
    - the remaining residual shell is now
      `base = 649037107316853453566312041152512*r + 336537759349479568515865502819821`
      - it satisfies `dst.time ≥ 108`
      - it carries the transport law
        `2^(dst.time - 108) * dst.base = 27*r + 14`
      - `base = 1298074214633706907132624082305024*r + 985574866666333022082177543972333` gives
        `dst.time = 108` and `dst.base = 54*r + 41`
      - `base = 2596148429267413814265248164610048*r + 336537759349479568515865502819821` gives
        `dst.time = 109` and `dst.base = 54*r + 7`
      - `base = 5192296858534827628530496329220096*r + 1634611973983186475648489585124845` gives
        `dst.time = 110` and `dst.base = 54*r + 17`
      - `base = 10384593717069655257060992658440192*r + 9423057261785427918444234078954989` gives
        `dst.time = 111` and `dst.base = 54*r + 49`
    - the remaining residual shell is now
      `base = 10384593717069655257060992658440192*r + 4230760403250600289913737749734893`
      - it satisfies `dst.time ≥ 112`
      - it carries the transport law
        `2^(dst.time - 112) * dst.base = 27*r + 11`
      - `base = 20769187434139310514121985316880384*r + 4230760403250600289913737749734893` gives
        `dst.time = 112` and `dst.base = 54*r + 11`
      - `base = 41538374868278621028243970633760768*r + 14615354120320255546974730408175085` gives
        `dst.time = 113` and `dst.base = 54*r + 19`
      - `base = 83076749736557242056487941267521536*r + 35384541554459566061096715725055469` gives
        `dst.time = 114` and `dst.base = 54*r + 23`
      - `base = 166153499473114484112975882535043072*r + 76922916422738187089340686358816237` gives
        `dst.time = 115` and `dst.base = 54*r + 25`
    - the returned `27*r + 20` transport is now also identified explicitly
      with the earlier verified `time ≥ 28` shell after renormalizing the
      shell parameter by `m ↦ 262144*m + 194180`
    - the returned `27*r + 16` transport is now also identified explicitly
      again with the earlier verified `time ≥ 31` shell after renormalizing
      the shell parameter by `m ↦ 68719476736*m + 40722652880`
    - the returned `27*r + 14` transport is now also identified explicitly
      again with the earlier verified `time ≥ 36` shell after renormalizing
      the shell parameter by `m ↦ 68719476736*m + 35632321270`
    - the returned `27*r + 11` transport is now also identified explicitly
      again with the earlier verified `time ≥ 40` shell after renormalizing
      the shell parameter by `m ↦ 68719476736*m + 27996823855`
    - the returned `27*r + 26` transport is now also identified explicitly
      with the earlier verified `time ≥ 44` shell after renormalizing the
      shell parameter by `m ↦ 262144*m + 252434`
    - the returned `27*r + 26` transport is now also identified explicitly
      again with the earlier verified `time ≥ 44` shell after renormalizing
      the shell parameter by `m ↦ 68719476736*m + 66174310930`
    - the returned `27*r + 20` transport is now also identified explicitly
      again with the earlier verified `time ≥ 28` shell after renormalizing
      the shell parameter by `m ↦ 18014398509481984*m + 13343998895912580`
    - the returned `27*r + 16` transport is now also identified explicitly
      again with the earlier verified `time ≥ 31` shell after renormalizing
      the shell parameter by `m ↦ 18014398509481984*m + 10675199116730064`
    - the returned `27*r + 14` transport is now also identified explicitly
      again with the earlier verified `time ≥ 36` shell after renormalizing
      the shell parameter by `m ↦ 18014398509481984*m + 9340799227138806`
    - the returned `27*r + 11` transport is now also identified explicitly
      again with the earlier verified `time ≥ 40` shell after renormalizing
      the shell parameter by `m ↦ 18014398509481984*m + 7339199392751919`
    - the returned `27*r + 26` transport is now also identified explicitly
      again with the earlier verified `time ≥ 44` shell after renormalizing
      the shell parameter by `m ↦ 18014398509481984*m + 17347198564686354`
    - the returned `27*r + 16` transport is now also identified explicitly
      again with the earlier verified `time ≥ 31` shell after renormalizing
      the shell parameter by `m ↦ 4722366482869645213696*m + 2798439397256086052560`
    - the returned `27*r + 14` transport is now also identified explicitly
      again with the earlier verified `time ≥ 36` shell after renormalizing
      the shell parameter by `m ↦ 4722366482869645213696*m + 2448634472599075295990`
    - the returned `27*r + 11` transport is now also identified explicitly
      again with the earlier verified `time ≥ 40` shell after renormalizing
      the shell parameter by `m ↦ 4722366482869645213696*m + 1923927085613559161135`
    - the remaining residual shell is now
      `base = 166153499473114484112975882535043072*r + 159999666159295429145828627626337773`
      - it satisfies `dst.time ≥ 116`
      - it carries the transport law
        `2^(dst.time - 116) * dst.base = 27*r + 26`
    - the returned `27*r + 26` transport is now also identified explicitly
      again with the earlier verified `time ≥ 44` shell after renormalizing
      the shell parameter by `m ↦ 4722366482869645213696*m + 4547464020541139835410`
      - `base = 332306998946228968225951765070086144*r + 326153165632409913258804510161380845` gives
        `dst.time = 116` and `dst.base = 54*r + 53`
      - `base = 664613997892457936451903530140172288*r + 159999666159295429145828627626337773` gives
        `dst.time = 117` and `dst.base = 54*r + 13`
    - the remaining residual shell is now
      `base = 664613997892457936451903530140172288*r + 492306665105524397371780392696423917`
      - it satisfies `dst.time ≥ 118`
      - it carries the transport law
        `2^(dst.time - 118) * dst.base = 27*r + 20`
    - the returned `27*r + 20` transport is now also identified explicitly
      again with the earlier verified `time ≥ 28` shell after renormalizing
      the shell parameter by `m ↦ 4722366482869645213696*m + 3498049246570107565700`
      - `base = 1329227995784915872903807060280344576*r + 1156920662997982333823683922836596205` gives
        `dst.time = 118` and `dst.base = 54*r + 47`
      - `base = 2658455991569831745807614120560689152*r + 1821534660890440270275587452976768493` gives
        `dst.time = 119` and `dst.base = 54*r + 37`
      - `base = 5316911983139663491615228241121378304*r + 492306665105524397371780392696423917` gives
        `dst.time = 120` and `dst.base = 54*r + 5`
    - the remaining residual shell is now
      `base = 5316911983139663491615228241121378304*r + 3150762656675356143179394513257113069`
      - it satisfies `dst.time ≥ 121`
      - it carries the transport law
        `2^(dst.time - 121) * dst.base = 27*r + 16`
    - the returned `27*r + 16` transport is now also identified explicitly
      again with the earlier verified `time ≥ 31` shell after renormalizing
      the shell parameter by `m ↦ 1237940039285380274899124224*m + 733594097354299422162443984`
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
exit is reduced to an explicit shell ladder through exact `time = 120`, leaving
only one thinner non-self-return residual shell
`base = 5316911983139663491615228241121378304*r + 3150762656675356143179394513257113069`
together with its intrinsic transport law
`2^(dst.time - 121) * dst.base = 27*r + 16`. The
`% 64 = 29` branch remains the only thin self-return branch, while the
non-self-return higher-time side is now almost entirely a finite list of
explicit destination slices. More structurally, the residual transport law has
now run the verified source-state cycle
`27*r + 26 → 27*r + 20 → 27*r + 16 → 27*r + 14 → 27*r + 11 → 27*r + 26 → 27*r + 20 → 27*r + 16 → 27*r + 14 → 27*r + 11 → 27*r + 26 → 27*r + 20 → 27*r + 16 → 27*r + 14 → 27*r + 11 → 27*r + 26 → 27*r + 20 → 27*r + 16 → 27*r + 14 → 27*r + 11 → 27*r + 26 → 27*r + 20 → 27*r + 16`.
The source now contains explicit theorems showing that returned `27*r + 20`,
`27*r + 16`, `27*r + 14`, and `27*r + 11` laws re-enter the earlier
`time ≥ 28`, `time ≥ 31`, `time ≥ 36`, and `time ≥ 40` shells, and that both
earlier and current returned `27*r + 26`, `27*r + 20`, `27*r + 16`, and
`27*r + 14`, and `27*r + 11` stages re-enter the older `time ≥ 44`,
`time ≥ 28`, `time ≥ 31`, `time ≥ 36`, and `time ≥ 40` shells in
renormalized coordinates. This is stronger evidence for a genuine
source-state renormalization cycle rather than an endless stream of novel
higher-time obstructions. The source now also packages those five recurring
return laws as the explicit finite-state wrapper
`VerifiedHigherTimeReturnClock` with cycle
`20 → 16 → 14 → 11 → 26 → 20`, so the “single machine, concurrent all at
once” viewpoint is now represented directly in Lean rather than only inferred
from scattered theorem clusters.

Exploratory interpretation:

- one possible reading of the verified return machine is that the surviving
  higher-time obstruction rotates through finitely many observer-normalized
  leading voices and ejection phases rather than tracing one endlessly novel
  branch
- in that language, different prime-centered observer perspectives might all
  normalize their own leading clock to a local zero while the underlying
  source-state machine keeps rotating globally
- the current Lean source does **not** prove that stronger prime-perspective
  statement; what is proved is the source-state return cycle
  `20 → 16 → 14 → 11 → 26 → 20` together with its exact transport laws
- the current green source now includes a tiny exploratory calibration layer
  `ExploratoryPrimeVoice`; it now includes a candidate canonical
  prime-local state and exact joint signatures for the verified return
  residues, not just isolated examples like “prime `5` as local root”
- the current arithmetic check now says something sharper: the five verified
  return residues do project to definite joint `5/7/11/13` signatures, but
  **not** by a naive phase-only multiplication law on the existing centered
  clocks; shell level or a similar extra coordinate really is part of the
  correct state
- the current Lean source now also proves a first agreement law across those
  concurrent views: after passing to the represented signed value, the
  prime-local views all agree on the same residue, and the verified return
  step adds the same signed delta in each view
- the current Lean source now further decomposes the remaining local update:
  the shell-level move is a threshold-crossing rule on the common next value,
  and the offset correction is then forced by the difference between the old
  and new shell anchors
- the current Lean source now packages that decomposition into explicit update
  objects: `ExploratoryPrimeVoice.predictedLocalUpdate` and
  `ExploratoryPrimeVoice.predictedJointUpdate` reconstruct the full local or
  joint reanchoring step from the current state plus the common next residue
  value, and
  `ExploratoryPrimeVoice.returnJointUpdate_eq_predictedJointUpdate` proves
  that the verified return machine exactly follows that packaged law on the
  five verified return residues
- the current Lean source now also contains a minimal exact test of “local
  return” behavior inside that sampled lift: `ExploratoryPrimeVoice.
  returnAnchorSignature_eq` proves that exact anchor occupancy rotates through
  `p5`, then none, then `p7`, then `p11`, then `p13` along the verified base
  cycle; this supports a rotating local-zero reading in the sampled
  `5/7/11/13` window, but it does **not** yet prove the full claim that every
  prime carries such a return structure
- the current Lean source now also proves the first non-finite structural
  version of that idea inside the exploratory chart:
  `ExploratoryPrimeVoice.canonicalState_eq_anchor_state_of_eq_anchor` shows
  that for any positive `p`, the canonical prime-local coordinate of
  `p * 2^k` is exactly `⟨k, 0⟩`; in this chart, every dyadic shell of a prime
  is an exact local zero for that prime
- the current Lean source now sharpens that further to an exact iff statement:
  `ExploratoryPrimeVoice.atAnchor_canonicalState_iff_exists_eq_anchor` proves
  that a number is exactly at local zero for `p` in the canonical prime chart
  iff it is a dyadic shell `p * 2^k`
- the current Lean source now lifts that exact criterion to the sampled
  `5/7/11/13` joint state itself:
  `ExploratoryPrimeVoice.atAnchor_jointState_p*_iff_exists_eq_anchor`
  identifies exact local zero on each joint-state coordinate with membership
  in that prime’s dyadic shell
- the current Lean source now packages those four coordinatewise shell tests
  into one tuple-level law:
  `ExploratoryPrimeVoice.anchorSignature_jointState_eq_shellSignature`
  identifies the sampled local-zero signature
  `anchorSignature (jointState n)` with the dyadic shell-membership tuple for
  `5/7/11/13`
- treat any “prime voice rotation” reading as a conjectural interpretation to
  test against explicit source-state definitions, not as established theorem
  content

## Best Next Step

The immediate next step is to continue consuming the remaining odd zero-shell
`time = 4` tail inside the existing time-4 eject tree rather than opening
another parallel split tree.

- the current green boundary already reaches the exact zero-shell transport
  family `2^(dst.time - 4) * dst.base = 729*m + 497`, its first exact
  destination shells `time = 4, 5, 6, 7`, and the direct bridge lemmas into
  the `54*k + 11/19/23/25` families
- the structural opportunity is now explicit in source: those bridge lemmas
  hand the zero-shell outputs to the same higher-time shell interfaces that
  the existing slice and exact-zone theorems already know how to consume
- the current green boundary now already includes the exact eject-13 /
  residual eject-`≥ 14` split, so the next proof move should use the residual
  theorem `fourteen_le_dst_eject_of_src_base_eq_14155776r_add_1051213`
  together with the already verified time-4 residual machinery, aiming for an
  exact eject-14 case and a thinner eject-`≥ 15` tail, so the observer-gap
  package keeps re-entering the established shell tree rather than reopening
  fresh arithmetic
- more concretely, the frontier should stay inside the same time-4 eject tree:
  the current green boundary already reaches the exact eject-13 split as the
  generic pair
  `dst_slice_eq_4_13_of_src_base_eq_524288r_add_264781` /
  `fourteen_le_dst_eject_of_src_base_eq_524288r_add_2637` and the zero-shell
  wrappers
  `dst_slice_eq_4_13_of_src_base_eq_14155776r_add_8129101` /
  `fourteen_le_dst_eject_of_src_base_eq_14155776r_add_1051213`; the next live
  tail is the `eject ≥ 14` family on
  `base = 14155776*r + 1051213`
- treat `base = 6912*m + 6637` carefully: the green fact there is only the
  residual law `dst.time ≥ 7` with
  `2^(dst.time - 7) * dst.base = 729*m + 700`; do not revive the discarded
  uniform `time = 9` shortcut
- only after the odd zero-shell `time = 4` residual is exhausted through
  those existing slice interfaces should we split further elsewhere, because
  the main risk now is not missing arithmetic but drifting away from the
  source-state transport structure we have already recovered

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
