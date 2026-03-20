# UFRF Frequently Asked Questions

**Use these labels literally when they appear in this file.**

- `Theorem`: a machine-verified Lean statement, cited by exact theorem name.
- `Definition`: formal setup or naming in the current repo.
- `Interpretation`: reviewer-facing explanation, not itself a theorem.
- `Open`: an intended direction, comparison, or unproved claim.

When there is any mismatch, the Lean source and the cited theorem names are canonical.

---

## On the Trinity

### "Why {-½, 0, +½}? Isn't that arbitrary?"

Theorem:

It's forced by four simultaneous constraints:

| Constraint | Theorem |
|---|---|
| Conservation (sum = 0) | `trinity.conservation` |
| Polarity (distinct nonzero elements) | `trinity_is_minimal_two` |
| Symmetry (neg = -pos) | `trinity_symmetry` |
| Observer at center | `observer_is_midpoint` |

`trinity_uniqueness` proves any triple satisfying mediation + symmetry + scaling is {-k/2, 0, k/2}.

### "Why 3 elements?"

Theorem:
`trinity_is_minimal_two` rules out the two-element case as lacking a mediator.
The one-element case `{0}` has no polarity.

Interpretation:
So three is presented as the minimal structure carrying conservation, polarity,
and mediation together.

### "The number 3 is a literal in the code. Derived or asserted?"

Theorem:
`uniqueness_of_three` (Structure13.lean:50) proves `is_balanced a ↔ a = 3`.

---

## On 13

### "Why 13?"

Theorem:

Four independent routes, same answer:

| Route | Theorem |
|---|---|
| Projective plane: 3²+3+1=13 | `uniqueness_of_thirteen` |
| Dimensional closure: 3×(3+1)+1=13 | `dimensional_closure_equivalent` |
| Kissing + center: K(3)+1=13 | `kissing_plus_center_is_cycle` |
| Gauge + observer: 12+1=13 | `gauge_plus_observer_is_cycle` |

### "What about the flip at 6.5?"

6.5/13 = 1/2. **Theorem:** `flip_at_half` (BreathingCycle.lean:166).

---

## On the Fine-Structure Constant

### "Where does 4π³+π²+π come from?"

Theorem:

| Component | Source | Theorem |
|---|---|---|
| Coefficient 4 | C(4,3) simplex faces | `simplex3_face_count` → `log3_geometric_factor_is_four` |
| Powers [3,2,1] | Tensor grades V, V⊗V, V⊗V⊗V | `LOGGrade.tensor_power` |
| ⌊result⌋ = 137 | π bounds | `alpha_inv_floor_137` |

### "Why doesn't it match CODATA exactly?"

Theorem:
`both_integer_parts_137` (AllenBridge.lean:298) proves both Allen's `144 - 7`
expression and UFRF's `4π³ + π² + π` expression share integer floor `137`.

Interpretation:
The repo treats `4π³ + π² + π` as the intrinsic closed-form expression and
CODATA values as measurement-side data. The explanatory projection-language
comparison here is reviewer-facing narrative, not a separate formal theorem
identifying the two expressions as the same measured quantity.

Open:
A precise formal bridge from the intrinsic expression to external measurement
conventions is not part of the current Lean proof surface.

### "The coefficient 4 — is that fitted?"

Theorem:
`simplex3_face_count` (Simplex.lean:41) proves `C(4,3) = 4`, and
`log3_geometric_factor_is_four` promotes that coefficient into the current
fine-structure derivation chain ending at `alpha_inv_floor_137`.

Interpretation:
The repo presents the coefficient `4` as derived from the current simplex and
closure layer, not as a fit parameter chosen after the fact.

---

## On the Kissing Hierarchy

### "How do packing constants relate to physics?"

Theorem:

| Allen's Number | Formula | Theorem |
|---|---|---|
| 6 faces | K(2) | `allen_faces_are_kissing_2d` |
| 7 modes | K(2)+1 | `allen_flip_from_kissing` |
| 42 boundary | K(2)×(K(2)+1) | `allen_boundary_from_kissing` |
| 24 phases | 2×K(3) | `allen_phases_from_kissing` |
| 144 states | K(3)² | `allen_states_from_kissing` |
| 137 floor | K(3)²-(K(2)+1) | `alpha_floor_from_kissing` |
| 96 closure | 2×K(3)×C(4,3) | `allen_closure_from_kissing` |
| 25=5² curvature | (K(3)+1)²-K(3)² | `curvature_5_from_kissing` |

Master theorem: `allen_numbers_are_theorems` (KissingHierarchy.lean:264).

Interpretation:
The repo proves the displayed numeric identities. Any further physical reading
of those identities is reviewer-facing interpretation, not an additional theorem
stating that the physical model itself is established by this table alone.

### "Fibonacci-kissing bridge — coincidence?"

Theorem:
`fibonacci_kissing_bridge` (FibonacciKissing.lean:69) proves `F(7) = 13`.
Also: `allen_transport_is_fibonacci` proves `F(12) = 144`,
`twins_straddle_K2` and `twins_straddle_K3` prove the displayed twin-prime
straddling facts, and `twin_sum_is_24` proves the `11 + 13 = 24` identity.

Interpretation:
The repo proves these arithmetic bridges directly. Whether one describes that
overlap as “coincidence” or “structure” is explanatory language, not an extra
theorem beyond the cited identities.

---

## On Gauge Groups and Tensor Grades

### "Tensor grades [1,2,3] — just counting?"

Definition:
The three grades are presented as tensor levels of a 3D space:
`V`, `V ⊗ V`, and `V ⊗ V ⊗ V`.

Theorem:
`total_gauge_bosons` (Noether.lean:114) proves the displayed `1 + 3 + 8 = 12`
count, and `gauge_plus_observer_is_cycle` (Noether.lean:137) proves the
resulting `12 + 1 = 13` cycle identity.

Interpretation:
So the current repo does not treat `[1,2,3]` as free counting labels; it uses
them as the organizational grades behind the displayed theorem chain.

### "Balance condition = 1 seems arbitrary."

Theorem:
`uniqueness_of_three` proves `is_balanced a ↔ a = 3`, and
`trinity_range_is_one` identifies the Trinity span with `1`.

Interpretation:
The FAQ's point is that the recurring `1` is treated as a structural closure
feature of the current framework, not as an independently chosen extra
constant.

---

## On Axioms and Foundations

### "Any axioms or hidden assumptions?"

Current verification status:
the current `UFRF/*.lean` source declares no custom axioms.
`AxiomAudit.lean` records `#print axioms` output for key theorems, and the
current audit surface shows only standard Lean foundations.

### "What about native_decide?"

Current verification status:
the current repo uses `native_decide` on decidable `Nat` or `Fin` arithmetic
checks. This answer is reporting the present audit state of the codebase, not a
separate standalone theorem.

---

## On the Residue / Contour Slice

### "What is actually proved about residues right now?"

Definition:
`ResidueDefinition.lean` fixes a concrete analytic slice for the single function
`breathingFunction = 1 / (z^13 - 1)` together with the explicit pole data
`breathingRoot` and `residueCandidateAt`. This is not a generic residue API.

Theorem:
`CircleIntegralBreathing.lean` proves concrete contour formulas for that specific
function. Representative results include:

| Scope | Theorem |
|---|---|
| Single local circle | `circleIntegral_breathingFunction_eq_two_pi_I_mul_residueCandidate_of_lt_half_infsep` |
| Boundary-clean outer rectangle | `boundaryRectIntegral_breathingFunction_eq_two_pi_I_mul_sum_residueCandidate_of_no_boundary_roots` |
| Large centered square (`R > 1`) | `boundaryRectIntegral_breathingFunction_eq_zero_of_one_lt_centeredSquare` |
| Large enclosing rectangle | `boundaryRectIntegral_breathingFunction_eq_zero_of_encloses_unitSquare` |

For a compact theorem inventory, see
[`docs/proofs/25_ResidueContourSlice.md`](/Users/dcharb/Documents/UFRF-Lean-V2/docs/proofs/25_ResidueContourSlice.md).

Interpretation:
The current formal result is that contour integrals of the specific function
`1 / (z^13 - 1)` can be computed from explicit local residue candidates at the
13 breathing roots, for the concrete circle and rectangle regimes formalized in
`CircleIntegralBreathing.lean`.

Open:
The repo does not yet prove a generic residue theorem, a general Laurent-series
interface, a monodromy package, or any claim that a projection law is itself a
complex-analytic residue theorem. Those would require additional infrastructure
and separate proofs.

---

## On External Validation

### "Where's the external validation?"

Theorem:
`allen_numbers_are_theorems` proves the Allen-number equalities formalized in
the current repo.

Interpretation:
Allen (2026) is external historical context, not part of the Lean proof layer.
The reviewer-facing point is that published numeric claims overlap with the
repo's existing theorem set.

Open:
Broader claims about `τ` ceiling, Josephson spectra, gravitational-wave
quantization, galaxy-cluster mass ratios, or neural-network convergence are
not part of the current cited Lean proof surface unless they are tied to separate
cited theorems elsewhere in the repo.

### "How is this different from numerology?"

Interpretation:

| | Numerology | UFRF |
|---|---|---|
| Starting point | Pattern-matching | Single axiom → derivation |
| Predictions | Post-hoc only | Falsifiable, 10+ domains |
| Verification | Human claims | Lean 4, zero sorry |
| External validation | None | Allen (2026) confirms 8 numbers |
| Free parameters | Chosen to fit | Zero |

Open:
Claims about falsifiability or external confirmation should always be read
alongside the cited theorem surface and the separate reviewer fence, not as a
standalone proof artifact.
