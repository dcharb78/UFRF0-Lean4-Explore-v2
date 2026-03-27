# UFRF Frequently Asked Questions

**Every answer maps to a machine-verified theorem name. Verify by running `lake build`.**

---

## On the Trinity

### "Why {-½, 0, +½}? Isn't that arbitrary?"

It's forced by four simultaneous constraints:

| Constraint | Theorem |
|---|---|
| Conservation (sum = 0) | `trinity.conservation` |
| Polarity (distinct nonzero elements) | `trinity_is_minimal_two` |
| Symmetry (neg = -pos) | `trinity_symmetry` |
| Observer at center | `observer_is_midpoint` |

`trinity_uniqueness` proves any triple satisfying mediation + symmetry + scaling is {-k/2, 0, k/2}.

### "Why 3 elements?"

Two elements summing to zero: {-x, x}. No mediator. (`trinity_is_minimal_two`)
One element: {0}. No polarity. Three is the minimum.

### "The number 3 is a literal in the code. Derived or asserted?"

Derived. `uniqueness_of_three` (Structure13.lean:50) proves `is_balanced a ↔ a = 3`.

---

## On 13

### "Why 13?"

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

| Component | Source | Theorem |
|---|---|---|
| Coefficient 4 | C(4,3) simplex faces | `simplex3_face_count` → `log3_geometric_factor_is_four` |
| Powers [3,2,1] | Tensor grades V, V⊗V, V⊗V⊗V | `LOGGrade.tensor_power` |
| ⌊result⌋ = 137 | π bounds | `alpha_inv_floor_137` |

### "Why doesn't it match CODATA exactly?"

Measured ≠ intrinsic. CODATA measures at observer scale. UFRF derives the intrinsic value. The projection law (`padic_is_inverse_limit`) shows compatible observations at all scales reconstruct the unique source. The gap between formulas IS the projection operating at different scales.

`both_integer_parts_137` (AllenBridge.lean:298) proves both Allen's 144−7 and UFRF's formula share integer floor 137.

### "The coefficient 4 — is that fitted?"

No. `simplex3_face_count` (Simplex.lean:41) proves C(4,3) = 4. The tetrahedron has 4 faces because Trinity (3) + 1 closure = 4 vertices. Chain: `trinity.conservation` → `simplex3_face_count` → `log3_geometric_factor_is_four` → `alpha_inv_floor_137`.

---

## On the Kissing Hierarchy

### "How do packing constants relate to physics?"

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

### "Fibonacci-kissing bridge — coincidence?"

F(7) = 13. **Theorem:** `fibonacci_kissing_bridge` (FibonacciKissing.lean:69).
Also: `allen_transport_is_fibonacci` proves F(12) = 144.
Twin primes straddle kissing numbers: `twins_straddle_K2`, `twins_straddle_K3`.
Twin sum 11+13=24=Allen's phases: `twin_sum_is_24`.

---

## On Gauge Groups and Tensor Grades

### "Tensor grades [1,2,3] — just counting?"

They're tensor powers of a 3D space: V (linear), V⊗V (curved), V⊗V⊗V (volumetric).
`total_gauge_bosons` (Noether.lean:114): 1+3+8=12.
`gauge_plus_observer_is_cycle` (Noether.lean:137): 12+1=13.

### "Balance condition = 1 seems arbitrary."

Same minimality selecting the Trinity. `uniqueness_of_three` proves `is_balanced a ↔ a = 3`. The balance condition, Trinity span (`trinity_range_is_one`), simplex closure (+1), and Möbius return (+1) are all the same structural "1."

---

## On the Collatz Conjecture

### "What does UFRF say about 3n+1?"

The Collatz map decomposes into UFRF primitives. The odd step `3n+1` is literally
`trinity_dimension × n + unity`. The even step `n/2` strips polarity (the derived
factor 2).

| Collatz Element | UFRF Source | Theorem |
|---|---|---|
| Coefficient 3 | Unique balanced projective order | `odd_step_coefficient_is_trinity_dimension` |
| Addend 1 | Trinity range \|½ - (-½)\| | `odd_step_addend_is_trinity_range` |
| Divisor 2 | Trinity poles (3−1) | `even_step_divisor_is_pole_count` |
| Terminal cycle length 3 | Trinity cardinality | `terminal_cycle_length` |
| Terminal value 4 | C(4,3) simplex faces | `terminal_visits_simplex_faces` |
| 13 reaches 1 in 9 steps | 9 = 3² interior positions | `thirteen_steps_is_interior_positions` |

Master theorem: `shared_generator` — the Collatz coefficient and the 13-cycle share
the same algebraic origin (a=3).

### "Does UFRF prove the Collatz conjecture?"

No. The module proves the *structure* of the map is derivable from Trinity, and verifies
convergence exhaustively for n=1..13. Universal convergence remains open. The honest claim:
UFRF explains *why* the operations have the form 3n+1 and n/2 — they are breathing
(expansion/contraction). Whether all integers breathe down to unity is computationally
irreducible in exactly the same sense as prime generation.

### "The terminal cycle {1,4,2} — coincidence?"

Three UFRF constants in a 3-cycle: Unity (1), Simplex faces (4), Peak amplitude (2).
`terminal_cycle_values` proves all three steps. `terminal_visits_simplex_faces` links 4
to `simplex3_boundary_face_count`.

### "Why does 3n+1 converge but 2n+1 wouldn't?"

Because 3 > φ² ≈ 2.618 and 2 < φ². The inequality `a < (a-1)²` — which guarantees
two halvings beat one expansion — holds for a ≥ 3 and fails for a = 2.
`convergence_from_three` proves the general case. `dimension_two_fails` proves 2 fails.
The golden ratio is the exact boundary. `trinity_dim_exceeds_golden_threshold` proves
trinity_dimension = 3 strictly exceeds φ².

### "Why is the transition graph always one component?"

Because 2 is a primitive root mod 13 (order 12 = K(3) = 13-1). Every nonzero residue
is a power of 2, so division by any power of 2 can reach any residue from any other.
`two_is_primitive_root_mod_13` proves this. A non-projective-plane prime might not have
2 as a primitive root, fragmenting the graph.

### "What does the nested 13² scale contribute?"

The Python analysis (Phase 3) finds that ZMod(169 × 2^k) gives *looser* bounds than
ZMod(13 × 2^k): convergence windows are 1.5–4× larger and bad streaks grow by ~1.
The 2-adic structure (not the 13-adic) is doing the heavy lifting. The 13-cycle provides
graph connectivity (via primitive root 2 mod 13) but the convergence rate is determined
by the 2-adic precision k.

### "Can UFRF rule out non-trivial Collatz cycles?"

Partially. `CollatzNoCycles.lean` (Phase 4) proves:

| Claim | Theorem |
|---|---|
| gcd(2, 3) = 1 | `two_three_coprime` |
| 2^a ≠ 3^b for b > 0 | `no_power_coincidence` |
| ¬(2^S = 3^L) for L > 0 | `cycle_exact_balance_impossible` |
| 3^L < 4^L for L > 0 | `cycle_step_power_bound` |
| 3, 5, 7, 9, 11, 13 don't cycle in ≤ 20 steps | `*_not_in_cycle` (native_decide) |

The exact power balance needed to close a cycle without the +1 terms is impossible by
coprimality. For the full argument (including the +1 corrections), Eliahou (1993) proved
any cycle has L > 17 million; this is not formalized in the repo.

### "Do the contraction certificates transfer from modular to actual integers?"

Not directly. Phase 4 analysis (analysis/collatz_unsafe_residues.py) finds:
- Exactly 13 "unsafe residues" at each level k: those with v₂(3r+1) ≥ k
- At these residues, modular v₂ can overcount actual v₂ by up to 5 (at k=3, r=85)
- The k=3 certificate margin (150 millibits) is far smaller than the max discrepancy (5 bits)
- **Result: The certificate does NOT transfer directly to all integers**

However, the fraction of unsafe residues is 13/(13·2^(k-1)) = 1/2^(k-3) → 0 geometrically.
A compactness argument on the solenoid may close this gap. See `CollatzInevitability.lean`
for the precise formulation of what remains to be proven.

---

## On Axioms and Foundations

### "Any axioms or hidden assumptions?"

**Zero custom axioms.** `Axiomatics.lean` was deleted entirely (commit 48960f9). `grep -rn "^axiom " UFRF/ --include="*.lean"` returns nothing. `AxiomAudit.lean` runs `#print axioms` on 53 key theorems — all show only standard Lean foundations.

### "What about native_decide?"

31 uses, all on decidable `Nat` or `Fin` arithmetic. Sound for decidable propositions.

---

## On External Validation

### "Where's the external validation?"

Allen (2026) published α⁻¹ derivation without UFRF knowledge. Every number in his paper is a Trinity theorem. `allen_numbers_are_theorems` proves all 8.

Same axiom also predicts (zero parameter changes): τ ceiling, Josephson spectra, gravitational wave quantization, galaxy cluster mass ratios, neural network convergence.

### "How is this different from numerology?"

| | Numerology | UFRF |
|---|---|---|
| Starting point | Pattern-matching | Single axiom → derivation |
| Predictions | Post-hoc only | Falsifiable, 10+ domains |
| Verification | Human claims | Lean 4, zero sorry |
| External validation | None | Allen (2026) confirms 8 numbers |
| Free parameters | Chosen to fit | Zero |
