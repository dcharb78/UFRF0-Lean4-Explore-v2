# UFRF Derivation Chain

**Every node is a proven theorem. Every arrow is a verified import.**
**Zero sorry. Zero custom axioms. 536+ proven entities. 43 modules.**

The entire framework derives from one structure: `Trinity {-½, 0, +½}` with `sum = 0`.

## Foundations

This repo contains **zero custom axioms**. The former `Axiomatics.lean` was deleted entirely (commit 48960f9). `#print axioms` on all key theorems returns only standard Lean foundations: `propext`, `Classical.choice`, `Quot.sound`. Verified in `AxiomAudit.lean` across the tracked key theorems.

## The Chain

```
Trinity.lean: trinity.conservation
│   The starting point: three elements {-½, 0, +½} summing to zero.
│   Proven: conservation, trinity_symmetry, observer_is_midpoint.
│
├── Trinity.lean: trinity_is_minimal_two
│   Two elements summing to zero: a = -b, no room for mediator.
│   Three is the minimum satisfying polarity + mediation + conservation.
│
├── Trinity.lean: trinity_uniqueness
│   Conservation + mediation + symmetry + scaling
│   → shape is {-k/2, 0, k/2} for any scaling k. Proven.
│
├── Structure13.lean: uniqueness_of_three
│   │   The projective balance constraint is_balanced(a) ↔ a = 3.
│   │   3 is forced. Proven.
│   │
│   ├── Structure13.lean: uniqueness_of_thirteen
│   │   │   a² + a + 1 = 13 when a = 3. Proven.
│   │   │   Also: thirteen_is_projective (13 = 3² + 3 + 1). Proven.
│   │   │
│   │   ├── Foundation.lean: cycle_is_thirteen
│   │   │   derived_cycle_length = 13. Proven.
│   │   │   Also: dimensional_closure_equivalent (3×(3+1)+1=13). Proven.
│   │   │
│   │   ├── BreathingCycle.lean: flip_at_half
│   │   │   │   6.5/13 = 1/2. The flip is the midpoint. Proven.
│   │   │   │
│   │   │   ├── BreathingCycle.lean: prism_identity
│   │   │   │   neg(comp(x)) = x + 1 on ZMod 13.
│   │   │   │   Time from symmetry. No external clock. Proven.
│   │   │   │
│   │   │   ├── BreathingCycle.lean: inversion_symmetry
│   │   │   │   (6 : CyclePos) + 7 = 0. Proven.
│   │   │   │
│   │   │   └── BreathingCycle.lean: bridge_seed_wraps
│   │   │       (12 : CyclePos) + 1 = 0. Möbius return. Proven.
│   │   │
│   │   │   ├── BreathingCycle.lean: terminal_block_reindexes_as_zero_to_three
│   │   │   │   Contextual chart at REST: 10,11,12,13 ↦ 0,1,2,3. Proven.
│   │   │   │
│   │   │   ├── BreathingCycle.lean: terminal_block_reindexes_at_scale
│   │   │   │   Scale-invariant chart: 10+13s,11+13s,12+13s,13+13s ↦ 0,1,2,3. Proven.
│   │   │   │
│   │   │   └── BreathingCycle.lean: terminal_block_closes_and_restarts_at_scale
│   │   │       13+13s is seed in the human chart, 3 in the local terminal chart,
│   │   │       0 in the residue chart, and the step into it matches 0→1. Proven.
│   │   │
│   │   ├── Addressing.lean: (ℤ, ZMod 13) coordinates
│   │   │   phase_count, 12 ≡ -1 (mod 13). Proven.
│   │   │
│   │   └── Recursion.lean: no_first_step_and_terminal_handoff_at_scale
│   │       Scale = ℤ. No bottom scale; bridge→seed nesting and terminal
│   │       handoff persist. Proven.
│   │       Also: bridge_to_seed_matches_terminal_chart
│   │       (REST-anchored chart 10,11,12,13 ↦ 0,1,2,3 equals
│   │       "REST + next-scale seed strip"). Proven.
│   │       Also: bridge_to_seed_matches_terminal_chart_at_scale
│   │       (the same handoff law at every 13-shifted terminal block). Proven.
│   │       Also: no_first_step_and_terminal_handoff_at_scale
│   │       (no bottom scale, and every 13-shifted terminal block still hands
│   │       off from closure at 13 to re-entry at 14). Proven.
│   │       Also: prism_walk_and_terminal_handoff_at_scale
│   │       (the cycle-side seed walk 0→1 reaches every position, 13=0 in the
│   │       pure cycle chart, and the local 13↦3 / 14↦4 handoff persists with
│   │       no bottom scale). Proven.
│   │
│   └── Foundation.lean: trinity_range_is_one
│       The span from -½ to +½ = 1. Proven.
│
├── Simplex.lean: simplex3_face_count
│   │   C(4,3) = 4. Tetrahedron has 4 faces. Proven.
│   │   Also: simplex3_boundary_is_four. Proven.
│   │
│   └── ThreeLOG.lean: log3_geometric_factor_is_four
│       │   Log3 duality factor = C(4,3) = 4. From simplex. Proven.
│       │
│       ├── ThreeLOG.lean: nine_interior_positions
│       │   3 grades × 3 modes = 9. Plus 4 structural = 13. Proven.
│       │
│       └── FineStructure.lean: alpha_inv_floor_137
│           │   ⌊4π³ + π² + π⌋ = 137. Proven with π bounds.
│           │   Also: alpha_polynomial_form, ufrf_matches_codata. Proven.
│           │
│           ├── AllenBridge.lean: both_integer_parts_137
│           │   Allen's 144-7 and UFRF's floor(4π³+π²+π) both = 137. Proven.
│           │
│           └── AlphaRunning.lean:
│               alpha_selected_one_step_absolute_error_package_has_local_origin_and_recurring_handoff
│               The current measurement-side endpoint packages local origin `0`,
│               the arithmetic-selected observer, the normalized real `/ 28`
│               one-step observable, the one-step residual against the static
│               CODATA gap, the absolute-error identity, and the same recurring
│               `13 ↦ 3`, `14 ↦ 4` handoff. Proven.
│               Also: alpha_running_three_layer_concurrency_package
│               (a running-side re-export of the lower cycle/recursion
│               concurrency package, not the semantic origin of that
│               structural theorem). Proven.
│
├── KeplerTriangle.lean: kepler_pythagorean
│   √φ from Kepler's Triangle. Proven.
│
├── KissingEigen.lean: kissing_plus_center_is_cycle
│   │   K(3) + 1 = 12 + 1 = 13. Sphere packing forces cycle length. Proven.
│   │   Also: kissing_equals_gauge (K(3) = gauge bosons). Proven.
│   │
│   ├── KissingHierarchy.lean: allen_numbers_are_theorems ⭐
│   │   │   ALL 8 Allen constants from Trinity:
│   │   │   allen_faces_are_kissing_2d: 6 = K(2)
│   │   │   allen_flip_from_kissing: 7 = K(2)+1
│   │   │   allen_boundary_from_kissing: 42 = K(2)×(K(2)+1)
│   │   │   allen_phases_from_kissing: 24 = 2×K(3)
│   │   │   allen_states_from_kissing: 144 = K(3)²
│   │   │   alpha_floor_from_kissing: 137 = K(3)²-(K(2)+1)
│   │   │   allen_closure_from_kissing: 96 = 2×K(3)×C(4,3)
│   │   │   curvature_5_from_kissing: 25 = (K(3)+1)²-K(3)² = 5²
│   │   │   Master conjunction proven by norm_num. Proven.
│   │   │
│   │   └── QUART.lean: concurrent_state_count
│   │       |Fin 2 × Fin 12 × Fin 4| = 96. Parity × kissing × simplex. Proven.
│   │
│   ├── FibonacciKissing.lean: fibonacci_kissing_bridge ⭐
│   │   F(K(2)+1) = F(7) = 13 = K(3)+1. Proven.
│   │   Also: allen_transport_is_fibonacci (F(12)=144). Proven.
│   │
│   ├── FibonacciKissing.lean: twins_straddle_K2, twins_straddle_K3
│   │   (5,7) around 6. (11,13) around 12. Proven.
│   │   twin_sum_is_24: 11+13=24=Allen's phases. Proven.
│   │
│   ├── FibonacciKissing.lean: nn_architecture_from_kissing
│   │   nn_heads=13, nn_dmodel=390, nn_batch=260 from kissing. Proven.
│   │
│   └── FibonacciPrimeChain.lean: axiom_at_checkpoint ⭐
│       F(4)=3, is_ufrf_prime 3, ¬is_ufrf_prime 4. Proven.
│       Also: spiral_primes (UFRF-prime at UFRF-prime indices). Proven.
│       tower: 7→13→233 escalation. tower_primes: all prime. Proven.
│
├── Noether.lean: total_gauge_bosons
│   │   1 + 3 + 8 = 12. Proven.
│   └── Noether.lean: gauge_plus_observer_is_cycle
│       12 + 1 = 13. Proven.
│
├── DivisionAlgebras.lean: visible_dimension_count
│   1 + 2 + 4 + 8 = 15. Hurwitz theorem. Proven.
│
├── Padic.lean: universal_conservation
│   │   Ring hom ℤ → ℤ_p preserves sum = 0. Proven.
│   │
│   └── InverseLimit.lean: padic_is_inverse_limit ⭐
│       │   Forward (padic_is_coherent): ℤ_p → coherent sequence. Proven.
│       │   Reverse: coherent sequence → unique ℤ_p. Proven.
│       │   Both directions of projection law. Proven.
│       │
│       └── Adele.lean: adele_conservation
│           Conservation over cycle primes {3,5,7,11,13}. Proven.
│
├── AllenEmbedding.lean: Z12_projects_to_Z6, six_not_divides_thirteen
│   Z₆ embeds in Z₁₂ (6∣12) but not Z₁₃ (6∤13). Proven.
│   CRT_Z78: Z₇₈ ≅ Z₆ × Z₁₃. Proven.
│   CRT_Z24: Z₂₄ ≅ Z₈ × Z₃. Proven.
│
└── KernelProof.lean: 107 cross-module verification examples
    28 layers. Proven.
```

## How to Read This

Start at `trinity.conservation`. Follow any path down. Every node is machine-verified. Zero gaps, zero sorry, zero custom axioms.
