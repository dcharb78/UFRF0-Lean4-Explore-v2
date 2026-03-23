# NumerizationSeeds - Arithmetic Seed/Completion Package

## Scope

This note documents the narrow arithmetic sidecar module
[`UFRF/NumerizationSeeds.lean`](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/NumerizationSeeds.lean).

Its role is limited:

- define the shifted triangular arithmetic seed quantity,
- define the triangular completion quantity,
- prove small-factor shielding and completion compositeness,
- connect the specific arithmetic seed at `17` to the already-proved
  fine-structure floor `137`.

This note does **not** promote those facts into residue theorems, projection-law
theorems, or cycle-position identifications.

## Definitions

```lean
def numerizationSeed (n : ℕ) : ℕ := n * (n - 1) / 2 + 1
def numerizationCompletion (n : ℕ) : ℕ := n * (n + 1) / 2
def numerizationEntry (n i : ℕ) : ℕ := n * (n - 1) / 2 + i
```

## Source-Paper Relation

The motivating paper
[`/Users/dcharb/Downloads/preprints202503.0082.v1.pdf`](/Users/dcharb/Downloads/preprints202503.0082.v1.pdf)
defines the first numerization stack by

```text
m = n_i  with  m = n * (n - 1) / 2 + i,  1 ≤ i ≤ n
```

For fixed `n`, the first and last numbers in that stack are therefore

```text
n * (n - 1) / 2 + 1
n * (n + 1) / 2
```

This module records exactly those two arithmetic endpoints as
`numerizationSeed` and `numerizationCompletion`, and it now also records the
general stack-entry formula itself as `numerizationEntry`.

What this module does **not** import from the paper is just as important:

- no alternative prime taxonomy,
- no replacement arithmetic for the repo's standard arithmetic layer,
- no AI/quantum/crypto application claims,
- no promotion of numerization into residue, contour, Allen, or
  `AlphaRunning` semantics.

Interpretation:

- `numerizationSeed` is the shifted triangular arithmetic quantity,
- `numerizationCompletion` is the ordinary triangular arithmetic quantity.

These are arithmetic expressions on naturals, not new cycle-position
definitions.

## Proven Theorems

- `numerizationSeed_not_dvd_three`:
  for every natural `n`, `3` does not divide `numerizationSeed n`.
- `numerizationSeed_not_dvd_five`:
  for every natural `n`, `5` does not divide `numerizationSeed n`.
- `numerizationEntry_one_eq_seed`:
  the first entry in stack `n` is exactly `numerizationSeed n`.
- `numerizationEntry_self_eq_completion`:
  the last valid entry in stack `n` is exactly
  `numerizationCompletion n`.
- `numerizationEntry_mem_stack_interval`:
  if `1 ≤ i ≤ n`, then the paper's entry `numerizationEntry n i` lies between
  the stack seed and stack completion.
- `existsUnique_numerizationEntry`:
  every positive natural `m` belongs to a unique stack `n` with a unique valid
  in-stack index `i`, packaged as a unique pair `(n, i)` satisfying
  `numerizationEntry n i = m`.
- `numerizationCompletion_not_prime`:
  for every `n ≥ 3`, the triangular completion quantity
  `numerizationCompletion n` is not prime.
- `numerizationSeed_seventeen_eq_137`:
  the shifted triangular arithmetic seed at `17` is exactly `137`.
- `alpha_inv_floor_eq_numerizationSeed_seventeen`:
  the existing fine-structure floor theorem matches that same arithmetic seed:
  `⌊ufrf_alpha_inv⌋ = numerizationSeed 17`.

## Proof Shape

The two shielding theorems avoid any analytic or geometric interpretation.
They use a doubled division-free form:

```lean
2 * numerizationSeed (n + 1) = (n + 1) * n + 2
```

From there:

- divisibility by `3` or `5` would force the polynomial `(n + 1) * n + 2`
  to vanish in `ZMod 3` or `ZMod 5`,
- finite case analysis in those rings rules that out.

The stack-entry interval package is simpler:

- `numerizationEntry n 1 = numerizationSeed n`,
- `numerizationEntry n n = numerizationCompletion n`,
- so any entry with `1 ≤ i ≤ n` lies in the closed interval bounded by those
  two endpoints.

The existence/uniqueness theorem adds one more step:

- consecutive completions satisfy
  `numerizationCompletion (n + 1) = numerizationCompletion n + (n + 1)`,
- the previous completion lies strictly below every entry in the next stack,
- so `Nat.find` can choose the first stack whose completion is at least `m`,
  and the resulting index is forced uniquely.

The completion theorem splits by parity:

- if `n = 2k`, then `numerizationCompletion n = k * (2k + 1)`,
- if `n = 2k + 1`, then `numerizationCompletion n = (2k + 1) * (k + 1)`.

For `n ≥ 3`, both factors are distinct from `1`, so the product is not prime.

## Fit With Existing Repo Semantics

This module is intentionally adjacent to, but separate from:

- [`UFRF/PrimeSemantics.lean`](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/PrimeSemantics.lean),
  which distinguishes standard primes, UFRF natural-number primes, and cycle
  positions,
- [`UFRF/FineStructure.lean`](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/FineStructure.lean),
  which proves `⌊ufrf_alpha_inv⌋ = 137`,
- [`UFRF/Phenomena.lean`](/Users/dcharb/Documents/UFRF-Lean-V2/UFRF/Phenomena.lean),
  which packages the chart arithmetic for `137`.

The shared value `137` is recorded only as an arithmetic bridge.
No theorem here identifies numerization seeds with UFRF seed positions.

## Open

- No enrichment-ratio theorem is proved here.
- No Allen / hex bridge theorem is proved here.
- No neural-network dynamical claim is proved here.
- No residue, contour, or projection-law claim is attached to this module.
