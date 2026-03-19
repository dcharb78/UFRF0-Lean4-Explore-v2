# PrimeChoreography - Prime Superposition Dynamics

## Overview
The "choreography" of primes on the breathing cycle, showing how primes distribute across the 13 phases.

## Key Definitions

### `ufrf_prime`
```lean
def ufrf_prime (n : ℕ) : Prop :=
  n = 1 ∨ (Nat.Prime n ∧ n ≠ 2)
```

**UFRF Prime Set**: `{1} ∪ {p | prime(p), p ≠ 2}`

This excludes 2 (the only even prime) and includes 1 (the seed).

### `prime_phase`
```lean
def prime_phase (p : ℕ) : ZMod 13 := p
```

Maps a prime to its phase on the cycle.

---

## Proven Theorems

### **Theorem: One is UFRF Prime**
```lean
theorem one_is_ufrf_prime : 
    ufrf_prime 1
```
**Proof**: `rfl`

**Significance**: In UFRF, 1 is considered "prime" because it's the Seed—the starting point of all cycles.

---

### **Theorem: Two is Not UFRF Prime**
```lean
theorem two_is_not_ufrf_prime : 
    ¬ ufrf_prime 2
```
**Proof**: Case analysis.

**Significance**: 2 is excluded because it's the only even prime—it breaks the symmetry of the odd primes.

---

### **Theorem: Odd Standard Primes are UFRF Primes**
```lean
theorem odd_primes_are_ufrf_primes (p : ℕ) 
    (hp : Nat.Prime p) (hodd : p ≠ 2) :
    ufrf_prime p
```
**Proof**: Direct from definition.

**Significance**: Every standard prime other than `2` is UFRF-prime.

---

## Superposition Engine

The `superposition` function computes the collective waveform of all primes up to a given bound:

```lean
noncomputable def superposition (n_max : ℕ) (t : ℝ) : ℝ :=
  (Finset.range n_max).sum (λ p => 
    if ufrf_prime p then waveform ((t + p) % 13) else 0)
```

This shows how primes "interfere" with each other on the breathing cycle, creating patterns in the prime distribution.
