# Semigroup

A Lean 4 formalization of finite semigroup theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4). This library develops the structural theory of semigroups: Green's relations, ideals, simple semigroups, substructures, and the Rees–Suschkewitsch classification theorem.

## Overview

The central objects of study are finite semigroups and their internal structure, with an emphasis on the five **Green's relations** (𝓡, 𝓛, 𝓙, 𝓗, 𝓓) and the representation theory of simple and 0-simple semigroups via Rees matrix constructions.

**Highlights:**
- Full definitions and basic theory of all five Green's relations
- Green's Lemma (bijections between 𝓡- and 𝓛-classes)
- The Location Theorem and group structure on H-classes of idempotents
- The **D-J Theorem**: in finite semigroups, 𝓓 = 𝓙
- The **Rees–Suschkewitsch Theorem**: finite simple semigroups are exactly Rees matrix semigroups over groups
- Ideal theory and its relationship to Green's 𝓙-order
- Exponentiation for semigroups (with positive natural number exponents)
- Idempotent powers: every element of a finite semigroup has an idempotent power

## Repository Structure

```
Semigroup.lean              -- Top-level imports
Semigroup/
  Power.lean                -- Exponentiation for semigroups (Pow S ℕ+)
  Idempotent.lean           -- Idempotent elements; every element has an idempotent power
  Regular.lean              -- Regular elements and regular semigroups
  Simple.lean               -- Simple and 0-simple semigroups
  Substructure.lean         -- Subsemigroups, submonoids, subgroups
  Greens/
    Defs.lean               -- Definitions of 𝓡, 𝓛, 𝓙, 𝓗, 𝓓
    Basic.lean              -- Basic lemmas; morphism preservation
    Finite.lean             -- D-J Theorem (𝓓 = 𝓙 in finite semigroups)
    Lemma.lean              -- Green's Lemma (bijections between classes)
    Location.lean           -- Location Theorem; H-class subgroup structure
  Ideal/
    Defs.lean               -- Left, right, and two-sided ideals
    Basic.lean              -- Basic ideal lemmas
    Green.lean              -- Ideals and Green's 𝓙-order
    Quotient.lean           -- Rees quotients
  ReesMatrix/
    Defs.lean               -- Rees matrix semigroups (with and without zero)
    Simple.lean             -- Rees–Suschkewitsch Theorem (simple case)
    ZeroSimple.lean         -- Rees–Suschkewitsch Theorem (0-simple case, partial)
```
