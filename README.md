# Semigroup

A Lean 4 formalization of finite semigroup theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4). This library develops the structural theory of semigroups: Green's relations, ideals, simple semigroups, substructures, and the Rees–Suschkewitsch classification theorem.

## Repository Structure

```
Semigroup.lean              -- Top-level imports
Semigroup/
  SemigroupIdempotentPow.lean -- Idempotent elements; every element has an idempotent power
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
