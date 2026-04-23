import Mathlib.Algebra.Group.Defs

/-!
# Regular Elements and Regular Semigroups

This file defines regular elements and regular semigroups.

## Main Definitions

* `IsRegularElem` — an element `x` is regular if there exists `y` with `x * y * x = x`.
* `IsRegular` — a semigroup is regular if every element is regular.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-- An element `x` is regular if there exists `y` with `x * y * x = x`. -/
def IsRegularElem (x : S) : Prop := ∃ y : S, x * y * x = x

/-- A semigroup is regular if every element is regular. -/
class IsRegular (S : Type*) [Semigroup S] : Prop where
  regular : ∀ x : S, IsRegularElem x

@[simp] lemma IsRegular.isRegularElem [IsRegular S] (x : S) : IsRegularElem x := IsRegular.regular x

end Semigroup
