import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.Tactic

/-!
# Ideal Structure for Semigroups

This file defines left, right, and two-sided ideals, as well as minimal ideals.

## Main Definitions

* `LeftIdeal α` — a subset of a magma closed under left multiplication.
* `RightIdeal α` — a subset of a magma closed under right multiplication.
* `MulTwoSidedIdeal α` — a two-sided ideal:
  a subset closed under both left and right multiplication.
* `LeftIdeal.ofSet`, `RightIdeal.ofSet`, `MulTwoSidedIdeal.ofSet` —
  the smallest ideal containing a set.
* `LeftIdeal.principal`, `RightIdeal.principal`, `MulTwoSidedIdeal.principal` — principal ideals.
* `MulTwoSidedIdeal.IsMinimal` — an ideal is minimal if it is
  nonempty and has no proper nonempty sub-ideal.

## Notation
- `⊤, ∅ or {} : MulTwoSidedIdeal α` refer to the full and empty ideals, respectively.
- Given `[MulZeroClass α]`, `⊥` represents the left/right/two-sided ideal `{0}`

For `p, q : MulTwoSidedIdeal α`:
- `p ∩ q : MulTwoSidedIdeal α` denotes their intersection.
- `p ≤ q` is notation for `(p : Set α) ⊆ (q : Set α)`

## Implementation notes
The `SetLike` implementation is from the template in the docstring of `Mathlib.Data.Setlike.Basic`.

For a `p : MulTwoSidedIdeal α` and `x : α`, the notation `x ∈ (p : Set α)` is preferred
over `x ∈ p.carrier` and this is supported by tagging the `mem_carrier` lemmas with `@[simp]`.

For principal ideals, use `MulTwoSidedIdeal.ofSet {x}`.
-/

open Pointwise

/-! ## Left Ideals -/

/-- A left ideal of a magma is a subset closed under left multiplication. -/
structure LeftIdeal (α : Type*) [Mul α] where
  carrier : Set α
  mul_mem_mem {x : α} (hin : x ∈ carrier) (y : α) : y * x ∈ carrier

namespace LeftIdeal

variable {α : Type*} [Mul α] {x y : α}

instance : EmptyCollection (LeftIdeal α) where
  emptyCollection := ⟨∅, by simp⟩

instance : Top (LeftIdeal α) where
  top := ⟨Set.univ, fun _ _ => Set.mem_univ _⟩

instance : SetLike (LeftIdeal α) α :=
  ⟨LeftIdeal.carrier, fun p q h => by cases p; cases q; congr⟩

instance : PartialOrder (LeftIdeal α) := PartialOrder.ofSetLike _ _

@[simp] lemma mem_carrier {p : LeftIdeal α} : x ∈ p.carrier ↔ x ∈ (p : Set α) := Iff.rfl

@[ext] theorem ext {p q : LeftIdeal α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

@[simp] lemma mem_top {x : α} : x ∈ (⊤ : LeftIdeal α) := Set.mem_univ x

@[simp] lemma mem {p : LeftIdeal α} (hin : x ∈ p) : y * x ∈ p := p.mul_mem_mem hin y

variable {S : Type*} [Semigroup S]

/-- The smallest left ideal containing a given set. -/
def ofSet (p : Set S) : LeftIdeal S where
  carrier := Set.univ * p ∪ p
  mul_mem_mem := by
    intro x hx y
    simp only [Set.mem_union, Set.mem_mul] at *
    left; rcases hx with ⟨w, _, v, hv, rfl⟩ | hin
    · exact ⟨y * w, Set.mem_univ _, v, hv, mul_assoc _ _ _⟩
    · exact ⟨y, Set.mem_univ _, x, hin, rfl⟩

@[simp] lemma ofSet_coe (p : Set S) : ↑(ofSet p) = Set.univ * p ∪ p := rfl

@[simp] lemma mem_ofSet (p : Set S) (x : S) : x ∈ (ofSet p) ↔ x ∈ Set.univ * p ∪ p := by rfl

end LeftIdeal

/-! ## Right Ideals -/

/-- A right ideal of a magma is a subset closed under right multiplication. -/
structure RightIdeal (α : Type*) [Mul α] where
  carrier : Set α
  mem_mul_mem {x : α} (hin : x ∈ carrier) (y : α) : x * y ∈ carrier

namespace RightIdeal

variable {α : Type*} [Mul α] {x y : α}

instance : EmptyCollection (RightIdeal α) where
  emptyCollection := ⟨∅, by simp⟩

instance : Top (RightIdeal α) where
  top := ⟨Set.univ, fun _ _ => Set.mem_univ _⟩

instance : SetLike (RightIdeal α) α :=
  ⟨RightIdeal.carrier, fun p q h => by cases p; cases q; congr⟩

instance : PartialOrder (RightIdeal α) := PartialOrder.ofSetLike _ _

@[simp] lemma mem_carrier {p : RightIdeal α} : x ∈ p.carrier ↔ x ∈ (p : Set α) := Iff.rfl

@[ext] theorem ext {p q : RightIdeal α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

@[simp] lemma mem_top {x : α} : x ∈ (⊤ : RightIdeal α) := Set.mem_univ x

@[simp] lemma mem {p : RightIdeal α} (hin : x ∈ p) : x * y ∈ p := p.mem_mul_mem hin y

variable {S : Type*} [Semigroup S]

/-- The smallest right ideal containing a given set. -/
def ofSet (p : Set S) : RightIdeal S where
  carrier := p * Set.univ ∪ p
  mem_mul_mem := by
    intro x hx y
    simp only [Set.mem_union, Set.mem_mul] at *
    left; rcases hx with ⟨w, hw, v, _, rfl⟩ | hin
    · exact ⟨w, hw, v * y, Set.mem_univ _, (mul_assoc _ _ _).symm⟩
    · exact ⟨x, hin, y, Set.mem_univ _, rfl⟩

@[simp] lemma ofSet_coe (p : Set S) : ↑(ofSet p) = p * Set.univ ∪ p := rfl

@[simp] lemma mem_ofSet (p : Set S) (x : S) : x ∈ (ofSet p) ↔ x ∈ p * Set.univ ∪ p := by rfl

end RightIdeal

/-! ## Two-Sided Ideals -/

/-- A two-sided ideal of a magma is a subset closed under both left and right multiplication. -/
structure MulTwoSidedIdeal (α : Type*) [Mul α] where
  carrier : Set α
  mem_mul_mem {x : α} (hin : x ∈ carrier) (y : α) : x * y ∈ carrier
  mul_mem_mem {x : α} (hin : x ∈ carrier) (y : α) : y * x ∈ carrier

namespace MulTwoSidedIdeal

variable {α : Type*} [Mul α] {x y z : α}

/-- The intersection of two ideals is an ideal. -/
instance : Inter (MulTwoSidedIdeal α) where
  inter p q :=
    { carrier := p.carrier ∩ q.carrier
      mem_mul_mem := fun hx y => ⟨p.mem_mul_mem hx.1 y, q.mem_mul_mem hx.2 y⟩
      mul_mem_mem := fun hx y => ⟨p.mul_mem_mem hx.1 y, q.mul_mem_mem hx.2 y⟩ }

@[simp] lemma inter_coe {p q : MulTwoSidedIdeal α} : ↑(p ∩ q) = ↑p ∩ ↑q := rfl

instance : EmptyCollection (MulTwoSidedIdeal α) where
  emptyCollection :=
    { carrier := ∅
      mem_mul_mem := by simp
      mul_mem_mem := by simp }

instance : Top (MulTwoSidedIdeal α) where
  top :=
    { carrier := Set.univ
      mem_mul_mem := fun _ _ => Set.mem_univ _
      mul_mem_mem := fun _ _ => Set.mem_univ _ }

/-- Forget the right-closure to get a left ideal. -/
def toLeftIdeal (p : MulTwoSidedIdeal α) : LeftIdeal α where
  carrier := p.carrier
  mul_mem_mem := p.mul_mem_mem

/-- Forget the left-closure to get a right ideal. -/
def toRightIdeal (p : MulTwoSidedIdeal α) : RightIdeal α where
  carrier := p.carrier
  mem_mul_mem := p.mem_mul_mem

instance : SetLike (MulTwoSidedIdeal α) α :=
  ⟨MulTwoSidedIdeal.carrier, fun p q h => by cases p; cases q; congr⟩

instance : PartialOrder (MulTwoSidedIdeal α) := PartialOrder.ofSetLike _ _

@[simp] lemma mem_carrier {p : MulTwoSidedIdeal α} : x ∈ p.carrier ↔ x ∈ (p : Set α) := Iff.rfl

@[simp] lemma coe_top : ((⊤ : MulTwoSidedIdeal α) : Set α) = Set.univ := rfl

@[simp] lemma mem_top {x : α} : x ∈ (⊤ : MulTwoSidedIdeal α) := Set.mem_univ x

@[simp] lemma toLeftIdeal_coe (p : MulTwoSidedIdeal α) : ↑(p.toLeftIdeal) = (p : Set α) := rfl
@[simp] lemma toRightIdeal_coe (p : MulTwoSidedIdeal α) : ↑(p.toRightIdeal) = (p : Set α) := rfl

@[ext] theorem ext {p q : MulTwoSidedIdeal α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

@[simp] lemma mem' {p : MulTwoSidedIdeal α} (hin : x ∈ p) : z * x * y ∈ p :=
  p.mem_mul_mem (p.mul_mem_mem hin z) y

@[simp] lemma mul_right_mem {p : MulTwoSidedIdeal α} (hin : x ∈ p) : x * y ∈ p :=
  p.mem_mul_mem hin y

@[simp] lemma mul_left_mem {p : MulTwoSidedIdeal α} (hin : x ∈ p) : y * x ∈ p :=
  p.mul_mem_mem hin y

variable {S : Type*} [Semigroup S]

/-- The smallest two-sided ideal containing a given set. -/
def ofSet (p : Set S) : MulTwoSidedIdeal S where
  carrier := Set.univ * p * Set.univ ∪ LeftIdeal.ofSet p ∪ RightIdeal.ofSet p
  mem_mul_mem := by
    intros x hx y
    simp only [Set.mem_union, Set.mem_mul, LeftIdeal.ofSet_coe, RightIdeal.ofSet_coe] at hx ⊢
    rcases hx with ((htwo | (hleft | heq)) | hright | hin)
    · obtain ⟨a, ⟨b, _, c, hc, rfl⟩, d, _, rfl⟩ := htwo
      exact Or.inl (Or.inl ⟨b * c,
        ⟨b, Set.mem_univ _, c, hc, rfl⟩, d * y, Set.mem_univ _, by group⟩)
    · obtain ⟨a, _, b, hb, rfl⟩ := hleft
      exact Or.inl (Or.inl ⟨a * b, ⟨a, Set.mem_univ _, b, hb, rfl⟩, y, Set.mem_univ _, rfl⟩)
    · exact Or.inr (Or.inl ⟨x, heq, y, Set.mem_univ _, rfl⟩)
    · obtain ⟨a, ha, b, _, rfl⟩ := hright
      exact Or.inr (Or.inl ⟨a, ha, b * y, Set.mem_univ _, by group⟩)
    · exact Or.inr (Or.inl ⟨x, hin, y, Set.mem_univ _, rfl⟩)
  mul_mem_mem := by
    intros x hx y
    simp only [Set.mem_union, Set.mem_mul, LeftIdeal.ofSet_coe, RightIdeal.ofSet_coe] at hx ⊢
    rcases hx with ((htwo | (hleft | heq)) | hright | hin)
    · obtain ⟨a, ⟨b, _, c, hc, rfl⟩, d, _, rfl⟩ := htwo
      exact Or.inl (Or.inl ⟨y * b * c, ⟨y * b, Set.mem_univ _, c, hc, rfl⟩,
        d, Set.mem_univ _, by group⟩)
    · obtain ⟨a, _, b, hb, rfl⟩ := hleft
      exact Or.inl (Or.inr (Or.inl ⟨y * a, Set.mem_univ _, b, hb, by group⟩))
    · exact Or.inl (Or.inr (Or.inl ⟨y, Set.mem_univ _, x, heq, rfl⟩))
    · obtain ⟨a, ha, b, _, rfl⟩ := hright
      exact Or.inl (Or.inl ⟨y * a, ⟨y, Set.mem_univ _, a, ha, rfl⟩, b, Set.mem_univ _, by group⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨y, Set.mem_univ _, x, hin, rfl⟩))

@[simp] lemma ofSet_coe (p : Set S) :
    ((ofSet p) : Set S) =
      Set.univ * p * Set.univ ∪ ↑(LeftIdeal.ofSet p) ∪ ↑(RightIdeal.ofSet p) := rfl

@[simp] lemma mem_ofSet (s : Set S) (x : S) : x ∈ (ofSet s) ↔
    x ∈ (Set.univ * s * Set.univ ∪ (LeftIdeal.ofSet s : Set S) ∪ RightIdeal.ofSet s) := by rfl

/-! ## Minimal Ideals -/

/-- An ideal is minimal if it is nonempty and has no proper nonempty sub-ideal. -/
def IsMinimal (I : MulTwoSidedIdeal α) : Prop :=
  I ≠ ∅ ∧ ∀ (J : MulTwoSidedIdeal α), J ≠ ∅ → J ≤ I → J = I

/-- An ideal is 0-minimal if it is nonempty, not `{0}`, and every sub-ideal is
either equal or `{0}`. -/
def IsZeroMinimal [MulZeroClass α] (I : MulTwoSidedIdeal α) : Prop :=
  I ≠ ∅ ∧ I.carrier ≠ {0} ∧
    ∀ (J : MulTwoSidedIdeal α), J ≠ ∅ → J ≤ I → (J = I ∨ J.carrier = {0})

@[simp] lemma isMinimal_iff (I : MulTwoSidedIdeal α) :
    I.IsMinimal ↔ I ≠ ∅ ∧ ∀ (J : MulTwoSidedIdeal α), J ≠ ∅ → J ≤ I → J = I := Iff.rfl

@[simp] lemma isZeroMinimal_iff [MulZeroClass α] (I : MulTwoSidedIdeal α) :
    I.IsZeroMinimal ↔ I ≠ ∅ ∧ I.carrier ≠ {0} ∧
      ∀ (J : MulTwoSidedIdeal α), J ≠ ∅ → J ≤ I → (J = I ∨ J.carrier = {0}) := Iff.rfl

end MulTwoSidedIdeal
