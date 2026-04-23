import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.Tactic

/-!
# Substructures for semigroups, monoids, and groups (without identity axiom)

This file defines:
* `Semigroup.Subsemigroup` — a subset of a semigroup closed under multiplication.
* `Semigroup.Submonoid` — a subset with a distinguished identity element.
* `Semigroup.Subgroup` — a subset with identity, inverse, and closure axioms.

Along with `SetLike` instances, partial orders, and basic API for each structure.

## Notation
- `≤` : subset ordering on `Subsemigroup/Submonoid/Subgroup` via `SetLike`

## Implementation notes
The `SetLike` implementation follows the template in the docstring of `Mathlib.Data.Setlike.Basic`.
The `Submonoid` and `Subgroup` structures carry their *own* `one` and `inv` rather than
depending on a `Monoid / Group` instance on `S`, making them suitable for semigroup
theory where the ambient type has no global identity.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-! ### Subsemigroup -/

/-- A subsemigroup of a semigroup is a subset closed under multiplication. -/
structure Subsemigroup (S : Type*) [Semigroup S] where
  carrier : Set S
  mul_mem {x y : S} (hx : x ∈ carrier) (hy : y ∈ carrier) : x * y ∈ carrier

namespace Subsemigroup

variable {S : Type*} [Semigroup S]

instance : SetLike (Subsemigroup S) S :=
  ⟨Subsemigroup.carrier, fun p q h => by cases p; cases q; congr⟩

instance : PartialOrder (Subsemigroup S) := PartialOrder.ofSetLike _ _

@[simp] lemma mem_carrier {p : Subsemigroup S} {x : S} : x ∈ p.carrier ↔ x ∈ (p : Set S) :=
  Iff.rfl

@[ext] theorem ext {p q : Subsemigroup S} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

instance (T : Subsemigroup S) : Mul T :=
  ⟨fun a b => ⟨a.1 * b.1, T.mul_mem a.2 b.2⟩⟩

variable {T : Subsemigroup S}

@[simp] theorem coe_mul (x y : T) : (↑(x * y) : S) = ↑x * ↑y := rfl

@[simp] theorem mk_mul_mk (x y : S) (hx : x ∈ T) (hy : y ∈ T) :
    (⟨x, hx⟩ : T) * ⟨y, hy⟩ = ⟨x * y, T.mul_mem hx hy⟩ := rfl

@[simp] theorem mul_def (x y : T) :
    x * y = ⟨x * y, T.mul_mem x.2 y.2⟩ := rfl

instance : Semigroup T where
  mul_assoc _ _ _ := by simp [mul_assoc]

end Subsemigroup

/-! ### Submonoid -/

/-- A submonoid of a semigroup, carrying its own identity element. -/
structure Submonoid (S : Type*) [Semigroup S] extends Subsemigroup S where
  one : S
  one_mem : one ∈ carrier
  one_mul {x : S} (hx : x ∈ carrier) : one * x = x
  mul_one {x : S} (hx : x ∈ carrier) : x * one = x

namespace Submonoid

variable {S : Type*} [Semigroup S]

lemma one_eq {T₁ T₂ : Submonoid S} (h : T₁.carrier = T₂.carrier) : T₁.one = T₂.one := by
  have h₁ : T₁.one ∈ T₂.carrier := h ▸ T₁.one_mem
  have h₂ : T₂.one ∈ T₁.carrier := h ▸ T₂.one_mem
  rw [← T₁.one_mul h₂, T₂.mul_one h₁]

instance : SetLike (Submonoid S) S :=
  ⟨Subsemigroup.carrier ∘ Submonoid.toSubsemigroup, fun T₁ T₂ h => by
    have heq : T₁.carrier = T₂.carrier := by simp_all
    have hone : T₁.one = T₂.one := one_eq heq
    cases T₁; rename Subsemigroup S => T₁'; cases T₁'
    cases T₂; rename Subsemigroup S => T₂'; congr⟩

instance : PartialOrder (Submonoid S) := PartialOrder.ofSetLike _ _

@[simp] lemma mem_carrier {p : Submonoid S} {x : S} : x ∈ p.carrier ↔ x ∈ (p : Set S) :=
  Iff.rfl

@[ext] theorem ext {p q : Submonoid S} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

instance (T : Submonoid S) : Mul T :=
  ⟨fun a b => ⟨a.1 * b.1, T.mul_mem a.2 b.2⟩⟩

variable {T : Submonoid S}

@[simp] theorem coe_mul (x y : T) : (↑(x * y) : S) = ↑x * ↑y := rfl

@[simp] theorem mk_mul_mk (x y : S) (hx : x ∈ T) (hy : y ∈ T) :
    (⟨x, hx⟩ : T) * ⟨y, hy⟩ = ⟨x * y, T.mul_mem hx hy⟩ := rfl

@[simp] theorem mul_def (x y : T) :
    x * y = ⟨x * y, T.mul_mem x.2 y.2⟩ := rfl

instance : Semigroup T where
  mul_assoc _ _ _ := by simp [mul_assoc]

instance : One T where
  one := ⟨T.one, T.one_mem⟩

theorem one_def : (1 : T) = ⟨T.one, T.one_mem⟩ := rfl

@[simp] theorem coe_one : ↑(1 : T) = T.one := rfl

instance : Monoid T where
  one_mul x := Subtype.ext (T.one_mul x.2)
  mul_one x := Subtype.ext (T.mul_one x.2)

end Submonoid

/-! ### Subgroup -/

/-- A subgroup of a semigroup is a subset with a distinguished identity, inverse, and
closure under multiplication. This models "maximal subgroup" without requiring a Group
instance on the ambient type. -/
structure Subgroup (S : Type*) [Semigroup S] extends Submonoid S where
  inv : S → S
  inv_not_mem {x : S} (hx : x ∉ carrier) : inv x = x
  inv_mem {x : S} (hx : x ∈ carrier) : inv x ∈ carrier
  inv_mul {x : S} (hx : x ∈ carrier) : inv x * x = one
  mul_inv {x : S} (hx : x ∈ carrier) : x * inv x = one

namespace Subgroup

variable {S : Type*} [Semigroup S]

lemma one_eq {T₁ T₂ : Subgroup S} (heq : T₁.carrier = T₂.carrier) : T₁.one = T₂.one :=
  Submonoid.one_eq heq

lemma inv_unique' {H : Subgroup S} {x y : S} (hx : x ∈ H.carrier)
    (hy : y ∈ H.carrier) (heq : H.one = x * y) : H.inv y = x := by
  have h₁ := H.inv_mul hy
  rw [heq] at h₁
  have h₂ : H.inv y * y * H.inv y = x * (y * H.inv y) := by
    rw [h₁]; simp [mul_assoc]
  rw [H.inv_mul hy, H.mul_inv hy, H.one_mul, H.mul_one] at h₂
  · exact h₂
  · exact hx
  · exact H.inv_mem hy

lemma inv_unique {H : Subgroup S} {x y : S} (hx : x ∈ H.carrier)
    (hy : y ∈ H.carrier) (heq : H.one = x * y) : H.inv x = y := by
  have h := inv_unique' hx hy heq
  apply inv_unique' hy hx
  rw [← h]; exact (H.mul_inv hy).symm

lemma inv_eq {T₁ T₂ : Subgroup S} (heq : T₁.carrier = T₂.carrier) : T₁.inv = T₂.inv := by
  ext x
  by_cases hx : x ∈ T₁.carrier
  · have hx₂ : x ∈ T₂.carrier := heq ▸ hx
    have h₃ : T₁.inv x ∈ T₂.carrier := heq ▸ T₁.inv_mem hx
    exact (inv_unique' h₃ hx₂ ((T₁.inv_mul hx).symm ▸ (one_eq heq).symm)).symm
  · rw [T₁.inv_not_mem hx, T₂.inv_not_mem (heq ▸ hx)]

instance : SetLike (Subgroup S) S :=
  ⟨Subsemigroup.carrier ∘ Submonoid.toSubsemigroup ∘ Subgroup.toSubmonoid, fun T₁ T₂ h => by
    have heq : T₁.carrier = T₂.carrier := by simp_all
    have hone : T₁.one = T₂.one := one_eq heq
    have hinv : T₁.inv = T₂.inv := inv_eq heq
    cases T₁; rename Submonoid S => T₁'; cases T₁'
    rename Subsemigroup S => T₁''; cases T₁''
    cases T₂; rename Submonoid S => T₂'; cases T₂'
    rename Subsemigroup S => T₂''; cases T₂''; congr⟩

instance : PartialOrder (Subgroup S) := PartialOrder.ofSetLike _ _

@[simp] lemma mem_carrier {p : Subgroup S} {x : S} : x ∈ p.carrier ↔ x ∈ (p : Set S) :=
  Iff.rfl

@[ext] theorem ext {p q : Subgroup S} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

instance (H : Subgroup S) : Group H where
  mul := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, H.mul_mem ha hb⟩
  mul_assoc := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Subtype.ext (mul_assoc a b c)
  one := ⟨H.one, H.one_mem⟩
  mul_one := fun ⟨a, ha⟩ => Subtype.ext (H.mul_one ha)
  one_mul := fun ⟨a, ha⟩ => Subtype.ext (H.one_mul ha)
  inv := fun ⟨a, ha⟩ => ⟨H.inv a, H.inv_mem ha⟩
  inv_mul_cancel := fun ⟨a, ha⟩ => Subtype.ext (H.inv_mul ha)

variable {H : Subgroup S}

@[simp] theorem coe_mul (x y : H) : (↑(x * y) : S) = ↑x * ↑y := rfl

@[simp] theorem mk_mul_mk (x y : S) (hx : x ∈ H) (hy : y ∈ H) :
    (⟨x, hx⟩ : H) * ⟨y, hy⟩ = ⟨x * y, H.mul_mem hx hy⟩ := rfl

@[simp] theorem mul_def (x y : H) :
    x * y = ⟨x * y, H.mul_mem x.2 y.2⟩ := rfl

theorem one_def : (1 : H) = ⟨H.one, H.one_mem⟩ := rfl

@[simp] theorem coe_one : ↑(1 : H) = H.one := rfl

@[simp] theorem inv_def (x : H) : x⁻¹ = ⟨H.inv x.1, H.inv_mem x.2⟩ := rfl

/-- A subgroup is maximal if it is not properly contained in any larger subgroup. -/
def IsMaximal (H : Subgroup S) : Prop :=
  ∀ K : Subgroup S, H ≤ K → H = K

lemma mem_def {H : Subgroup S} (x : S) : x ∈ H ↔ x ∈ H.carrier := Iff.rfl

/-- Lift a carrier-bijection to a type-level bijection on subtypes. -/
def bijOn_toEquiv {H K : Subgroup S} (f : S → S) (hbij : Set.BijOn f H.carrier K.carrier) :
    Function.Bijective (fun x : ↑H ↦ (⟨f x.val, hbij.1 x.prop⟩ : ↑K)) := by
  constructor
  · intro a b hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (hbij.2.1 a.prop b.prop hab)
  · intro y
    obtain ⟨z, hz₁, hz₂⟩ := hbij.2.2 y.prop
    exact ⟨⟨z, hz₁⟩, Subtype.ext hz₂⟩

/-- Given a bijection between two subgroups that preserves multiplication,
construct an isomorphism. -/
noncomputable def hom_of_bijOn {H K : Subgroup S}
  (f : S → S)
  (hbij : Set.BijOn f H.carrier K.carrier)
  (hpres : ∀ (x y : S), x ∈ H → y ∈ H → f (x * y) = f x * f y)
  : H ≃* K := by
  have hbije := bijOn_toEquiv f hbij
  exact {
    toFun := fun x => ⟨f x.val, hbij.1 x.prop⟩
    invFun := Function.surjInv hbije.surjective
    left_inv := Function.leftInverse_surjInv hbije
    right_inv := Function.rightInverse_surjInv hbije.surjective
    map_mul' := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      exact Subtype.ext (hpres a b ha hb)
  }

end Subgroup

end Semigroup
