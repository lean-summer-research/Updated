import Mathlib.Algebra.Group.WithOne.Defs

/-!
# Green's Relations

This file defines Green's preorders and equivalence relations on semigroups.

## Main definitions

**Green's Preorders** for `x y : S` in a semigroup `S`:
* `Semigroup.RPreorder` (`x ≤𝓡 y`) — `∃ z : WithOne S, ↑y * z = ↑x`.
* `Semigroup.LPreorder` (`x ≤𝓛 y`) — `∃ z : WithOne S, z * ↑y = ↑x`.
* `Semigroup.JPreorder` (`x ≤𝓙 y`) — `∃ w v : WithOne S, w * ↑y * v = ↑x`.
* `Semigroup.HPreorder` (`x ≤𝓗 y`) — `x ≤𝓡 y ∧ x ≤𝓛 y`.

**Green's Equivalences** (symmetric closures of the preorders):
* `Semigroup.REquiv` (`x 𝓡 y`), `Semigroup.LEquiv` (`x 𝓛 y`),
  `Semigroup.JEquiv` (`x 𝓙 y`), `Semigroup.HEquiv` (`x 𝓗 y`).
* `Semigroup.DEquiv` (`x 𝓓 y`) — composition of 𝓡 and 𝓛.

**Equivalence classes** as sets:
* `⟦x⟧𝓡`, `⟦x⟧𝓛`, `⟦x⟧𝓙`, `⟦x⟧𝓗`, `⟦x⟧𝓓`.

## Main results

* `Semigroup.rEquiv_lEquiv_comm` — 𝓡 and 𝓛 commute under composition.
* `Semigroup.DEquiv.isEquivalence` — 𝓓 is an equivalence relation.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-! ### Green's Preorders -/

/-- `x` is 𝓡-below `y` if `x = y` or there exists a `z : S` such that `y * z = x`. -/
def RPreorder (x y : S) : Prop := ∃ z : WithOne S , ↑y * z = ↑x

infix:50 " ≤𝓡 " => RPreorder

namespace RPreorder

@[simp] lemma refl (x : S) : x ≤𝓡 x := ⟨1, by simp⟩

@[trans] lemma trans {x y z : S} (hxy : x ≤𝓡 y) (hyz : y ≤𝓡 z) : x ≤𝓡 z := by
  obtain ⟨w, hw⟩ := hxy
  obtain ⟨v, hv⟩ := hyz
  exact ⟨v * w, by rw [← mul_assoc, hv, hw]⟩

instance isPreorder : IsPreorder S RPreorder where
  refl := refl
  trans := @trans _ _

end RPreorder

/-- `x` is 𝓛-below `y` if `x = y` or there exists a `z : S` such that `z * y = x`. -/
def LPreorder (x y : S) : Prop := ∃ z : WithOne S, z * ↑y = ↑x

infix:50 " ≤𝓛 " => LPreorder

namespace LPreorder

@[simp] lemma refl (x : S) : x ≤𝓛 x := ⟨1, by simp⟩

@[trans] lemma trans {x y z : S} (hxy : x ≤𝓛 y) (hyz : y ≤𝓛 z) : x ≤𝓛 z := by
  obtain ⟨u, hu⟩ := hxy
  obtain ⟨v, hv⟩ := hyz
  exact ⟨u * v, by rw [mul_assoc, hv, hu]⟩

/-- `≤𝓛` is a Preorder -/
instance isPreorder : IsPreorder S LPreorder where
  refl := refl
  trans := @trans _ _

end LPreorder

/-- `x` is 𝓙-below `y` if there exists `w v : WithOne S` such that `w * ↑y * v = ↑x`. -/
def JPreorder (x y : S) : Prop := ∃ w v : WithOne S, w * ↑y * v = ↑x

infix:50 " ≤𝓙 " => JPreorder

namespace JPreorder

@[simp] lemma refl (x : S) : x ≤𝓙 x := ⟨1, 1, by simp⟩

@[trans] lemma trans {x y z : S} (hxy : x ≤𝓙 y) (hyz : y ≤𝓙 z) : x ≤𝓙 z := by
  obtain ⟨u₁, v₁, h₁⟩ := hxy
  obtain ⟨u₂, v₂, h₂⟩ := hyz
  exact ⟨u₁ * u₂, v₂ * v₁, by rw [← h₁, ← h₂]; simp [mul_assoc]⟩

instance isPreorder : IsPreorder S JPreorder where
  refl := refl
  trans := @trans _ _

end JPreorder

/-- `x` is 𝓗-below `y` if `x ≤𝓡 y` and `x ≤𝓛 y`. -/
def HPreorder (x y : S) : Prop := x ≤𝓡 y ∧ x ≤𝓛 y

notation:50 f " ≤𝓗 " g:50 => HPreorder f g

namespace HPreorder

@[simp] lemma refl (x : S) : x ≤𝓗 x := ⟨RPreorder.refl x, LPreorder.refl x⟩

@[trans] lemma trans {x y z : S} (hxy : x ≤𝓗 y) (hyz : y ≤𝓗 z) : x ≤𝓗 z :=
  ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩

instance isPreorder : IsPreorder S HPreorder where
  refl := refl
  trans := @trans _ _

end HPreorder

/-! ### Green's Equivalences (except 𝓓) -/

/-- The symmetric closure of a preorder is an equivalence relation. -/
def _root_.IsPreorder.SymmClosure {α : Type*} (p : α → α → Prop) [h : IsPreorder α p] :
    Equivalence (fun x y ↦ p x y ∧ p y x) where
  refl x := ⟨h.refl x, h.refl x⟩
  symm := And.symm
  trans h₁ h₂ := ⟨h.trans _ _ _ h₁.1 h₂.1, h.trans _ _ _ h₂.2 h₁.2⟩

/-- Green's 𝓡 equivalence: the symmetric closure of `≤𝓡`. -/
def REquiv (x y : S) : Prop := x ≤𝓡 y ∧ y ≤𝓡 x

notation :50 x " 𝓡 " y:50 => REquiv x y

namespace REquiv

theorem isEquivalence : Equivalence (fun x y : S ↦ x 𝓡 y) :=
  IsPreorder.SymmClosure (fun x y : S ↦ x ≤𝓡 y)

@[simp] lemma refl (x : S) : x 𝓡 x := REquiv.isEquivalence.refl x
@[simp, symm] lemma symm {x y : S} (h : x 𝓡 y) : y 𝓡 x := REquiv.isEquivalence.symm h
@[trans] lemma trans {x y z : S} (h₁ : x 𝓡 y) (h₂ : y 𝓡 z) : x 𝓡 z :=
  REquiv.isEquivalence.trans h₁ h₂

def set (x : S) : Set (S) := {y | y 𝓡 x}
notation "⟦" x "⟧𝓡" => set x
@[simp] lemma set_def (x : S) : ⟦x⟧𝓡 = {y | y 𝓡 x} := rfl
@[simp] lemma set_refl (x : S) : x ∈ ⟦x⟧𝓡 := refl x
@[simp] lemma mem_set {x y : S} : y ∈ ⟦x⟧𝓡 ↔ y 𝓡 x := Iff.rfl

end REquiv

/-- Green's 𝓛 equivalence: the symmetric closure of `≤𝓛`. -/
def LEquiv (x y : S) : Prop := x ≤𝓛 y ∧ y ≤𝓛 x

notation :50 x " 𝓛 " y:50 => LEquiv x y

namespace LEquiv

theorem isEquivalence : Equivalence (fun x y : S ↦ x 𝓛 y) :=
  IsPreorder.SymmClosure (fun x y : S ↦ x ≤𝓛 y)

@[simp] lemma refl (x : S) : x 𝓛 x := isEquivalence.refl x
@[simp, symm] lemma symm {x y : S} (h : x 𝓛 y) : y 𝓛 x := isEquivalence.symm h
@[trans] lemma trans {x y z : S} (h₁ : x 𝓛 y) (h₂ : y 𝓛 z) : x 𝓛 z := isEquivalence.trans h₁ h₂

def set (x : S) : Set (S) := {y | y 𝓛 x}
notation "⟦" x "⟧𝓛" => set x
@[simp] lemma set_def (x : S) : ⟦x⟧𝓛 = {y | y 𝓛 x} := rfl
@[simp] lemma set_refl (x : S) : x ∈ ⟦x⟧𝓛 := refl x
@[simp] lemma mem_set {x y : S} : y ∈ ⟦x⟧𝓛 ↔ y 𝓛 x := Iff.rfl

end LEquiv

/-- Green's 𝓙 equivalence: the symmetric closure of `≤𝓙`. -/
def JEquiv (x y : S) : Prop := x ≤𝓙 y ∧ y ≤𝓙 x

notation :50 x " 𝓙 " y:50 => JEquiv x y

namespace JEquiv

theorem isEquivalence : Equivalence (fun x y : S ↦ x 𝓙 y) :=
  IsPreorder.SymmClosure (fun x y : S ↦ x ≤𝓙 y)

@[simp] lemma refl (x : S) : x 𝓙 x := isEquivalence.refl x
@[simp, symm] lemma symm {x y : S} (h : x 𝓙 y) : y 𝓙 x := isEquivalence.symm h
@[trans] lemma trans {x y z : S} (h₁ : x 𝓙 y) (h₂ : y 𝓙 z) : x 𝓙 z := isEquivalence.trans h₁ h₂

def set (x : S) : Set (S) := {y | y 𝓙 x}
notation "⟦" x "⟧𝓙" => set x
@[simp] lemma set_def (x : S) : ⟦x⟧𝓙 = {y | y 𝓙 x} := rfl
@[simp] lemma set_refl (x : S) : x ∈ ⟦x⟧𝓙 := JEquiv.refl x
@[simp] lemma mem_set {x y : S} : y ∈ ⟦x⟧𝓙 ↔ y 𝓙 x := Iff.rfl

end JEquiv

/-- Green's 𝓗 equivalence: the symmetric closure of `≤𝓗`. -/
def HEquiv (x y : S) : Prop := x ≤𝓗 y ∧ y ≤𝓗 x

notation :50 x " 𝓗 " y:50 => HEquiv x y

namespace HEquiv

theorem isEquivalence : Equivalence (fun x y : S ↦ x 𝓗 y) :=
  IsPreorder.SymmClosure (fun x y : S ↦ x ≤𝓗 y)

@[simp] lemma refl (x : S) : x 𝓗 x := isEquivalence.refl x
@[simp, symm] lemma symm {x y : S} (h : x 𝓗 y) : y 𝓗 x := isEquivalence.symm h
@[trans] lemma trans {x y z : S} (h₁ : x 𝓗 y) (h₂ : y 𝓗 z) : x 𝓗 z := isEquivalence.trans h₁ h₂

def set (x : S) : Set (S) := {y | y 𝓗 x}
notation "⟦" x "⟧𝓗" => set x
@[simp] lemma set_def (x : S) : ⟦x⟧𝓗 = {y | y 𝓗 x} := rfl
@[simp] lemma set_refl (x : S) : x ∈ ⟦x⟧𝓗 := HEquiv.refl x
@[simp] lemma mem_set {x y : S} : y ∈ ⟦x⟧𝓗 ↔ y 𝓗 x := Iff.rfl

end HEquiv

/-! ### Commutativity of 𝓡 and 𝓛 -/

/-- 𝓡 and 𝓛 commute under composition. -/
theorem rEquiv_lEquiv_comm (x y : S) : (∃ z, x 𝓡 z ∧ z 𝓛 y) ↔ (∃ z, x 𝓛 z ∧ z 𝓡 y) := by
  constructor
  · rintro ⟨z, ⟨hr, hl⟩⟩
    have hr₁ := hr
    have hl₁ := hl
    rcases hr₁ with ⟨⟨w₁, hw₁⟩, ⟨v₁, hv₁⟩⟩
    rcases hl₁ with ⟨⟨w₂, hw₂⟩, ⟨v₂, hv₂⟩⟩
    cases v₂ with
    | one =>
      simp only [one_mul, WithOne.coe_inj] at hv₂
      subst z
      exact ⟨x, LEquiv.refl x, hr⟩
    | coe v₂ =>
      cases w₁ with
      | one =>
        simp only [mul_one, WithOne.coe_inj] at hw₁
        subst hw₁
        exact ⟨y, hl, REquiv.refl y⟩
      | coe w₁ =>
        refine ⟨v₂ * z * w₁, ⟨?_, ⟨v₂, by simp only [mul_assoc, WithOne.coe_mul]; rw [← hw₁]⟩⟩,
          ⟨⟨w₁, by simp[hv₂]⟩ , ?_⟩⟩
        · use w₂
          simp only [WithOne.coe_mul, ← mul_assoc]
          rw [mul_assoc w₂, hv₂, hw₂, ← hw₁]
        · use v₁
          simp only [mul_assoc v₂, WithOne.coe_mul]
          rw [hw₁, ← hv₂, ← hv₁]
          simp [mul_assoc]
  · rintro ⟨z, ⟨hl, hr⟩⟩
    have hr₁ := hr; have hl₁ := hl
    rcases hr₁ with ⟨⟨w₁, hw₁⟩, ⟨v₁, hv₁⟩⟩
    rcases hl₁ with ⟨⟨w₂, hw₂⟩, ⟨v₂, hv₂⟩⟩
    cases w₂ with
    | one =>
      simp only [one_mul, WithOne.coe_inj] at hw₂
      subst z
      exact ⟨y, hr, LEquiv.refl y⟩
    | coe w₂ =>
      cases v₁ with
      | one =>
        simp only [mul_one, WithOne.coe_inj] at hv₁
        subst hv₁
        exact ⟨x, REquiv.refl x, hl⟩
      | coe v₁ =>
        refine ⟨w₂ * z * v₁, ⟨?_, ⟨v₁, by simp [hw₂]⟩⟩, ⟨⟨w₂, by simp [← hv₁, ← mul_assoc]⟩,
          ⟨v₂, by simp [hw₂, ← mul_assoc, hv₂, hv₁]⟩⟩⟩
        · use w₁; simp only [WithOne.coe_mul]
          nth_rw 1 [← hw₂]; conv => lhs; lhs; rw [mul_assoc, hv₁]
          rw [mul_assoc, hw₁]

/-! ### Green's 𝓓 relation -/

/-- Green's 𝓓 equivalence: the composition of 𝓡 and 𝓛. -/
def DEquiv : S → S → Prop := fun x y => ∃ z, x 𝓡 z ∧ z 𝓛 y

infix:50 " 𝓓 " => DEquiv

namespace DEquiv

@[simp] lemma refl (x : S) : x 𝓓 x := ⟨x, REquiv.refl x, LEquiv.refl x⟩

@[simp, symm] lemma symm {x y : S} (h : x 𝓓 y) : y 𝓓 x := by
  obtain ⟨z, hz₁, hz₂⟩ := h
  rw [DEquiv, rEquiv_lEquiv_comm]
  exact ⟨z, hz₂.symm, hz₁.symm⟩

lemma closed_under_lEquiv {x y z : S} (hd : x 𝓓 y) (hl : y 𝓛 z) : x 𝓓 z :=
  let ⟨w, hw₁, hw₂⟩ := hd
  ⟨w, hw₁, hw₂.trans hl⟩

lemma closed_under_rEquiv {x y z : S} (hd : x 𝓓 y) (hl : y 𝓡 z) : x 𝓓 z := by
  obtain ⟨w, hw₁, hw₂⟩ := hd.symm
  exact (show z 𝓓 x from ⟨w, hl.symm.trans hw₁, hw₂⟩).symm

@[trans] lemma trans {x y z : S} (h₁ : x 𝓓 y) (h₂ : y 𝓓 z) : x 𝓓 z := by
  obtain ⟨w, hw₁, hw₂⟩ := h₂
  exact (h₁.closed_under_rEquiv hw₁).closed_under_lEquiv hw₂

theorem isEquivalence : Equivalence (fun x y : S => x 𝓓 y) where
  refl := refl; symm := symm; trans := trans

def set (x : S) : Set (S) := {y | y 𝓓 x}
notation "⟦" x "⟧𝓓" => set x
@[simp] lemma set_def (x : S) : ⟦x⟧𝓓 = {y | y 𝓓 x} := rfl
@[simp] lemma set_refl (x : S) : x ∈ ⟦x⟧𝓓 := DEquiv.refl x
@[simp] lemma mem_set {x y : S} : y ∈ ⟦x⟧𝓓 ↔ y 𝓓 x := Iff.rfl

end DEquiv

/-! #### `le` and `ge` projections -/

variable {x y : S}

@[simp] lemma REquiv.le (h : x 𝓡 y) : x ≤𝓡 y := h.1
@[simp] lemma REquiv.ge (h : x 𝓡 y) : y ≤𝓡 x := h.2
@[simp] lemma LEquiv.le (h : x 𝓛 y) : x ≤𝓛 y := h.1
@[simp] lemma LEquiv.ge (h : x 𝓛 y) : y ≤𝓛 x := h.2
@[simp] lemma JEquiv.le (h : x 𝓙 y) : x ≤𝓙 y := h.1
@[simp] lemma JEquiv.ge (h : x 𝓙 y) : y ≤𝓙 x := h.2
@[simp] lemma HEquiv.le (h : x 𝓗 y) : x ≤𝓗 y := h.1
@[simp] lemma HEquiv.ge (h : x 𝓗 y) : y ≤𝓗 x := h.2

end Semigroup
