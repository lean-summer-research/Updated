import Semigroup.Regular
import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# Rees Matrix Semigroups

This file defines Rees matrix semigroups (with and without zero).

## Main Definitions

* `Semigroup.Rees` — a Rees matrix semigroup `M[G; I, J; P]` over a group `G`
  with index sets `I, J` and sandwich matrix `P : I → J → G`.
* `Semigroup.ReesZero` — a Rees matrix semigroup with zero `M⁰[G; I, J; P]`,
  where `P : I → J → WithZero G` and zero products are possible.
-/

namespace Semigroup

section ReesWithoutZero

variable {I : Type*} {J : Type*} {G : Type*} [Group G] (P : I → J → G)

/-- A Rees matrix semigroup element consists of a row index, column index, and group element. -/
structure Rees (P : I → J → G) : Type _ where
  i : I
  j : J
  g : G

omit [Group G] in
@[ext] theorem Rees.ext {a b : Rees P} (hi : a.i = b.i) (hj : a.j = b.j) (hg : a.g = b.g) :
    a = b := by cases a; cases b; congr

instance Rees.instMul : Mul (Rees P) where
  mul (a b : Rees P) := ⟨a.i, b.j, a.g * (P b.i a.j) * b.g⟩

@[simp] lemma Rees.mul_def (i₁ i₂ : I) (j₁ j₂ : J) (g₁ g₂ : G) :
    ⟨i₁, j₁, g₁⟩ * ⟨i₂, j₂, g₂⟩ = (⟨i₁, j₂, g₁ * (P i₂ j₁) * g₂⟩ : Rees P):= by rfl

@[simp] lemma Rees.mul_i (a b : Rees P) : (a * b).i = a.i := rfl
@[simp] lemma Rees.mul_j (a b : Rees P) : (a * b).j = b.j := rfl
@[simp] lemma Rees.mul_g (a b : Rees P) : (a * b).g = a.g * (P b.i a.j) * b.g := rfl

instance Rees.instSemigroup : Semigroup (Rees P) where
  mul_assoc := by
    rintro ⟨i₁, j₁, g₁⟩ ⟨i₂, j₂, g₂⟩ ⟨i₃, j₃, g₃⟩
    simp [← mul_assoc]

end ReesWithoutZero

section ReesWithZero

variable {I : Type*} {J : Type*} {G : Type*} [Group G]

/-- A nonzero element of a Rees matrix semigroup with zero. The full semigroup is
`Option (ReesZero P)` where `none` represents zero. -/
structure ReesZero (P : I → J → (WithZero G)) : Type _ where
  i : I
  j : J
  g : G

variable (P : I → J → (WithZero G))

instance ReesZero.instMul : Mul (Option (ReesZero P)) where
  mul (x y : Option (ReesZero P)) :=
    match x, y with
    | some a, some b =>
      let pg := P b.i a.j
      match pg with
      | some pg => some ⟨a.i, b.j, a.g * pg * b.g⟩
      | none => none
    | _, _ => none

@[simp] lemma ReesZero.none_mul (x : Option (ReesZero P)) :
    none * x = none := by rfl

@[simp] lemma ReesZero.mul_none (x : Option (ReesZero P)) :
    x * none = none := by rcases x <;> rfl

@[simp] lemma ReesZero.mul_def (x y : (ReesZero P)) :
    some x * some y =
      (match P y.i x.j with
        | some pg => (some ⟨x.i, y.j, x.g * pg * y.g⟩ : Option (ReesZero P))
        | none => (none : Option (ReesZero P))) := by rfl

lemma ReesZero.mul_of_ne_none (x y : ReesZero P) {g : G} (hp : P y.i x.j = some g) :
    some x * some y = some ⟨x.i, y.j, x.g * g * y.g⟩ := by simp_all [mul_def]

instance ReesZero.instSemigroup : Semigroup (Option (ReesZero P)) where
  mul_assoc := by
    intro a b c
    rcases a with (hn | a)
    · simp
    rcases b with (hn | b)
    · simp
    rcases c with (hn | c)
    · simp
    simp
    by_cases h₁ : P b.i a.j ≠ none
    · simp_all only [WithZero]
      rw [Option.ne_none_iff_exists] at h₁
      obtain ⟨p₁, hp₁⟩ := h₁
      simp [← hp₁]
      · by_cases h₂ : P c.i b.j ≠ none
        · simp_all only [WithZero]
          rw [Option.ne_none_iff_exists] at h₂
          obtain ⟨p₂, hp₂⟩ := h₂
          simp [← hp₂, ← hp₁, ← mul_assoc]
        · simp_all
    · simp_all
      by_cases h₁ : P c.i b.j ≠ none
      · simp_all only [WithZero]
        rw [Option.ne_none_iff_exists] at h₁
        obtain ⟨p₁, hp₁⟩ := h₁
        simp [← hp₁, h₁]
      · simp_all

instance : Semigroup (Option (ReesZero P)) := ReesZero.instSemigroup P

/-- `Option (ReesZero P)` has zero given by `none`. -/
instance ReesZero.instZero : Zero (Option (ReesZero P)) where
  zero := none

/-- `Option (ReesZero P)` is a semigroup with zero. -/
instance ReesZero.instSemigroupWithZero : SemigroupWithZero (Option (ReesZero P)) where
  zero_mul := ReesZero.none_mul P
  mul_zero := ReesZero.mul_none P

/-- Given an element `(i, j, g)` of a *regular* Rees' Matrix semigroup with zero, there exists
a `i'` such that `P i' j ≠ none`. -/
lemma ReesZero.exists_nonzero_col (hreg : ∀ x : Option (ReesZero P), IsRegularElem x)
  (x : ReesZero P) :
    ∃ i' : I, P i' x.j ≠ none := by
  simp_all only [IsRegularElem, ne_eq]
  specialize hreg (some x)
  rcases hreg with ⟨y, hy⟩
  rcases y with (_ | y')
  · contradiction
  · by_cases hp : P y'.i x.j ≠ none
    · use y'.i
    · simp_all only [ne_eq, not_not]
      by_contra hneg
      simp_all

/-- Given an element `(i, j, g)` of a *regular* Rees' Matrix semigroup with zero, there exists
a `j'` such that `P i j' ≠ none`. -/
lemma ReesZero.exists_nonzero_row (hreg : ∀ x : Option (ReesZero P), IsRegularElem x)
  (x : ReesZero P) :
    ∃ j' : J, P x.i j' ≠ none := by
  simp_all only [IsRegularElem, ne_eq]
  specialize hreg (some x)
  rcases hreg with ⟨y, hy⟩
  rcases y with (_ | y')
  · simp_all
  · simp_all only [mul_def]
    by_cases hp : P y'.i x.j ≠ none
    · simp_all only [WithZero]
      rw [Option.ne_none_iff_exists] at hp
      obtain ⟨g, hg⟩ := hp
      rw [← hg] at hy
      simp at hy
      by_cases hp₂ : P x.i y'.j ≠ none
      · exact ⟨y'.j, hp₂⟩
      · simp_all
    · simp_all

/-- A Rees Matrix semigroup with zero is Regular iff every row and every column of its
sandwich matrix has a nonzero entry. -/
theorem ReesZero.regular_iff_nonzero (hi : ∀ i, ∃ x : ReesZero P, x.i = i)
  (hj : ∀ j, ∃ x : ReesZero P, x.j = j) :
    (∀ x : Option (ReesZero P), IsRegularElem x) ↔
    (∀ i : I, ∃ j : J, P i j ≠ none) ∧
    (∀ j : J, ∃ i : I, P i j ≠ none) := by
  constructor
  · intro hreg
    constructor
    · intro i
      obtain ⟨x, hx⟩ := hi i
      rw [← hx]
      exact ReesZero.exists_nonzero_row P hreg x
    · intro j
      obtain ⟨x, hx⟩ := hj j
      rw [← hx]
      exact ReesZero.exists_nonzero_col P hreg x
  · rintro ⟨hi₂, hj₂⟩
    simp only [IsRegularElem]
    intro x
    rcases x with (x | x)
    · use none; simp
    · obtain ⟨j', hj'⟩ := hi₂ x.i
      obtain ⟨i', hi'⟩ := hj₂ x.j
      simp_all only [WithZero]
      rw [Option.ne_none_iff_exists] at hi' hj'
      obtain ⟨y, hy⟩ := hi'
      obtain ⟨z, hz⟩ := hj'
      use some ⟨i', j', y⁻¹ * x.g⁻¹ * z⁻¹⟩
      simp [← hy, ← hz]
      congr
      simp [← mul_assoc]

end ReesWithZero

end Semigroup
