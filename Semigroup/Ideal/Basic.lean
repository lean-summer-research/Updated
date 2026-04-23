import Semigroup.Ideal.Defs

/-!
# Basic Properties of Semigroup Ideals

This file contains derived properties of semigroup ideals

## Main Results

* `LeftIdeal.ofSet_minimal` — `ofSet q` is the smallest left ideal containing `q`.
* `RightIdeal.ofSet_minimal` — `ofSet q` is the smallest right ideal containing `q`.
* `MulTwoSidedIdeal.ofSet_minimal` — `ofSet q` is the smallest two-sided ideal containing `q`.
* `MulTwoSidedIdeal.exists_mem_of_ne_empty` — a nonempty ideal has an element.
* `MulTwoSidedIdeal.minimal_ideal_unique` — minimal ideals are unique.
* `MulTwoSidedIdeal.principal_zero_eq` — the principal ideal of `0` is `{0}`.
* `MulTwoSidedIdeal.zero_is_minimal` — `{0}` is a minimal ideal.
-/

open Pointwise

namespace LeftIdeal

variable {S : Type*} [Semigroup S]

/-- `ofSet q` is the smallest left ideal containing `q`. -/
theorem ofSet_minimal {p : LeftIdeal S} {q : Set S} (hin : q ⊆ ↑p) :
    (ofSet q) ≤ p := by
  intro x (hx : x ∈ Set.univ * q ∪ q)
  simp only [Set.mem_union, Set.mem_mul] at hx
  rcases hx with ⟨y, _, w, hw, rfl⟩ | hx
  · exact p.mul_mem_mem (hin hw) y
  · exact hin hx

end LeftIdeal

namespace RightIdeal

variable {S : Type*} [Semigroup S]

/-- `ofSet q` is the smallest right ideal containing `q`. -/
theorem ofSet_minimal {p : RightIdeal S} {q : Set S} (hin : q ⊆ ↑p) :
    (ofSet q) ≤ p := by
  intro x (hx : x ∈ q * Set.univ ∪ q)
  simp only [Set.mem_union, Set.mem_mul] at hx
  rcases hx with ⟨y, hy, _, _, rfl⟩ | hx
  · exact p.mem_mul_mem (hin hy) _
  · exact hin hx

end RightIdeal

namespace MulTwoSidedIdeal

variable {α : Type*} [Mul α]

lemma exists_mem_of_ne_empty {I : MulTwoSidedIdeal α} (h : I ≠ ∅) : ∃ x, x ∈ I := by
  have hset : (I : Set α) ≠ ∅ := fun hh => h (SetLike.coe_injective hh)
  exact Set.nonempty_iff_ne_empty.mpr hset

/-- A semigroup has at most one minimal ideal. -/
theorem minimal_ideal_unique (I J : MulTwoSidedIdeal α) (hI : IsMinimal I) (hJ : IsMinimal J) :
    I = J := by
  obtain ⟨hI_ne, hI_min⟩ := hI
  obtain ⟨hJ_ne, hJ_min⟩ := hJ
  obtain ⟨a, ha⟩ := exists_mem_of_ne_empty hI_ne
  obtain ⟨b, hb⟩ := exists_mem_of_ne_empty hJ_ne
  have hab : a * b ∈ (I ∩ J : Set α) := ⟨I.mul_right_mem ha, J.mul_left_mem hb⟩
  have h_inter_ne : I ∩ J ≠ ∅ := by
    intro H
    have hset : (I ∩ J : Set α) = ∅ := congrArg (fun K : MulTwoSidedIdeal α => (K : Set α)) H
    rw [hset] at hab; exact hab
  exact (hI_min _ h_inter_ne fun _ hx => hx.1).symm |>.trans
    (hJ_min _ h_inter_ne fun _ hx => hx.2)

variable {S : Type*} [Semigroup S]

@[simp] lemma ofSet_coe_prop (p : Set S) {x y z : S} (hin : x ∈ ↑(ofSet p)) :
    z * x * y ∈ ↑(ofSet p) :=
  (ofSet p).mem_mul_mem ((ofSet p).mul_mem_mem hin z) y

theorem ofSet_minimal {p : MulTwoSidedIdeal S} {q : Set S} (hin : q ⊆ ↑p) :
    (ofSet q) ≤ p := by
  intro x (hx : x ∈ (ofSet q : Set S))
  rw [ofSet_coe] at hx
  simp only [LeftIdeal.ofSet_coe, RightIdeal.ofSet_coe,
    Set.mem_union, Set.mem_mul] at hx
  rcases hx with ((⟨_, ⟨_, _, w, hw, rfl⟩, _, _, rfl⟩ |
    ⟨_, _, b, hb, rfl⟩ | hx) | ⟨w, hw, _, _, rfl⟩ | hx)
  · exact MulTwoSidedIdeal.mem' (hin hw)
  · exact MulTwoSidedIdeal.mul_left_mem (hin hb)
  · exact hin hx
  · exact MulTwoSidedIdeal.mul_right_mem (hin hw)
  · exact hin hx

variable {S' : Type*} [SemigroupWithZero S']

/-- In a semigroup with zero, the principal ideal of `0` is `{0}`. -/
lemma principal_zero_eq : ((ofSet {(0 : S')}) : Set S') = {0} := by
  ext x; simp only [Set.mem_singleton_iff]; constructor
  · intro hx
    simp only [ofSet, Set.mul_singleton, mul_zero, Set.image_univ, Set.range_const,
      Set.singleton_mul, zero_mul, LeftIdeal.ofSet, Set.union_self, Set.singleton_union,
      RightIdeal.ofSet, SetLike.mem_coe] at hx
    rcases hx with (((⟨a, c, rfl⟩ | ⟨a, rfl⟩) | rfl) | ⟨b, rfl⟩) | rfl <;> simp
  · rintro rfl
    change (0 : S') ∈ ofSet {(0 : S')}
    simp only [ofSet, LeftIdeal.ofSet, RightIdeal.ofSet]
    right; right; rfl

/-- In a semigroup with zero, `{0}` (as a principal ideal) is minimal. -/
lemma zero_is_minimal : IsMinimal (ofSet {(0 : S')}) := by
  refine ⟨?_, ?_⟩
  · intro h
    have hset : ((ofSet {(0 : S')}) : Set S') = (∅ : Set S') :=
      congrArg (fun (I : MulTwoSidedIdeal S') => (I : Set S')) h
    rw [principal_zero_eq] at hset
    exact Set.singleton_ne_empty _ hset
  · intro J hJ_ne hJ_le
    ext x; constructor
    · exact fun hx => hJ_le hx
    · intro hx
      have : x ∈ ((ofSet {(0 : S')}) : Set S') := hx
      rw [principal_zero_eq, Set.mem_singleton_iff] at this; subst x
      obtain ⟨y, hy⟩ := exists_mem_of_ne_empty hJ_ne
      have h0 := J.mul_right_mem (y := 0) hy
      rwa [mul_zero] at h0

end MulTwoSidedIdeal
