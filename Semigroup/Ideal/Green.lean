import Semigroup.Ideal.Defs
import Semigroup.Greens.Basic

/-!
# Green's Relations and Ideals

This file characterizes Green's relations in terms of principal ideals.

## Main Results

* `LPreorder.iff_leftIdeal_subset` — principal left ideal inclusion iff `x ≤𝓛 y`.
* `RPreorder.iff_rightIdeal_subset` — principal right ideal inclusion iff `x ≤𝓡 y`.
* `JPreorder.iff_mulTwoSidedIdeal_subset` — principal ideal inclusion iff `x ≤𝓙 y`.
* `LEquiv.iff_leftIdeal_eq` — principal left ideals are equal iff `x 𝓛 y`.
* `REquiv.iff_rightIdeal_eq` — principal right ideals are equal iff `x 𝓡 y`.
* `JEquiv.iff_mulTwoSidedIdeal_eq` — principal ideals are equal iff `x 𝓙 y`.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S] (x y : S)

/-- `x` is in the principal left ideal of `y` iff `x ≤𝓛 y`. -/
lemma LPreorder.iff_in_leftIdeal : x ∈ LeftIdeal.ofSet {y} ↔ x ≤𝓛 y := by
  simp_all only [LeftIdeal.mem_ofSet, Set.mul_singleton, Set.image_univ, Set.union_singleton,
    Set.mem_insert_iff, Set.mem_range]
  constructor <;> intro h
  · rcases h with heq | ⟨z, hz⟩
    · subst heq; simp
    · use z; simp_all [← WithOne.coe_mul]
  · obtain ⟨w, hw⟩ := h
    cases w with
    | one => simp_all
    | coe w =>
      right
      simp_all only [← WithOne.coe_mul, WithOne.coe_inj]
      use w

/-- For `x ∈ i : LeftIdeal S`, if `y ≤𝓛 x` then `y ∈ i`. -/
lemma LPreorder.le_in_leftIdeal {x y : S} {i : LeftIdeal S} (hx : x ∈ i) (hy : y ≤𝓛 x) :
    y ∈ i := by
  obtain ⟨z, hz⟩ := hy
  cases z with
  | one => simp_all
  | coe z =>
    simp_all [← WithOne.coe_mul]
    subst y; simp_all

/-- The principal left ideal of `x` is a subset of that of `y` iff `x ≤𝓛 y` -/
theorem LPreorder.iff_leftIdeal_subset : LeftIdeal.ofSet {x} ≤ LeftIdeal.ofSet {y} ↔ x ≤𝓛 y := by
  constructor
  · rintro h
    rw [← LPreorder.iff_in_leftIdeal]
    apply h; simp
  · rintro ⟨z, hz⟩
    cases z with
    | one => simp_all
    | coe z =>
      intros w hw
      rw [LPreorder.iff_in_leftIdeal] at hw ⊢
      simp_all only [← WithOne.coe_mul, WithOne.coe_inj]
      subst x
      apply LPreorder.trans hw; simp

/-- The principal left ideal of `x` is a equal to that of `y` iff `x 𝓛 y`. -/
theorem LEquiv.iff_leftIdeal_eq : LeftIdeal.ofSet {x} = LeftIdeal.ofSet {y} ↔ x 𝓛 y := by
  constructor
  · intro h
    constructor <;> rw [← LPreorder.iff_leftIdeal_subset, h]
  · rintro ⟨hr, hl⟩
    simp_all only [← LPreorder.iff_leftIdeal_subset]
    ext z
    constructor <;> intro h
    · exact hr h
    · exact hl h

/-- `x` is in the principal right ideal of `y` iff `x ≤𝓡 y`. -/
lemma RPreorder.iff_in_rightIdeal : x ∈ RightIdeal.ofSet {y} ↔ x ≤𝓡 y := by
  simp_all only [RightIdeal.mem_ofSet, Set.singleton_mul, Set.image_univ, Set.union_singleton,
    Set.mem_insert_iff, Set.mem_range]
  constructor
  · intro h
    rcases h with heq | ⟨z, hz⟩
    · subst heq; simp
    · use z; simp_all [← WithOne.coe_mul]
  · intro h
    obtain ⟨w, hw⟩ := h
    cases w with
    | one => simp_all
    | coe w =>
      right
      simp_all only [← WithOne.coe_mul, WithOne.coe_inj]
      use w

/-- For `x ∈ i : RightIdeal S`, if `y ≤𝓡 x` then `y ∈ i`. -/
lemma RPreorder.le_in_rightIdeal {x y : S} {i : RightIdeal S} (hx : x ∈ i) (hy : y ≤𝓡 x) :
    y ∈ i := by
  obtain ⟨z, hz⟩ := hy
  cases z with
  | one => simp_all
  | coe z =>
    simp_all [← WithOne.coe_mul]
    subst y; simp_all

/-- The principal right ideal of `x` is a subset of that of `y` iff `x ≤𝓡 y` -/
theorem RPreorder.iff_rightIdeal_subset : RightIdeal.ofSet {x} ≤ RightIdeal.ofSet {y} ↔ x ≤𝓡 y := by
  constructor
  · rintro h
    rw [← RPreorder.iff_in_rightIdeal]
    apply h; simp
  · rintro ⟨z, hz⟩
    cases z with
    | one => simp_all
    | coe z =>
      intros w hw
      rw [RPreorder.iff_in_rightIdeal] at hw ⊢
      simp_all only [← WithOne.coe_mul, WithOne.coe_inj]
      subst x
      apply hw.trans; simp

/-- The principal right ideal of `x` is a equal to that of `y` iff `x 𝓡 y`. -/
theorem REquiv.iff_rightIdeal_eq : RightIdeal.ofSet {x} = RightIdeal.ofSet {y} ↔ x 𝓡 y := by
  constructor
  · intro h
    constructor <;> rw [← RPreorder.iff_rightIdeal_subset, h]
  · rintro ⟨hr, hl⟩
    simp_all only [← RPreorder.iff_rightIdeal_subset]
    ext z
    constructor <;> intro h
    · exact hr h
    · exact hl h

/-- `x` is in the principal ideal of `y` iff `x ≤𝓙 y`. -/
lemma JPreorder.iff_in_mulTwoSidedIdeal : x ∈ MulTwoSidedIdeal.ofSet {y} ↔ x ≤𝓙 y := by
  simp_all only [MulTwoSidedIdeal.mem_ofSet, Set.mul_singleton, Set.image_univ, LeftIdeal.ofSet_coe,
    Set.union_singleton, Set.union_insert, RightIdeal.ofSet_coe, Set.singleton_mul, Set.mem_union,
    Set.mem_insert_iff, Set.mem_range, true_or, Set.insert_eq_of_mem]
  constructor <;> intro h
  · rcases h with ((h | ⟨z, hz⟩) | (⟨z, hz⟩ | ⟨z, hz⟩)) | h
    · simp_all
    · simp_all
      obtain ⟨w, hw⟩ := hz.1
      subst hw
      obtain ⟨v, hv⟩ := hz.2
      subst hv; simp
    · subst hz; simp
    · obtain ⟨w, hw⟩ := h
      subst hw; simp
  · obtain ⟨w, ⟨v, hv⟩⟩ := h
    cases w with
    | one =>
       cases v with
       | one => simp_all
       | coe v =>
         simp_all [← WithOne.coe_mul]
         subst x; simp_all
    | coe w =>
      cases v with
      | one =>
        simp_all [← WithOne.coe_mul]
        subst x; simp_all
      | coe v =>
        simp_all only [← WithOne.coe_mul, WithOne.coe_inj]
        subst x
        left; right; left
        use w * y; simp

/-- For `x ∈ i : MulTwoSidedIdeal S`, if `y ≤𝓙 x` then `y ∈ i`. -/
lemma JPreorder.le_in_mulTwoSidedIdeal {x y : S} {i : MulTwoSidedIdeal S}
  (hx : x ∈ i) (hy : y ≤𝓙 x) : y ∈ i := by
  obtain ⟨z, v, hy⟩ := hy
  cases z with
  | one =>
    cases v with
    | one => simp_all
    | coe v =>
      simp_all [← WithOne.coe_mul]
      subst y; simp_all
  | coe z =>
    cases v with
    | one =>
      simp_all [← WithOne.coe_mul]
      subst y; simp_all
    | coe v =>
      simp_all [← WithOne.coe_mul]
      subst y; simp_all

/-- The principal ideal of `x` is a subset of that of `y` iff `x ≤𝓙 y` -/
theorem JPreorder.iff_mulTwoSidedIdeal_subset :
    MulTwoSidedIdeal.ofSet {x} ≤ MulTwoSidedIdeal.ofSet {y} ↔ x ≤𝓙 y := by
  constructor
  · intros h
    rw [← JPreorder.iff_in_mulTwoSidedIdeal]
    apply h
    simp
  · rintro ⟨w, v, hx⟩
    cases w with
    | one =>
      simp_all only [one_mul]
      cases v with
      | one => simp_all
      | coe v =>
        simp_all only [← WithOne.coe_mul, WithOne.coe_inj]
        subst x
        intros z hz
        rw [JPreorder.iff_in_mulTwoSidedIdeal] at hz ⊢
        apply JPreorder.trans hz; simp_all
    | coe w =>
      cases v with
      | one =>
        simp_all only [← WithOne.coe_mul, mul_one, WithOne.coe_inj]
        subst x
        intros x hx
        rw [JPreorder.iff_in_mulTwoSidedIdeal] at hx ⊢
        apply JPreorder.trans hx; simp_all
      | coe v =>
        simp_all only [← WithOne.coe_mul, WithOne.coe_inj]
        subst x
        intros x hx
        rw [JPreorder.iff_in_mulTwoSidedIdeal] at hx ⊢
        apply JPreorder.trans hx; simp_all

/-- The principal ideal of `x` is a equal to that of `y` iff `x 𝓙 y`. -/
theorem JEquiv.iff_mulTwoSidedIdeal_eq :
    MulTwoSidedIdeal.ofSet {x} = MulTwoSidedIdeal.ofSet {y} ↔ x 𝓙 y := by
  constructor
  · intro h
    constructor <;> rw [← JPreorder.iff_mulTwoSidedIdeal_subset, h]
  · rintro ⟨hr, hl⟩
    simp_all only [← JPreorder.iff_mulTwoSidedIdeal_subset]
    ext z
    constructor <;> intros h
    · exact hr h
    · exact hl h

end Semigroup
