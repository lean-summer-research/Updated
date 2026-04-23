import Mathlib.Data.Set.Function
import Semigroup.Greens.Basic

/-!
# Green's Lemma

This file proves Green's lemma for 𝓡 and 𝓛.

## Main Theorems

Let `x 𝓡 y` such that `y * u = x` and `x * v = y`.
* `REquiv.invOn_lClass` - the map `x ↦ x * u` is the inverse of `x ↦ x * v` on the 𝓛-class of `x`.
* `REquiv.bijOn_lClass` - the map `x ↦ x * v` is a bijection from the
𝓛-class of `x` to the 𝓛-class of `y`.
* `REquiv.bijOn_lClass_pres_hClass` - this bijection preserves 𝓗 classes.

Let `x 𝓛 y` such that `u * y = x` and `v * x = y`.
* `LEquiv.invOn_rClass` - the map `x ↦ u * x` is the inverse of `x ↦ v * x` on the 𝓡-class of `x`.
* `LEquiv.bijOn_rClass` - the map `x ↦ v * x` is a bijection from the
𝓡-class of `x` to the 𝓡-class of `y`.
* `LEquiv.bijOn_rClass_pres_hClass` - this bijection preserves 𝓗 classes.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S] {x y u v w : S}

/-- If `x 𝓡 y` such that `x * v = y` and `y * u = x`, then right translation by `v * u` on any
element 𝓛-equivalent to `x` is the identity. -/
private lemma REquiv.translation_id (hv : x * v = y) (hu : y * u = x) (hw : w 𝓛 x) :
    w * v * u = w := by
  rcases hw.le with ⟨z, hz⟩
  cases z with
  | one => simp only [one_mul, WithOne.coe_inj] at hz; subst hz; rw [hv, hu]
  | coe z =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hz
    subst hz
    rw [mul_assoc z, hv, mul_assoc, hu]

/-- If `x * v = y`, then the map `w ↦ w * v` maps the 𝓛-class of `x` to that of `y` -/
lemma RPreorder.mapsTo_lClass (hv : x * v = y) :
    Set.MapsTo (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  simp only [Set.MapsTo, LEquiv.set, Set.mem_setOf_eq]
  intros z hz
  rw [← hv]
  exact hz.rmul_compat v

/-- If `x 𝓡 y` such that `x * v = y` then the map `w ↦ w * v` is injective on the 𝓛-class of `x`. -/
lemma REquiv.injOn_lClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.InjOn (fun w ↦ w * v) ⟦x⟧𝓛 := by
  rcases hr.le with ⟨u, hu⟩
  cases u with
  | one => -- trivial case, x = y
    simp only [mul_one, WithOne.coe_inj] at hu; subst hu
    intros w hw z hz heq
    simp only [LEquiv.set, Set.mem_setOf_eq] at hw hz heq
    rw [← WithOne.coe_inj] at heq ⊢ hv
    simp only [WithOne.coe_mul] at heq hv
    obtain ⟨a, ha⟩ := hw.le
    obtain ⟨b, hb⟩ := hz.le
    rwa [← ha, ← hb, mul_assoc, mul_assoc, hv, ha, hb] at heq
  | coe u =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hu
    intros w hw z hz heq
    simp only at heq
    have hw₂ := REquiv.translation_id hv hu hw
    have hz₂ := REquiv.translation_id hv hu hz
    rw [← hw₂, ← hz₂, heq]

/-- If `x 𝓡 y` such that `x * v = y`, then the map `w ↦ w * v` is surjective
from the 𝓛-class of `x` to that of `y`. -/
lemma REquiv.surjOn_lClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.SurjOn (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  rcases hr.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp only [mul_one, WithOne.coe_inj] at hu; subst hu -- trivial case where y = x
    intros z hz
    use z
    rw [← WithOne.coe_inj] at hv ⊢
    simp_all only [refl, WithOne.coe_mul, LEquiv.set, Set.mem_setOf_eq, LEquiv.symm, true_and]
    obtain ⟨a, ha⟩ := hz.le
    rw [← ha, mul_assoc, hv]
  | coe u =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hu
    intros z hz
    simp only [LEquiv.set, Set.mem_setOf_eq, Set.mem_image] at hz ⊢
    use z * u
    exact ⟨by rw [← hu]; apply hz.rmul_compat, REquiv.translation_id hu hv hz⟩

/-- If `x * v = y` and `y * u = x`, then the map `w ↦ w * u` is the inverse of
`w ↦ w * v` when restricted to the 𝓛-classes of `x` and `y` -/
theorem REquiv.invOn_lClass (hv : x * v = y) (hu : y * u = x) :
    Set.InvOn (fun w ↦ w * u) (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  simp only [Set.InvOn, Set.LeftInvOn, LEquiv.set, Set.mem_setOf_eq]
  constructor <;> intro z hz
  · exact REquiv.translation_id hv hu hz
  · exact REquiv.translation_id hu hv hz

/-- If `x 𝓡 y` such that `x * v = y`, then the map `w ↦ w * v` is a bijection from
the 𝓛-class of `x` to that of `y`. -/
theorem REquiv.bijOn_lClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.BijOn (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 :=
  Set.BijOn.mk (RPreorder.mapsTo_lClass hv) (hr.injOn_lClass hv) (hr.surjOn_lClass hv)

theorem REquiv.exists_bij_on_lClass (hr : x 𝓡 y) : ∃ f : S → S, Set.BijOn f ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  rcases hr.ge with ⟨v, hv⟩
  cases v with
  | one =>
    simp only [mul_one, WithOne.coe_inj] at hv; subst hv -- trivial case where `x = y`
    exact ⟨id, by apply Set.bijOn_id⟩
  | coe v =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hv
    exact ⟨fun w ↦ w * v, hr.bijOn_lClass hv⟩

/-- If `x 𝓡 y` such that `x * v = y`, then the map `w ↦ w * v` preserves 𝓗-classes. -/
lemma REquiv.bijOn_lClass_pres_hClass (hr : x 𝓡 y) (hv : x * v = y) {a b : S} (hw : a 𝓛 x)
  (hz : b 𝓛 x) : a 𝓗 b ↔ (fun w ↦ w * v) a 𝓗 (fun w ↦ w * v) b := by
  simp only [HEquiv.iff_rEquiv_and_lEquiv]
  rcases hr.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp only [mul_one, WithOne.coe_inj] at hu; subst hu -- trivial case where `x = y`
    obtain ⟨z₁, hz₁⟩ := hw.le
    have hyv : ↑y * ↑v = (↑y : WithOne S) := by
      simp [← WithOne.coe_mul, hv]
    have hr₃ : a * v 𝓡 a := by
      simp only [REquiv, RPreorder.mul_right_self, true_and]
      exact ⟨1, by simp [← hz₁, mul_assoc, hyv]⟩
    obtain ⟨z₂, hz₂⟩ := hz.le
    have hr₄ : b 𝓡 b * v := by
      simp only [REquiv, RPreorder.mul_right_self, and_true]
      exact ⟨1, by simp [← hz₂, mul_assoc, hyv]⟩
    constructor
    · rintro ⟨hr₂, hl⟩
      exact ⟨hr₃.trans (hr₂.trans hr₄), hl.rmul_compat v⟩
    · rintro ⟨hr₁, hl⟩
      exact ⟨hr₃.symm.trans (hr₁.trans hr₄.symm), hw.trans hz.symm⟩
  | coe u =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hu
    have hid_a := REquiv.translation_id hv hu hw
    have hid_b := REquiv.translation_id hv hu hz
    have hr₂ : a * v 𝓡 a  := by
      simp only [REquiv, RPreorder.mul_right_self, true_and]
      exact ⟨u, by simpa [← WithOne.coe_mul, WithOne.coe_inj]⟩
    have hr₃ : b 𝓡 b * v := by
      simp only [REquiv, RPreorder.mul_right_self, and_true]
      exact ⟨u, by simpa [← WithOne.coe_mul, WithOne.coe_inj]⟩
    constructor <;> rintro ⟨hr₁, hl⟩
    · exact ⟨hr₂.trans (hr₁.trans hr₃), hl.rmul_compat v⟩
    · exact ⟨hr₂.symm.trans (hr₁.trans hr₃.symm), hw.trans hz.symm⟩

/-- If `x 𝓡 y` such that `x * v = y`, then for all `z 𝓛 x`, `z 𝓡 z * v`. -/
lemma REquiv.bijOn_lClass_rEquiv (hr : x 𝓡 y) (hv : x * v = y) {z : S} (hz : z 𝓛 x) :
    z 𝓡 z * v := by
  rcases hr.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp only [mul_one, WithOne.coe_inj] at hu; subst hu -- trivial case where `x = y`
    obtain ⟨a, ha⟩ := hz.le
    have hyv : ↑y * ↑v = (↑y : WithOne S) := by
      simp [← WithOne.coe_mul, hv]
    simp only [REquiv, RPreorder.mul_right_self, and_true]
    exact ⟨1, by simp [← ha, mul_assoc, hyv]⟩
  | coe u =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hu
    obtain ⟨a, ha⟩ := hz.le
    simp only [REquiv, RPreorder.mul_right_self, and_true]
    use u
    simp only [← WithOne.coe_mul, WithOne.coe_inj]
    apply REquiv.translation_id hv hu hz

lemma REquiv.mapsTo_hClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.MapsTo (fun w ↦ w * v) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  rcases hr.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp only [mul_one, WithOne.coe_inj] at hu; subst hu -- trivial case where `x = y`
    intros z
    simp_all only [refl, HEquiv.set, HEquiv.iff_rEquiv_and_lEquiv, Set.mem_setOf_eq, and_imp]
    intros hrz hlz
    have hyv : ↑y * ↑v = (↑y : WithOne S) := by
      simp [← WithOne.coe_mul, hv]
    have hr : z * v 𝓡 z := by
      obtain ⟨a, ha⟩ := hlz.le
      simp only [REquiv, RPreorder.mul_right_self, true_and]
      exact ⟨1, by simp [← ha, mul_assoc, hyv]⟩
    exact ⟨hr.trans hrz, by rw [← hv]; apply hlz.rmul_compat⟩
  | coe u =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hu
    intros z hz
    simp only [HEquiv.set, HEquiv.iff_rEquiv_and_lEquiv, Set.mem_setOf_eq]
    refine ⟨?_, (hr.bijOn_lClass hv).mapsTo hz.to_lEquiv⟩
    have hr₂ : z * v 𝓡 z := by
      simp only [REquiv, RPreorder.mul_right_self, true_and]
      use u
      simp only [← WithOne.coe_mul, WithOne.coe_inj]
      apply REquiv.translation_id hv hu
      exact hz.to_lEquiv
    exact hr₂.trans (hz.to_rEquiv.trans hr)

lemma REquiv.surjOn_hClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.SurjOn (fun w ↦ w * v) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  have hsurj := hr.surjOn_lClass hv
  rcases hr.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp only [mul_one, WithOne.coe_inj] at hu; subst hu -- trivial case where `x = y`
    intros z hz
    simp only [HEquiv.set, Set.mem_setOf_eq, Set.mem_image] at hz ⊢
    specialize hsurj hz.to_lEquiv
    simp only [LEquiv.set, Set.mem_image, Set.mem_setOf_eq] at hsurj
    obtain ⟨w, hw₁, hw₂⟩ := hsurj
    simp only [HEquiv.iff_rEquiv_and_lEquiv]
    refine ⟨w, ⟨?_, hw₁⟩, hw₂⟩
    have hw₃ : w 𝓡 z := by
      simp only [REquiv]
      refine ⟨?_, ⟨v, by simp [hw₂.symm]⟩⟩
      use 1; simp only [mul_one]
      obtain ⟨u, hu⟩ := hw₁.le
      have hv' : ↑y * ↑v = (↑y : WithOne S) := by simp [← WithOne.coe_mul, hv]
      simp only [← hw₂, WithOne.coe_mul]
      rw [← hu, mul_assoc, hv']
    apply hw₃.trans hz.to_rEquiv
  | coe u =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hu
    intros z hz
    specialize hsurj hz.to_lEquiv
    simp_all only [HEquiv.set, Set.mem_setOf_eq, LEquiv.set, Set.mem_image]
    obtain ⟨w, hw₁, hw₂⟩ := hsurj
    use w
    simp_all only [HEquiv.iff_rEquiv_and_lEquiv, LEquiv.symm, and_true]
    have hw₃ : w 𝓡 z := by
      subst hw₂
      simp only [REquiv, RPreorder.mul_right_self, and_true]
      use u
      simp only [← WithOne.coe_mul, WithOne.coe_inj]
      exact REquiv.translation_id hv hu hw₁
    exact hw₃.trans (hz.1.trans hr.symm)

lemma REquiv.injOn_hClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.InjOn (fun w ↦ w * v) ⟦x⟧𝓗 := by
  have h_inj := hr.injOn_lClass hv
  obtain ⟨u, hu⟩ := hr.le
  cases u with
  | one =>
    simp only [mul_one, WithOne.coe_inj] at hu; subst hu -- trivial case where `x = y`
    intros a ha b hb heq
    simp only [HEquiv.set, Set.mem_setOf_eq] at ha hb heq ⊢
    exact h_inj ha.to_lEquiv hb.to_lEquiv heq
  | coe u =>
    simp [← WithOne.coe_mul] at hu
    intros a ha b hb heq
    exact h_inj ha.to_lEquiv hb.to_lEquiv heq

lemma REquiv.invOn_hClass (hv : x * v = y) (hu : y * u = x) :
    Set.InvOn (fun w ↦ w * u) (fun w ↦ w * v) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  simp only [Set.InvOn, Set.LeftInvOn, HEquiv.set, Set.mem_setOf_eq]
  constructor <;> intro z hz
  · apply REquiv.translation_id hv hu hz.to_lEquiv
  · apply REquiv.translation_id hu hv hz.to_lEquiv

/-- If `x 𝓡 y` such that `x * v = y`, then the map `w ↦ w * v` is a bijection from
the 𝓗-class of `x` to that of `y`. -/
theorem REquiv.bijOn_hClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.BijOn (fun w ↦ w * v) ⟦x⟧𝓗 ⟦y⟧𝓗 :=
  Set.BijOn.mk (hr.mapsTo_hClass hv) (hr.injOn_hClass hv) (hr.surjOn_hClass hv)

theorem REquiv.exists_bij_on_hClass (hr : x 𝓡 y) : ∃ f : S → S, Set.BijOn f ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  rcases hr.ge with ⟨v, hv⟩
  cases v with
  | one =>
    simp only [mul_one, WithOne.coe_inj] at hv; subst hv
    exact ⟨id, by apply Set.bijOn_id⟩
  | coe v =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hv
    exact ⟨fun w ↦ w * v, hr.bijOn_hClass hv⟩

/-! ### Dual proofs -/

/-- If `x 𝓛 y` such that `u * y = x` and `v * x = y`, then left translation by `u * v` on any
element 𝓡-equivalent to `x` is the identity. -/
private lemma LEquiv.translation_id (hv : v * x = y) (hu : u * y = x) (hw : w 𝓡 x) :
    u * v * w = w := by
  rcases hw.le with ⟨z, hz⟩
  cases z with
  | one => simp only [mul_one, WithOne.coe_inj] at hz; subst hz; rw [mul_assoc, hv, hu]
  | coe z =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hz
    subst hz
    rw [← mul_assoc, mul_assoc u, hv, hu]

/-- If `v * x = y`, then the map `w ↦ v * w` maps the 𝓡-class of `x` to that of `y` -/
lemma LPreorder.mapsTo_rClass (hy : v * x = y) :
    Set.MapsTo (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  simp only [Set.MapsTo, REquiv.set, Set.mem_setOf_eq]
  intros z hz
  rw [← hy]
  exact hz.lmul_compat v

/-- If `x 𝓛 y` such that `v * x = y` then the map `w ↦ v * w` is injective on the 𝓡-class of `x`. -/
lemma LEquiv.injOn_rClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.InjOn (fun w ↦ v * w) ⟦x⟧𝓡 := by
  rcases hl.le with ⟨u, hu⟩
  cases u with
  | one => -- trivial case, x = y
    simp only [one_mul, WithOne.coe_inj] at hu; subst hu
    intros w hw z hz heq
    simp only [REquiv.set, Set.mem_setOf_eq] at hw hz heq
    rw [← WithOne.coe_inj] at heq ⊢ hv
    simp only [WithOne.coe_mul] at heq hv
    obtain ⟨a, ha⟩ := hw.le
    obtain ⟨b, hb⟩ := hz.le
    rwa [← ha, ← hb, ← mul_assoc, ← mul_assoc, hv, ha, hb] at heq
  | coe u =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hu
    intros w hw z hz heq
    simp only at heq
    have hw₂ := LEquiv.translation_id hv hu hw
    have hz₂ := LEquiv.translation_id hv hu hz
    rw [← hw₂, ← hz₂, mul_assoc, heq, ← mul_assoc]

/-- If `x 𝓛 y` such that `v * x = y`, then the map `w ↦ v * w` is surjective
from the 𝓡-class of `x` to that of `y`. -/
lemma LEquiv.surjOn_rClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.SurjOn (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  rcases hl.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp only [one_mul, WithOne.coe_inj] at hu; subst hu -- trivial case where y = x
    intros z hz
    use z
    rw [← WithOne.coe_inj] at hv ⊢
    simp_all only [refl, WithOne.coe_mul, REquiv.set, Set.mem_setOf_eq, REquiv.symm, true_and]
    obtain ⟨a, ha⟩ := hz.le
    rw [← ha, ← mul_assoc, hv]
  | coe u =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hu
    intros z hz
    simp only [REquiv.set, Set.mem_setOf_eq, Set.mem_image] at hz ⊢
    use u * z
    constructor
    · rw [← hu]
      apply hz.lmul_compat u
    · rw [← mul_assoc]
      apply LEquiv.translation_id hu hv hz

/-- If `u * y = x` and `v * x = y`, then the map `w ↦ u * w` is the inverse of
`w ↦ v * w` when restricted to the 𝓡-classes of `x` and `y` -/
theorem LEquiv.invOn_rClass (hv : v * x = y) (hu : u * y = x) :
    Set.InvOn (fun w ↦ u * w) (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  simp only [Set.InvOn, Set.LeftInvOn, REquiv.set, Set.mem_setOf_eq]
  constructor <;> intro z hz <;> rw [← mul_assoc]
  · apply LEquiv.translation_id hv hu hz
  · apply LEquiv.translation_id hu hv hz

/-- If `x 𝓛 y` such that `v * x = y`, then the map `w ↦ v * w` is a bijection from
the 𝓡-class of `x` to that of `y`. -/
theorem LEquiv.bijOn_rClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.BijOn (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 :=
  Set.BijOn.mk (LPreorder.mapsTo_rClass hv) (hl.injOn_rClass hv) (hl.surjOn_rClass hv)

theorem LEquiv.exists_bijOn_rClass (hl : x 𝓛 y) : ∃ f : S → S, Set.BijOn f ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  rcases hl.ge with ⟨v, hv⟩
  cases v with
  | one =>
    simp only [one_mul, WithOne.coe_inj] at hv; subst hv -- trivial case where `x = y`
    exact ⟨id, by apply Set.bijOn_id⟩
  | coe v =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hv
    exact ⟨fun w ↦ v * w, hl.bijOn_rClass hv⟩

/-- If `x 𝓛 y` such that `v * x = y`, then for all `z 𝓡 x`, `z 𝓛 v * z`. -/
lemma LEquiv.bijOn_rClass_lEquiv (hr : x 𝓛 y) (hv : v * x = y) {z : S} (hz : z 𝓡 x) :
    z 𝓛 v * z := by
  rcases hr.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp only [one_mul, WithOne.coe_inj] at hu; subst hu -- trivial case where `x = y`
    obtain ⟨a, ha⟩ := hz.le
    have hyv : ↑v * ↑y = (↑y : WithOne S) := by
      simp [← WithOne.coe_mul, hv]
    simp only [LEquiv, LPreorder.mul_left_self, and_true]
    exact ⟨1, by simp [← ha, ← mul_assoc, hyv]⟩
  | coe u =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hu
    obtain ⟨a, ha⟩ := hz.le
    simp only [LEquiv, LPreorder.mul_left_self, and_true]
    use u
    simp only [← WithOne.coe_mul, ← mul_assoc, WithOne.coe_inj]
    apply LEquiv.translation_id hv hu hz

lemma LEquiv.mapsTo_hClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.MapsTo (fun w ↦ v * w) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  rcases hl.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp only [one_mul, WithOne.coe_inj] at hu; subst hu -- trivial case where `x = y`
    intros z
    simp_all only [refl, HEquiv.set, HEquiv.iff_rEquiv_and_lEquiv, Set.mem_setOf_eq, and_imp]
    intros hrz hlz
    have hvy : ↑v * ↑y = (↑y : WithOne S) := by
      simp [← WithOne.coe_mul, hv]
    have hl : v * z 𝓛 z := by
      obtain ⟨a, ha⟩ := hrz.le
      simp only [LEquiv, LPreorder.mul_left_self, true_and]
      exact ⟨1, by simp [← ha, ← mul_assoc, hvy]⟩
    refine ⟨?_, hl.trans hlz⟩
    rw [← hv]
    apply hrz.lmul_compat
  | coe u =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hu
    intros z hz
    have hbij := hl.bijOn_rClass hv
    have h := hbij.mapsTo hz.to_rEquiv
    simp only [HEquiv.set, HEquiv.iff_rEquiv_and_lEquiv, Set.mem_setOf_eq]
    refine ⟨h, ?_⟩
    have hl₂ : v * z 𝓛 z := by
      simp only [LEquiv, LPreorder.mul_left_self, true_and]
      use u
      simp only [← WithOne.coe_mul, ← mul_assoc, WithOne.coe_inj]
      apply LEquiv.translation_id hv hu
      exact hz.to_rEquiv
    exact hl₂.trans (hz.to_lEquiv.trans hl)

lemma LEquiv.surjOn_hClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.SurjOn (fun w ↦ v * w) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  have hsurj := hl.surjOn_rClass hv
  rcases hl.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp only [one_mul, WithOne.coe_inj] at hu; subst hu -- trivial case where `x = y`
    intros z hz
    simp only [HEquiv.set, Set.mem_setOf_eq, Set.mem_image] at hz ⊢
    specialize hsurj hz.to_rEquiv
    simp only [REquiv.set, Set.mem_image, Set.mem_setOf_eq] at hsurj
    obtain ⟨w, hw₁, hw₂⟩ := hsurj
    simp only [HEquiv.iff_rEquiv_and_lEquiv]
    refine ⟨w, ⟨hw₁, ?_⟩, hw₂⟩
    have hw₃ : w 𝓛 z := by
      simp only [LEquiv]
      refine ⟨?_, ⟨v, by simp [hw₂.symm]⟩⟩
      use 1; simp only [one_mul]
      obtain ⟨a, ha⟩ := hw₁.le
      have hy' : ↑v * ↑y = (↑y : WithOne S) := by simp [← WithOne.coe_mul, hv]
      simp only [← hw₂, WithOne.coe_mul]
      rw [← ha, ← mul_assoc, hy']
    apply hw₃.trans hz.to_lEquiv
  | coe u =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hu
    intros z hz
    specialize hsurj hz.to_rEquiv
    simp_all only [HEquiv.set, Set.mem_setOf_eq, REquiv.set, Set.mem_image]
    obtain ⟨w, hw₁, hw₂⟩ := hsurj
    use w
    simp_all only [HEquiv.iff_rEquiv_and_lEquiv, REquiv.symm, true_and, and_true]
    have hw₃ : w 𝓛 z := by
      subst hw₂
      simp only [LEquiv, LPreorder.mul_left_self, and_true]
      use u
      simp only [← WithOne.coe_mul, ← mul_assoc, WithOne.coe_inj]
      exact LEquiv.translation_id hv hu hw₁
    exact hw₃.trans (hz.2.trans hl.symm)

lemma LEquiv.injOn_hClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.InjOn (fun w ↦ v * w) ⟦x⟧𝓗 := by
  have h_inj := hl.injOn_rClass hv
  obtain ⟨u, hx⟩ := hl.ge
  cases u with
  | one =>
    simp only [one_mul, WithOne.coe_inj] at hx; subst hx -- trivial case where `x = y`
    intros a ha b hb heq
    simp only [HEquiv.set, Set.mem_setOf_eq] at ha hb heq ⊢
    exact h_inj ha.to_rEquiv hb.to_rEquiv heq
  | coe u =>
    simp [← WithOne.coe_mul] at hx
    intros a ha b hb heq
    exact h_inj ha.to_rEquiv hb.to_rEquiv heq

lemma LEquiv.invOn_hClass (hv : v * x = y) (hu : u * y = x) :
    Set.InvOn (fun w ↦ u * w) (fun w ↦ v * w) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  simp only [Set.InvOn, Set.LeftInvOn, HEquiv.set, Set.mem_setOf_eq]
  constructor <;> intro z hz <;> rw [← mul_assoc]
  · apply LEquiv.translation_id hv hu hz.to_rEquiv
  · apply LEquiv.translation_id hu hv hz.to_rEquiv

/-- If `x 𝓛 y` such that `v * x = y`, then the map `w ↦ v * w` is a bijection from
the 𝓗-class of `x` to that of `y`. -/
theorem LEquiv.bijOn_hClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.BijOn (fun w ↦ v * w) ⟦x⟧𝓗 ⟦y⟧𝓗 :=
  Set.BijOn.mk (hl.mapsTo_hClass hv) (hl.injOn_hClass hv) (hl.surjOn_hClass hv)

theorem LEquiv.exists_bijOn_hClass (hl : x 𝓛 y) : ∃ f : S → S, Set.BijOn f ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  rcases hl.ge with ⟨v, hv⟩
  cases v with
  | one =>
    simp only [one_mul, WithOne.coe_inj] at hv; subst hv -- trivial case where `x = y`
    exact ⟨id, by apply Set.bijOn_id⟩
  | coe v =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hv
    exact ⟨fun w ↦ v * w, hl.bijOn_hClass hv⟩

end Semigroup
