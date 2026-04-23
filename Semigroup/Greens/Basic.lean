import Semigroup.Greens.Defs
import Mathlib.Algebra.Group.Idempotent

/-!
# Basic Properties of Green's Relations

This file proves basic lemmas about Green's relations.

## Main results

* `Semigroup.HEquiv.iff_rEquiv_and_lEquiv` — 𝓗 is the intersection of 𝓡 and 𝓛.

**Multiplication compatibility**
* `Semigroup.REquiv.lmul_compat` — `𝓡` is compatible with left multiplication.
* `Semigroup.LEquiv.rmul_compat` — `𝓛` is compatible with right multiplication.

**Coercion lemmas**
The `@[simp]`-tagged lemmas close goals like `x * y ≤𝓡 x` automatically.
Given `hr : x 𝓡 y` and a goal `x 𝓙 y`, `simp [hr]` or `simp_all` suffices.

**Idempotent properties**
* `Semigroup.RPreorder.le_idempotent` — `x ≤𝓡 e ↔ x = e * x`.
* `Semigroup.LPreorder.le_idempotent` — `x ≤𝓛 e ↔ x = x * e`.
* `Semigroup.HPreorder.le_idempotent` — `x ≤𝓗 e ↔ x = e * x ∧ x = x * e`.

**Morphism preservation** for all Green's relations and preorders.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-- 𝓗 is the intersection of 𝓡 and 𝓛. -/
theorem HEquiv.iff_rEquiv_and_lEquiv (x y : S) : x 𝓗 y ↔ x 𝓡 y ∧ x 𝓛 y := by
  simp [HEquiv, HPreorder, LEquiv, REquiv]; tauto

/-! ### Multiplication compatibility of 𝓡 and 𝓛 -/

@[simp] lemma RPreorder.lmul_compat {x y : S} (h : x ≤𝓡 y) (z : S) : z * x ≤𝓡 z * y := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, by simp [mul_assoc, hu]⟩

@[simp] theorem REquiv.lmul_compat {x y : S} (h : x 𝓡 y) (z : S) : z * x 𝓡 z * y :=
  ⟨h.1.lmul_compat z, h.2.lmul_compat z⟩

@[simp] lemma LPreorder.rmul_compat {x y : S} (h : x ≤𝓛 y) (z : S) : x * z ≤𝓛 y * z := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, by simp [← mul_assoc, hu]⟩

@[simp] theorem LEquiv.rmul_compat {x y : S} (h : x 𝓛 y) (z : S) : x * z 𝓛 y * z :=
  ⟨h.1.rmul_compat z, h.2.rmul_compat z⟩

section DerivedAPI

variable {x y z : S}

/-! ### Coercion lemmas -/

@[simp] lemma RPreorder.to_jPreorder (h : x ≤𝓡 y) : x ≤𝓙 y := by
  obtain ⟨u, hu⟩ := h
  exact ⟨1, u, by simp_all⟩

@[simp] lemma LPreorder.to_jPreorder (h : x ≤𝓛 y) : x ≤𝓙 y := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, 1, by simp_all⟩

@[simp] lemma HPreorder.to_rPreorder (h : x ≤𝓗 y) : x ≤𝓡 y := h.1
@[simp] lemma HPreorder.to_lPreorder (h : x ≤𝓗 y) : x ≤𝓛 y := h.2

@[simp] lemma REquiv.to_jEquiv (h : x 𝓡 y) : x 𝓙 y := by simp_all [JEquiv, REquiv]
@[simp] lemma LEquiv.to_jEquiv (h : x 𝓛 y) : x 𝓙 y := by simp_all [JEquiv, LEquiv]

@[simp] lemma DEquiv.to_jEquiv (h : x 𝓓 y) : x 𝓙 y := by
  obtain ⟨z, ⟨⟨o, ho⟩, ⟨u, hu⟩⟩, ⟨v, hv⟩, ⟨w, hw⟩⟩ := h
  exact ⟨⟨v, o, by rw [hv, ho]⟩, ⟨w, u, by rw [← hw, ← hu]; simp [← mul_assoc]⟩⟩

@[simp] lemma HEquiv.to_jEquiv (h : x 𝓗 y) : x 𝓙 y := by
  rw [HEquiv.iff_rEquiv_and_lEquiv] at h
  simp_all [JEquiv, REquiv]

@[simp] lemma HEquiv.to_rEquiv (h : x 𝓗 y) : x 𝓡 y := ((iff_rEquiv_and_lEquiv x y).mp h).1
@[simp] lemma HEquiv.to_lEquiv (h : x 𝓗 y) : x 𝓛 y := ((iff_rEquiv_and_lEquiv x y).mp h).2

@[simp] lemma HEquiv.to_dEquiv (h : x 𝓗 y) : x 𝓓 y := ⟨x, REquiv.refl x, h.to_lEquiv⟩
@[simp] lemma REquiv.to_dEquiv (h : x 𝓡 y) : x 𝓓 y := ⟨y, h, LEquiv.refl y⟩
@[simp] lemma LEquiv.to_dEquiv (h : x 𝓛 y) : x 𝓓 y := ⟨x, REquiv.refl x, h⟩

/-! ### Multiplication lemmas -/

@[simp] lemma RPreorder.mul_right_self : x * y ≤𝓡 x := ⟨y, WithOne.coe_mul ..⟩
@[simp] lemma LPreorder.mul_left_self : x * y ≤𝓛 y := ⟨x, WithOne.coe_mul ..⟩
@[simp] lemma JPreorder.mul_sandwich_self : x * y * z ≤𝓙 y := ⟨x, z, by simp⟩

@[simp] lemma REquiv.of_preorder_mul_right (h : x ≤𝓡 x * y) : x 𝓡 x * y :=
  ⟨h, RPreorder.mul_right_self⟩

@[simp] lemma LEquiv.of_preorder_mul_left (h : x ≤𝓛 y * x) : x 𝓛 y * x :=
  ⟨h, LPreorder.mul_left_self⟩

@[simp] lemma JEquiv.of_preorder_mul_sandwich (h : x ≤𝓙 y * x * z) : x 𝓙 y * x * z :=
  ⟨h, JPreorder.mul_sandwich_self⟩

@[simp] lemma REquiv.right_cancel (h : x 𝓡 x * y * z) : x 𝓡 x * y := by
  simp_all only [REquiv, RPreorder.mul_right_self, and_true]
  obtain ⟨⟨u, hu⟩, _⟩ := h
  exact ⟨z * u, by simp_rw [WithOne.coe_mul, ← mul_assoc] at *; exact hu⟩

@[simp] lemma REquiv.right_extend (h : x 𝓡 x * y * z) : x * y 𝓡 x * y * z := by
  simp_all only [REquiv, RPreorder.mul_right_self, and_true]
  obtain ⟨⟨u, hu⟩, _⟩ := h
  exact ⟨u * y, by simp_rw [WithOne.coe_mul, ← mul_assoc] at *; rw [hu]⟩

@[simp] lemma LEquiv.left_cancel (h : x 𝓛 z * y * x) : x 𝓛 y * x := by
  simp_all only [LEquiv, LPreorder.mul_left_self, and_true]
  obtain ⟨u, hu⟩ := h
  exact ⟨u * z, by simp_rw [WithOne.coe_mul, ← mul_assoc] at *; exact hu⟩

@[simp] lemma LEquiv.left_extend (h : x 𝓛 z * y * x) : y * x 𝓛 z * y * x := by
  simp_all only [LEquiv, LPreorder.mul_left_self, and_true, LPreorder.rmul_compat]
  obtain ⟨u, hu⟩ := h
  exact ⟨y * u, by
    simp_rw [WithOne.coe_mul, ← mul_assoc] at *
    have : ↑y * u * ↑z * y * x = ↑y * (u * ↑z * y * x) := by simp [← mul_assoc]
    rw [this, hu]⟩

end DerivedAPI

/-! ### Idempotent properties -/

/-- An element `x` is 𝓡-below an idempotent `e` if and only if `x = e * x`. -/
theorem RPreorder.le_idempotent {e : S} (h : IsIdempotentElem e) (x : S) :
    (x ≤𝓡 e) ↔ (e * x = x) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [← WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [← hru, ← mul_assoc, h]
  · intro hl
    exact ⟨x, by rwa [← WithOne.coe_inj] at hl⟩

/-- An element `x` is 𝓛-below an idempotent `e` if and only if `x = x * e`. -/
theorem LPreorder.le_idempotent {e : S} (h : IsIdempotentElem e) (x : S) :
    (x ≤𝓛 e) ↔ (x * e = x) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [← WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [← hru, mul_assoc, h]
  · intro hl
    exact ⟨x, by rwa [← WithOne.coe_inj] at hl⟩

/-- An element is 𝓗-below an idempotent if and only if it is a sandwich fixed point. -/
theorem HPreorder.le_idempotent {e : S} (he : IsIdempotentElem e) (x : S) :
    x ≤𝓗 e ↔ e * x * e = x := by
  constructor
  · rintro ⟨hr, hl⟩
    rw [RPreorder.le_idempotent he] at hr
    rw [LPreorder.le_idempotent he] at hl
    rw [hr, hl]
  · intro h; constructor
    · rw [← h]
      exact ⟨x * e, by simp [← WithOne.coe_mul, ← mul_assoc]⟩
    · rw [← h]
      exact ⟨e * x, by simp [← WithOne.coe_mul, mul_assoc]⟩

/-! ### Morphism preservations -/

section Morphism

variable {S T : Type*} [Semigroup S] [Semigroup T] {x y : S}
variable {F : Type*} [FunLike F S T] [MulHomClass F S T] (f : F)

/-- The 𝓡-preorder is preserved by semigroup morphisms. -/
@[simp] lemma RPreorder.map (h : x ≤𝓡 y) : f x ≤𝓡 f y := by
  obtain ⟨z, hz⟩ := h
  cases z with
  | one => simp_all
  | coe z => rw [← WithOne.coe_mul, WithOne.coe_inj] at hz; subst x; simp

/-- The 𝓛-preorder is preserved by semigroup morphisms. -/
@[simp] lemma LPreorder.map (h : x ≤𝓛 y) : f x ≤𝓛 f y := by
  obtain ⟨z, hz⟩ := h
  cases z with
  | one => simp_all
  | coe z => rw [← WithOne.coe_mul, WithOne.coe_inj] at hz; subst x; simp

/-- The 𝓙-preorder is preserved by semigroup morphisms. -/
@[simp] lemma JPreorder.map (h : x ≤𝓙 y) : f x ≤𝓙 f y := by
  obtain ⟨u, v, huv⟩ := h
  cases u <;> cases v <;> simp_all [← WithOne.coe_mul] <;> subst x <;> simp

/-- The 𝓗-preorder is preserved by semigroup morphisms. -/
@[simp] lemma HPreorder.map (h : x ≤𝓗 y) : f x ≤𝓗 f y :=
  ⟨h.1.map f, h.2.map f⟩

/-- The 𝓡 equivalence is preserved by semigroup morphisms. -/
@[simp] lemma REquiv.map (h : x 𝓡 y) : f x 𝓡 f y :=
  ⟨h.1.map f, h.2.map f⟩

/-- The 𝓛 equivalence is preserved by semigroup morphisms. -/
@[simp] lemma LEquiv.map (h : x 𝓛 y) : f x 𝓛 f y :=
  ⟨h.1.map f, h.2.map f⟩

/-- The 𝓙 equivalence is preserved by semigroup morphisms. -/
@[simp] lemma JEquiv.map (h : x 𝓙 y) : f x 𝓙 f y :=
  ⟨h.1.map f, h.2.map f⟩

/-- The 𝓗 equivalence is preserved by semigroup morphisms. -/
@[simp] lemma HEquiv.map (h : x 𝓗 y) : f x 𝓗 f y :=
  ⟨h.1.map f, h.2.map f⟩

/-- The 𝓓 equivalence is preserved by semigroup morphisms. -/
@[simp] lemma DEquiv.map (h : x 𝓓 y) : f x 𝓓 f y := by
  obtain ⟨z, hxz, hyz⟩ := h
  exact ⟨f z, hxz.map f, hyz.map f⟩

end Morphism

end Semigroup
