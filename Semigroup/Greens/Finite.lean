import Mathlib.Data.Fintype.Option
import Semigroup.Greens.Basic
import Semigroup.SemigroupIdempotentPow

/-!
# Finite Semigroups and Green's Relations

This file proves theorems about Green's relations in finite semigroups.

## Main theorems

* `Semigroup.dEquiv_iff_jEquiv` - `x 𝓓 y ↔ x 𝓙 y`.
* `Semigroup.REquiv.of_rPreorder_and_jEquiv` - If `x 𝓙 y` and `x ≤𝓡 y`, then `x 𝓡 y`.
* `Semigroup.LEquiv.of_lPreorder_and_jEquiv` - If `x 𝓙 y` and `x ≤𝓛 y`, then `x 𝓛 y`.
* `Semigroup.HEquiv.of_eq_sandwich` - If `x = u * x * v`, then `x 𝓗 u * x ∧ x 𝓗 x * v`.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S] [Finite S] [Pow (WithOne S) ℕ+] [PNatPowAssoc (WithOne S)]
  {x y u v : S}

/-! ### The D-J Theorem for Finite Semigroups -/

/-- If `S` is finite, then `WithOne S` is also finite. -/
instance _root_.WithOne.finite : Finite (WithOne S) := inferInstanceAs (Finite (Option S))

/-- In finite semigroups, 𝓙-equivalence implies 𝓓-equivalence. -/
@[simp] lemma JEquiv.to_dEquiv (hj : x 𝓙 y) : x 𝓓 y := by
  have hj₁ := hj
  obtain ⟨⟨s, t, ha⟩, ⟨u, v, hb⟩⟩ := hj₁
  have hab : s * u * x * (v * t) = ↑x := by grind
  obtain ⟨k, ⟨l, ⟨hkne, hlne, heq₁, heq₂⟩⟩⟩ := Monoid.exists_pow_sandwich_eq_self hab
  cases v with
  | one =>
    use x
    simp only [mul_one, one_mul, REquiv.refl, true_and] at ⊢ hb heq₂ hab
    refine ⟨?_, by use u⟩
    use (s * u)^(k-1) * s
    have hk : k - 1 + 1 = k := by exact Nat.succ_pred_eq_of_ne_zero hkne
    simp_rw [← hb, ← mul_assoc, mul_assoc _ s u, ← _root_.pow_succ, hk]
    simp [heq₁]
  | coe v =>
    use x * v
    simp only [REquiv, RPreorder.mul_right_self, and_true, LEquiv]
    constructor
    · use t * (v * t) ^ (l - 1) -- `x ≤𝓡 x * v`
      rw [WithOne.coe_mul, ← mul_assoc, mul_assoc ↑x ↑v t]
      rw [mul_assoc ↑x (↑v * t), ← pow_succ']
      have hl : l - 1 + 1 = l := by exact Nat.succ_pred_eq_of_ne_zero hlne
      rw [hl, heq₂]
    · refine ⟨?_, ⟨u, by simp [← mul_assoc, hb]⟩⟩
      use (s * u)^(k-1) * s -- `x * v ≤𝓛 y`
      rw [← hb]
      have hk : k - 1 + 1 = k := by exact Nat.succ_pred_eq_of_ne_zero hkne
      conv => lhs; rw [← mul_assoc, ← mul_assoc, mul_assoc _ s u]
      rw [WithOne.coe_mul, ← _root_.pow_succ, hk, heq₁]

/-- In finite semigroups, the 𝓓-relation equals the 𝓙-relation. -/
theorem dEquiv_iff_jEquiv : x 𝓓 y ↔ x 𝓙 y := ⟨DEquiv.to_jEquiv, JEquiv.to_dEquiv⟩

/-!
### Properties relating 𝓙, 𝓛, and 𝓡
This section shows how 𝓙-equivalence "strengthens"
𝓡 and 𝓛 preorders to equivalences in finite semigroups.
-/

/-- In finite semigroups, 𝓙-equivalence with a right product gives 𝓡-equivalence. -/
lemma REquiv.of_jEquiv_mul_right (hj : x 𝓙 x * y) : x 𝓡 x * y := by
  obtain ⟨⟨u, v, hxy⟩, _⟩ := hj
  rw [WithOne.coe_mul, ← mul_assoc, mul_assoc] at hxy
  obtain ⟨_, n, _, hneq, _, ha ⟩ := Monoid.exists_pow_sandwich_eq_self hxy
  simp only [REquiv, RPreorder.mul_right_self, and_true]
  use v * (↑y * v) ^ (n - 1)
  simp_rw [WithOne.coe_mul, ← mul_assoc, mul_assoc ↑x ↑y v]
  rw [mul_assoc ↑x (↑y * v), ← pow_succ']
  have hl : n - 1 + 1 = n := by exact Nat.succ_pred_eq_of_ne_zero hneq
  rw [hl, ha]

/-- In finite semigroups, 𝓙-equivalence with a left product gives 𝓛-equivalence. -/
lemma LEquiv.of_jEquiv_mul_left (hj : x 𝓙 y * x) : x 𝓛 y * x := by
  obtain ⟨⟨u, v, hxy⟩, _⟩ := hj
  rw [WithOne.coe_mul, ← mul_assoc] at hxy
  obtain ⟨n, _, hneq, _, ha, _⟩ := Monoid.exists_pow_sandwich_eq_self hxy
  simp only [LEquiv, LPreorder.mul_left_self, and_true]
  use (u * ↑y) ^ (n - 1) * u
  simp_rw [WithOne.coe_mul, ← mul_assoc, mul_assoc _ u, ← _root_.pow_succ]
  have hl : n - 1 + 1 = n := by exact Nat.succ_pred_eq_of_ne_zero hneq
  rw [hl, ha]

/-- In finite semigroups, 𝓙-equivalence strengthens the 𝓡-preorder to 𝓡-equivalence. -/
theorem REquiv.of_rPreorder_and_jEquiv (hr : x ≤𝓡 y) (hj : x 𝓙 y) : x 𝓡 y := by
  obtain ⟨z, hz⟩ := hr
  cases z with
  | one =>
    have heq : x = y := by simp_all
    subst x; simp
  | coe z =>
    have heq : y * z = x := by
      rw [← WithOne.coe_inj, WithOne.coe_mul]
      exact hz
    subst x
    exact (REquiv.of_jEquiv_mul_right hj.symm).symm

/-- In finite semigroups, 𝓙-equivalence strengthens the 𝓛-preorder to 𝓛-equivalence. -/
theorem LEquiv.of_lPreorder_and_jEquiv (hl : x ≤𝓛 y) (hj : x 𝓙 y) : x 𝓛 y := by
  obtain ⟨z, hz⟩ := hl
  cases z with
  | one =>
    have heq : x = y := by simp_all
    subst x; simp
  | coe z =>
    have heq : z * y = x := by
      rwa [← WithOne.coe_inj, WithOne.coe_mul]
    subst x
    exact (LEquiv.of_jEquiv_mul_left hj.symm).symm

/-! ### Theorems about 𝓗 -/

/-- In finite semigroups, an element sandwiched between two factors is 𝓗-related to its
left and right partial products. -/
theorem HEquiv.of_eq_sandwich (h : u * x * v = x) : x 𝓗 u * x ∧ x 𝓗 x * v := by
  simp only [iff_rEquiv_and_lEquiv]
  constructor <;> constructor
  · apply REquiv.of_rPreorder_and_jEquiv ⟨v, by simpa [← WithOne.coe_mul]⟩
    simp only [JEquiv, LPreorder.mul_left_self, LPreorder.to_jPreorder, and_true]
    exact ⟨1, ↑v, by simpa [← WithOne.coe_mul]⟩
  · apply LEquiv.of_jEquiv_mul_left
    simp only [JEquiv, LPreorder.mul_left_self, LPreorder.to_jPreorder, and_true]
    exact ⟨1, v, by simpa [← WithOne.coe_mul]⟩
  · apply REquiv.of_jEquiv_mul_right
    simp only [JEquiv, RPreorder.mul_right_self, RPreorder.to_jPreorder, and_true]
    exact ⟨u, 1, by simpa [← WithOne.coe_mul, ← mul_assoc]⟩
  · apply LEquiv.of_lPreorder_and_jEquiv ⟨u, by simpa [← WithOne.coe_mul, ← mul_assoc]⟩
    simp only [JEquiv, RPreorder.mul_right_self, RPreorder.to_jPreorder, and_true]
    exact ⟨u, 1, by simpa [← WithOne.coe_mul, ← mul_assoc]⟩

end Semigroup
