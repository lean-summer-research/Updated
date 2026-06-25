import Semigroup.Greens.Lemma
import Semigroup.Greens.Finite
import Semigroup.Substructure

/-!
# The Location Theorem

This file proves the Location Theorem, which states that the following
conditions are equivalent for `x y : S` where `S` is a semigroup:
  1. `x * y ∈ ⟦x⟧𝓡 ∩ ⟦y⟧𝓛`
  2. `⟦x⟧𝓡 ∩ ⟦y⟧𝓛` contains an idempotent element.

If the semigroup is finite, these conditions are equivalent to
  3. `x * y 𝓓 x` (Alternatively, `x * y 𝓓 y`) and `x 𝓓 y`

Additionally, we prove that the 𝓗-class of an idempotent element is a group,
and we define this as a subgroup of the underlying semigroup.

## Main Definitions

* `HEquiv.subgroup_of_idempotent` - Given an idempotent element `e : S`, the 𝓗-class of `e`
* `HEquiv.group_of_idempotent` - Given an idempotent element `e : S`, the H-class of `e`
as a group on the subtype `{x : S // x ∈ ⟦e⟧𝓗}`

## Main Theorems

* `DEquiv.mul_in_inter_iff_equiv` - For `x y : S` where `S` is a finite semigroup, `x * y` is in
`⟦x⟧𝓡 ∩ ⟦y⟧𝓛` iff `x 𝓓 y` and `x * y 𝓓 x`.
* `mul_in_inter_iff_exists_idempotent` - For `x y : S`, `x * y` is in `⟦x⟧𝓡 ∩ ⟦y⟧𝓛`
iff there exists an idempotent element in `⟦x⟧𝓡 ∩ ⟦y⟧𝓛`.
* `DEquiv.maximal_subgroups_equiv` - Two maximal subgroups of a 𝓓-class are isomorphic.
* `HEquiv.hClass_of_subgroup` - Every maximal subgroup is the 𝓗-class of an idempotent element.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-- In Finite semigroups, `x * y` is in the intersection of the 𝓡-class of `x` and the 𝓛-class
of `y` iff `x`, `y`, and `x * y` are 𝓓-Equivalent. -/
theorem DEquiv.mul_in_inter_iff_equiv (x y : S) [Finite S] [Pow (WithOne S) ℕ+]
  [PNatPowAssoc (WithOne S)] :
    x * y ∈ ⟦x⟧𝓡 ∩ ⟦y⟧𝓛 ↔ x 𝓓 y ∧ x * y 𝓓 x := by
  simp_all only [REquiv.set, LEquiv.set, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hr, hl⟩
    exact ⟨⟨x * y, ⟨hr.symm, hl⟩⟩, JEquiv.to_dEquiv <| REquiv.to_jEquiv hr⟩
  · rintro ⟨hj₁, hj₂⟩
    apply DEquiv.to_jEquiv at hj₁
    apply DEquiv.to_jEquiv at hj₂
    constructor
    · exact REquiv.of_rPreorder_and_jEquiv (by simp) hj₂
    · exact LEquiv.of_lPreorder_and_jEquiv (by simp) (JEquiv.trans hj₂ hj₁)

/-- `x * y` is 𝓡-equivalent to `x` and 𝓛-equivalent to `y` iff there exists an idempotent
element in the intersection of the 𝓡-class of `y` and the 𝓛-class of `x`. -/
theorem mul_in_inter_iff_exists_idempotent (x y : S) :
    x * y ∈ ⟦x⟧𝓡 ∩ ⟦y⟧𝓛 ↔ ∃ e, IsIdempotentElem e ∧ e ∈ ⟦y⟧𝓡 ∩ ⟦x⟧𝓛 := by
  constructor
  · simp_all only [REquiv.set, LEquiv.set, Set.mem_inter_iff, Set.mem_setOf_eq, IsIdempotentElem,
    and_imp]
    intro hr hl
    have heq : x * y = x * y := by rfl
    -- Mul on the right by y is a bijection from ⟦x⟧𝓛 to ⟦y⟧𝓛 which preserves 𝓗-classes
    have hsurj := hr.symm.surjOn_lClass heq
    specialize hsurj hl.symm
    rcases hsurj with ⟨w, hw, hw_eq⟩
    simp only [LEquiv.set, Set.mem_setOf_eq] at hw_eq hw
    have hwRy : w 𝓡 y := by
      rw [← hw_eq]
      apply hr.symm.bijOn_lClass_rEquiv heq hw
    use w
    refine ⟨?_, ⟨hwRy, hw⟩⟩
    -- there exists a `u` s.t. `y * u = w`
    obtain ⟨u, hu⟩ := hwRy.le
    cases u with
    | one =>
      simp only [mul_one, WithOne.coe_inj] at hu; subst hu
      exact hw_eq
    | coe u =>
      simp only [← WithOne.coe_mul, WithOne.coe_inj] at hu
      nth_rw 2 [← hu]
      rw [← mul_assoc, hw_eq, hu]
  · simp_all only [REquiv.set, LEquiv.set, Set.mem_inter_iff, Set.mem_setOf_eq,
    forall_exists_index, and_imp]
    intro e hi hr hl
    have he₁ : y = e * y := by
      have hr₁ : y ≤𝓡 e := hr.2
      have he := RPreorder.le_idempotent hi y
      rw [he] at hr₁
      exact hr₁.symm
    have he₂ : x = x * e := by
      have hl₁ : x ≤𝓛 e := hl.2
      have he := LPreorder.le_idempotent hi x
      rw [he] at hl₁
      exact hl₁.symm
    constructor
    · nth_rw 2 [he₂]
      apply REquiv.lmul_compat hr.symm
    · nth_rw 2 [he₁]
      apply LEquiv.rmul_compat hl.symm

/-- Idempotent-containing 𝓗-classes are closed under multiplication. -/
lemma HEquiv.mul_closed_of_idempotent {e x y : S} (he : IsIdempotentElem e)
    (hx : x ∈ ⟦e⟧𝓗) (hy : y ∈ ⟦e⟧𝓗) : x * y ∈ ⟦e⟧𝓗 := by
  simp_all only [set, Set.mem_setOf_eq]
  have he : ∃ e, IsIdempotentElem e ∧ e ∈ ⟦y⟧𝓡 ∩ ⟦x⟧𝓛 := by
    exact ⟨e, by simp_all [HEquiv.iff_rEquiv_and_lEquiv]⟩
  rw [← mul_in_inter_iff_exists_idempotent x y] at he
  simp_all only [iff_rEquiv_and_lEquiv, REquiv.set, LEquiv.set, Set.mem_inter_iff, Set.mem_setOf_eq]
  exact ⟨REquiv.trans he.1 hx.1, LEquiv.trans he.2 hy.2⟩

/-- For all elements in the 𝓗-class of an idempotent, that idempotent acts as a
left identity. -/
lemma HEquiv.idempotent_mul {e : S} (he : IsIdempotentElem e) {x : S} (hx : x ∈ ⟦e⟧𝓗) :
    e * x = x := by
  rw [← RPreorder.le_idempotent he]
  exact REquiv.le hx.to_rEquiv

/-- For all elements in the 𝓗-class of an idempotent, that idempotent acts as a
right identity. -/
lemma HEquiv.mul_idempotent {e : S} (he : IsIdempotentElem e) {x : S} (hx : x ∈ ⟦e⟧𝓗) :
    x * e = x := by
  rw [← LPreorder.le_idempotent he]
  exact LEquiv.le hx.to_lEquiv

/-- All idempotent elements in an 𝓗 class are equal. -/
lemma HEquiv.idempotent_eq {e x : S} (hh : x 𝓗 e)
    (he : IsIdempotentElem e) (hx : IsIdempotentElem x) : e = x := by
  have hle := hh.le.1
  have hge := hh.ge.2
  rw [RPreorder.le_idempotent he] at hle
  rw [LPreorder.le_idempotent hx] at hge
  nth_rw 1 [← hle, ← hge]

-- TODO. use REquiv.bijOn_hClass below
/-- The 𝓗-class of an idempotent element is closed under inverses. -/
private lemma HEquiv.exists_inverse_of_idempotent {e x : S}
  (he : IsIdempotentElem e) (hh : x ∈ ⟦e⟧𝓗) :
    ∃ y, y 𝓗 e ∧ x * y = e ∧ y * x = e := by
  simp only [set, Set.mem_setOf_eq] at hh
  have hr₁ : e ≤𝓡 x := by simp [hh]
  obtain ⟨y, hy⟩ := hr₁
  cases y with
  | one =>
    simp only [mul_one, WithOne.coe_inj] at hy
    subst hy
    exact ⟨x, by simp_all [IsIdempotentElem]⟩
  | coe y =>
    have heq : x * y = e := by simpa [← WithOne.coe_mul] using hy
    have hex : e * x = x := HEquiv.idempotent_mul he hh
    have hxe : x * e = x := HEquiv.mul_idempotent he hh
    -- z ↦ z * x is a bijection on the HClass of e
    have hsurj := hh.symm.to_rEquiv.surjOn_lClass hex
    have hein : e ∈ ⟦x⟧𝓛 := by simp_all
    specialize hsurj hein
    rcases hsurj with ⟨z, hz, hz_eq⟩
    simp_all only [LEquiv.set, Set.mem_setOf_eq, to_lEquiv, LEquiv.symm]
    have hez : z 𝓗 e := by
      have hl : e 𝓛 e := by simp
      have hpres := hh.symm.to_rEquiv.bijOn_lClass_pres_hClass hex hz hl
      rw [hpres]
      simp only [hz_eq, hex]
      exact hh.symm
    use z
    refine ⟨hez, ?_, hz_eq⟩
    have hl₁ : e 𝓛 e := by simp
    have hl₂ : x * z 𝓛 e := by exact (HEquiv.mul_closed_of_idempotent he hh hez).to_lEquiv
    have hinj := hh.symm.to_rEquiv.injOn_lClass hex
    specialize hinj hl₂ hl₁
    simp only at hinj
    apply hinj
    rw [mul_assoc, hz_eq, hex, hxe]

/-- The 𝓗-class of an idempotent element as a subgroup of the semigroup. -/
noncomputable def HEquiv.subgroup_of_idempotent {e : S} (he : IsIdempotentElem e) : Subgroup S where
  carrier := ⟦e⟧𝓗
  mul_mem := HEquiv.mul_closed_of_idempotent he
  one := e
  one_mem := by simp
  one_mul {x : S} (hx : x 𝓗 e) := HEquiv.idempotent_mul he hx
  mul_one {x : S} (hx : x 𝓗 e) := HEquiv.mul_idempotent he hx
  inv (x : S) := by
    have hd : Decidable (x ∈ ⟦e⟧𝓗) := by exact Classical.propDecidable (x ∈ ⟦e⟧𝓗)
    exact (if hx : x ∈ ⟦e⟧𝓗
      then Exists.choose (HEquiv.exists_inverse_of_idempotent he hx)
      else x )
  inv_not_mem := by simp_all
  inv_mem := by
    simp_all only [set, Set.mem_setOf_eq, symm, ↓reduceDIte]
    intros x hx
    have h := Classical.choose_spec (HEquiv.exists_inverse_of_idempotent he hx)
    exact h.1
  inv_mul := by
    simp_all only [set, Set.mem_setOf_eq, symm, ↓reduceDIte]
    intros x hx
    have h := Classical.choose_spec (HEquiv.exists_inverse_of_idempotent he hx)
    exact h.2.2
  mul_inv := by
    simp_all only [set, Set.mem_setOf_eq, symm, ↓reduceDIte]
    intros x hx
    have h := Classical.choose_spec (HEquiv.exists_inverse_of_idempotent he hx)
    exact h.2.1

@[simp] lemma HEquiv.subgroup_of_idempotent_carrier_def {e : S} (he : IsIdempotentElem e) :
    (HEquiv.subgroup_of_idempotent he).carrier = ⟦e⟧𝓗 := by
  rfl

/-- The 𝓗-class of a semigroup as a Group on the subtype `{x : S // x ∈ ⟦e⟧𝓗}` -/
noncomputable instance HEquiv.group_of_idempotent' {e : S} (he : IsIdempotentElem e) :
    Group ({x // x ∈ ⟦e⟧𝓗}) :=
  inferInstanceAs (Group (HEquiv.subgroup_of_idempotent he))

/-- If there exists an `x, y` in an 𝓗 class such that `x * y` remains in the 𝓗-class,
then that 𝓗 class contains an idempotent. -/
theorem HEquiv.idempotent_in_subgroup {x y : S} (h₁ : x 𝓗 y) (h₂ : x * y 𝓗 x) :
    ∃ e, e 𝓗 x ∧ IsIdempotentElem e := by
  have hh : x * y 𝓗 y := by apply HEquiv.trans h₂ h₁
  have h := mul_in_inter_iff_exists_idempotent x y
  simp_all only [REquiv.set, LEquiv.set, Set.mem_inter_iff, Set.mem_setOf_eq, to_rEquiv, to_lEquiv,
    and_self, true_iff]
  obtain ⟨e, he₁, he₂⟩ := h
  refine ⟨e, ?_, he₁⟩
  simp_all only [iff_rEquiv_and_lEquiv, LEquiv.symm, and_true]
  apply REquiv.trans he₂.1 h₁.1.symm

/-- If a 𝓓-class contains an idempotent, it contains at least one idempotent
in each 𝓡-class. -/
theorem DEquiv.idempotent_in_rClass {e x : S} (he : IsIdempotentElem e) (hx : x 𝓓 e) :
    ∃ f ∈ ⟦x⟧𝓡, IsIdempotentElem f := by
  obtain ⟨r, hr₁, hr₂⟩ := hx
  have her : r * e = r := by
    have h := LPreorder.le_idempotent he r
    rw [← h]
    exact hr₂.le
  obtain ⟨u, hu⟩ := hr₂.ge
  cases u with
  | one => exact ⟨r, by simp_all⟩
  | coe u =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hu
    refine ⟨r * u, ?_, ?_⟩
    · simp only [REquiv.set, Set.mem_setOf_eq]
      refine REquiv.trans ?_ hr₁.symm
      exact ⟨⟨u, by simp⟩, ⟨r, by simp [← WithOne.coe_mul, mul_assoc, hu, her]⟩⟩
    · simp only [IsIdempotentElem, ← mul_assoc]
      rw [mul_assoc r, hu, her]

/-- If a 𝓓-class contains an idempotent, it contains at least one idempotent
in each 𝓛-class. -/
theorem DEquiv.idempotent_in_lClass {e x : S} (he : IsIdempotentElem e) (hx : x 𝓓 e) :
    ∃ f ∈ ⟦x⟧𝓛, IsIdempotentElem f := by
  obtain ⟨r, hr₁, hr₂⟩ := hx.symm
  have her : e * r = r := by
    rw [← RPreorder.le_idempotent he r]
    exact hr₁.ge
  obtain ⟨u, hu⟩ := hr₁.le
  cases u with
  | one =>
    simp_all only [mul_one, WithOne.coe_inj, LEquiv.set, Set.mem_setOf_eq, REquiv.refl,
      LEquiv.to_dEquiv, symm]; subst hu
    use r
  | coe u =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at hu
    refine ⟨u * r, ?_, ?_⟩
    · simp only [LEquiv.set, Set.mem_setOf_eq]
      refine LEquiv.trans ⟨⟨u, by simp⟩, ⟨r, by simp [← WithOne.coe_mul, ← mul_assoc, hu, her]⟩⟩ hr₂
    · simp only [IsIdempotentElem, ← mul_assoc]
      rw [mul_assoc u, hu, mul_assoc, her]

/-- All elements within a subgroup are 𝓗-related. -/
lemma HEquiv.ofSubgroup {x y : S} {H : Subgroup S} (hx : x ∈ H) (hy : y ∈ H) : x 𝓗 y := by
  simp_all only [iff_rEquiv_and_lEquiv, REquiv, LEquiv]
  constructor <;> constructor
  · use (H.inv y * x)
    simp [← WithOne.coe_mul, ← mul_assoc, H.mul_inv hy, H.one_mul hx]
  · use (H.inv x * y)
    simp [← WithOne.coe_mul, ← mul_assoc, H.mul_inv hx, H.one_mul hy]
  · use (x * H.inv y)
    simp [← WithOne.coe_mul, mul_assoc, H.inv_mul hy, H.mul_one hx]
  · use (y * H.inv x)
    simp [← WithOne.coe_mul, mul_assoc, H.inv_mul hx, H.mul_one hy]

/-- A maximal subgroup is the 𝓗-class of an idempotent. -/
theorem HEquiv.hClass_of_subgroup {H : Subgroup S} (hH : H.IsMaximal) :
    ∃ e : S, IsIdempotentElem e ∧ H.carrier = ⟦e⟧𝓗 := by
  use H.one
  have hidem : IsIdempotentElem H.one := by
    simp only [IsIdempotentElem]
    apply H.one_mul
    exact H.one_mem
  let K := HEquiv.subgroup_of_idempotent hidem
  have hle : H ≤ K := by
    intros x hx
    simp only [subgroup_of_idempotent, set, Set.mem_setOf_eq, K]
    apply HEquiv.ofSubgroup hx H.one_mem
  refine ⟨hidem, ?_⟩
  specialize hH K hle
  rw [hH]
  simp [subgroup_of_idempotent, K]

/-- Let `e f : S` be idempotent elements.
Let `e 𝓓 f` such that we have a `s` with `e 𝓡 s` and `s 𝓛 f`.
Let `t` be the witness of `f ≤𝓛 s` such that `t * s = f`.
Then, the map `x ↦ t * x * s` is a bijection from the 𝓗-class of `e` to the 𝓗-class of `f`. -/
lemma DEquiv.bij_on_hClass {e f s t : S} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
  (hr : e 𝓡 s) (hl : s 𝓛 f) (ht : t * s = f) :
    Set.BijOn (fun x ↦ t * x * s) ⟦e⟧𝓗 ⟦f⟧𝓗 := by
  have hes : e * s = s := by
    rw [← RPreorder.le_idempotent he]
    exact hr.ge
  have hsf : s * f = s := by
    rw [← LPreorder.le_idempotent hf]
    exact hl.le
  -- `x ↦ x * s` is a bijection from ⟦e⟧𝓗 to ⟦s⟧𝓗
  obtain ⟨hs_map, hs_inj, hs_surj⟩ := hr.bijOn_hClass hes
  -- `x ↦ t * x` is a bijection from ⟦s⟧𝓗 to ⟦f⟧𝓗
  obtain ⟨ht_map, ht_inj, ht_surj⟩ := hl.bijOn_hClass ht
  refine Set.BijOn.mk ?_ ?_ ?_
  · intros x hx
    simp only [HEquiv.set, Set.mem_setOf_eq]
    have hh : x * s 𝓗 s := by specialize hs_map hx; simp_all
    specialize ht_map hh
    simpa [← mul_assoc] using ht_map
  · intros x hs y hy heq
    simp only [mul_assoc] at heq
    have heq : x * s = y * s := by exact ht_inj (hs_map hs) (hs_map hy) heq
    exact hs_inj hs hy heq
  · intros y hy
    specialize ht_surj hy
    simp only [HEquiv.set, Set.mem_image, Set.mem_setOf_eq] at ht_surj
    rcases ht_surj with ⟨z, hz, hz_eq⟩
    specialize hs_surj hz
    rcases hs_surj with ⟨w, hw, hw_eq⟩
    refine ⟨w, hw, ?_⟩
    simp_all only [HEquiv.set, Set.mem_setOf_eq]
    simp only [mul_assoc]
    rw [hw_eq, hz_eq]

/-- Let `e f : S` be idempotent elements.
Let `e 𝓓 f` such that we have a `s` with `e 𝓡 s` and `s 𝓛 f`.
Let `t` be the witness of `f ≤𝓛 s` such that `t * s = f`.
Let `u` be the witness of `e ≤𝓡 s` such that `s * u = e`.
Then, the map `x ↦ t * x * s` is a bijection which preserves multiplication (like a morphism). -/
private lemma DEquiv.bij_on_hClass_map_mul {e f s t x y : S} (_ : IsIdempotentElem e)
  (hf : IsIdempotentElem f) (hr : e 𝓡 s) (hl : s 𝓛 f) (ht : t * s = f)
  (_ : x 𝓗 e) (hy : y 𝓗 e) :
    (fun x ↦ t * x * s) x * (fun x ↦ t * x * s) y = (fun x ↦ t * x * s) (x * y) := by
  simp only
  have hsf : s * f = s := by rw [← LPreorder.le_idempotent hf]; exact hl.le
  have hidem : IsIdempotentElem (s * t) := by
    simp only [IsIdempotentElem]
    rw [← mul_assoc, mul_assoc s, ht, hsf]
  have hsty : s * t * y = y := by
    rw [← RPreorder.le_idempotent hidem]
    apply REquiv.le
    have hr₂ : s 𝓡 s * t := by
      simp only [REquiv, RPreorder.mul_right_self, and_true]
      use s
      simp [← WithOne.coe_mul, mul_assoc, ht, hsf]
    exact hy.to_rEquiv.trans (hr.trans hr₂)
  nth_rw 2 [← hsty]
  simp [← mul_assoc]

/-- For idempotents `e, f`, with `e 𝓓 f` such that `e 𝓡 s` and `s 𝓛 f` such that
`t * s = f`, the isomorphism between `⟦e⟧𝓗` and `⟦f⟧𝓗` -/
private noncomputable def DEquiv.hClass_equiv' {e f s t : S} (he : IsIdempotentElem e)
  (hf : IsIdempotentElem f) (hr : e 𝓡 s) (hl : s 𝓛 f) (ht : t * s = f) :
    HEquiv.subgroup_of_idempotent he ≃* HEquiv.subgroup_of_idempotent hf := by
  refine Subgroup.hom_of_bijOn (fun x ↦ t * x * s) (DEquiv.bij_on_hClass he hf hr hl ht) ?_
  intros w z hw hz
  exact (DEquiv.bij_on_hClass_map_mul he hf hr hl ht hw hz).symm

/-- For idempotents `e, f`, if `e 𝓓 f`, then `⟦e⟧𝓗` and `⟦f⟧𝓗` are isomorphic subgroups. -/
lemma DEquiv.hClass_equiv {e f : S} (he : IsIdempotentElem e)
  (hf : IsIdempotentElem f) (hd : e 𝓓 f) :
    Nonempty (HEquiv.subgroup_of_idempotent he ≃* HEquiv.subgroup_of_idempotent hf) := by
  obtain ⟨s, hr, hl⟩ := hd
  -- let `t` be the witness of `f ≤𝓛 s` such that `t * s = f`.
  obtain ⟨t, ht⟩ := hl.ge
  cases t with
  | one =>
    simp only [one_mul, WithOne.coe_inj] at ht; subst ht -- trivial case where `f = s`
    -- let `u` be the witness of `f ≤𝓡 e` such that `e * u = f`
    obtain ⟨u, hu⟩ := hr.ge
    cases u with
    | one => -- trivial case where `e = f`
      simp_all only [LEquiv.refl, mul_one, WithOne.coe_inj, REquiv.refl]
      have heq : HEquiv.subgroup_of_idempotent he = HEquiv.subgroup_of_idempotent hf := by congr
      rw [heq]
      apply Nonempty.intro; rfl
    | coe u =>
      simp [← WithOne.coe_mul] at hu
      -- ` f = e * u` and `e 𝓡 f`
      exact ⟨DEquiv.hClass_equiv' he hf hr hl hf⟩
  | coe t =>
    simp only [← WithOne.coe_mul, WithOne.coe_inj] at ht
    refine ⟨Subgroup.hom_of_bijOn (fun x ↦ t * x * s) (DEquiv.bij_on_hClass he hf hr hl ht) ?_⟩
    intros x y hx hy
    exact (DEquiv.bij_on_hClass_map_mul he hf hr hl ht hx hy).symm

/-- Two maximal subgroups of a 𝓓-class are isomorphic. -/
theorem DEquiv.maximal_subgroups_equiv {x y : S} {H K : Subgroup S}
  (hH : H.IsMaximal) (hK : K.IsMaximal) (hx : x ∈ H) (hy : y ∈ K) (hd : x 𝓓 y) :
    Nonempty (H ≃* K) := by
  obtain ⟨e₁, hi₁, h₁⟩ := HEquiv.hClass_of_subgroup hH
  obtain ⟨e₂, hi₂, h₂⟩ := HEquiv.hClass_of_subgroup hK
  simp only [Subgroup.mem_def, h₁, HEquiv.set, Set.mem_setOf_eq, h₂] at hx hy
  have he : e₁ 𝓓 e₂ := hx.to_dEquiv.symm.trans (hd.trans hy.to_dEquiv)
  have heq₁ : H = HEquiv.subgroup_of_idempotent hi₁ := by ext; simp [Subgroup.mem_def, h₁]
  have heq₂ : K = HEquiv.subgroup_of_idempotent hi₂ := by ext; simp [Subgroup.mem_def, h₂]
  rw [heq₁, heq₂]
  exact DEquiv.hClass_equiv hi₁ hi₂ he

end Semigroup
