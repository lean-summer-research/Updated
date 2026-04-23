import Semigroup.ReesMatrix.Defs
import Semigroup.Simple
import Semigroup.Greens.Location
import Semigroup.Idempotent

/-!
# Rees–Suschkewitsch Theorem (Simple Case)

This file proves the Rees–Suschkewitsch theorem for simple semigroups:
a finite simple semigroup is isomorphic to a Rees matrix semigroup over a group,
and conversely every Rees matrix semigroup over a group is simple.

## Main Definitions

* `Semigroup.RQuot S` — the quotient of `S` by 𝓡-equivalence.
* `Semigroup.LQuot S` — the quotient of `S` by 𝓛-equivalence.
* `Semigroup.ReesData S` — a coordinate system for expressing elements of `S` via a
  Rees matrix decomposition: an anchor idempotent `e`, row representatives `s` (one per
  𝓡-class, each 𝓛-equivalent to `e`), and column representatives `r` (one per 𝓛-class,
  each 𝓡-equivalent to `e`).
* `Semigroup.ReesData.sandwich` — the sandwich matrix `P(i,j) = r j * s i` in the
  𝓗-class group of `e`.
* `Semigroup.reesOf S` — the Rees matrix semigroup type isomorphic to a finite simple `S`.
* `Semigroup.reesEquiv S` — the explicit `MulEquiv` from `S` to `reesOf S`.

## Main Results

* `Semigroup.ReesData.decomp` — every element decomposes as `s i * g * r j`.
* `Semigroup.ReesData.unique` — the decomposition is unique.
* `Semigroup.ReesData.mulEquiv` — the multiplicative equivalence `S ≃* Rees C.sandwich`.
* `Semigroup.Rees.isSimple` — every Rees matrix semigroup (without zero) is simple.
-/

namespace Semigroup

universe u v w uS

/-! ## Quotient types for Green's relations -/

/-- The quotient of `S` by 𝓡-equivalence. -/
abbrev RQuot (S : Type*) [Semigroup S] : Type _ :=
  @Quotient S ⟨(· 𝓡 ·), REquiv.isEquivalence⟩

/-- The quotient of `S` by 𝓛-equivalence. -/
abbrev LQuot (S : Type*) [Semigroup S] : Type _ :=
  @Quotient S ⟨(· 𝓛 ·), LEquiv.isEquivalence⟩

/-! ## Rees coordinate data -/

/-- A Rees coordinate system for a semigroup `S` -/
structure ReesData (S : Type*) [Semigroup S] where
  e : S
  /-- Proof that `e` is idempotent. -/
  he : IsIdempotentElem e
  /-- Row representative: for each 𝓡-class, an element 𝓛-related to `e`. -/
  s : RQuot S → S
  /-- Column representative: for each 𝓛-class, an element 𝓡-related to `e`. -/
  r : LQuot S → S
  /-- Each row representative is 𝓛-related to `e`. -/
  hsL : ∀ i, s i 𝓛 e
  /-- Each column representative is 𝓡-related to `e`. -/
  hrR : ∀ j, r j 𝓡 e
  /-- Each row representative maps to its 𝓡-class. -/
  hsQ : ∀ i, @Quotient.mk S ⟨(· 𝓡 ·), REquiv.isEquivalence⟩ (s i) = i
  /-- Each column representative maps to its 𝓛-class. -/
  hrQ : ∀ j, @Quotient.mk S ⟨(· 𝓛 ·), LEquiv.isEquivalence⟩ (r j) = j

namespace ReesData

variable {S : Type uS} [Semigroup S] (C : ReesData S)

/-! ### Derived definitions -/

/-- The 𝓗-class of the idempotent, as a subtype. -/
abbrev HClass : Type uS := {x : S // x ∈ ⟦C.e⟧𝓗}

/-- The group structure on the 𝓗-class of the anchor idempotent. -/
noncomputable instance instGroupHClass : Group C.HClass :=
  HEquiv.group_of_idempotent' C.he

/-- 𝓡-class representatives are left-absorbed by `e`: `s i * e = s i`. -/
theorem s_mul_e (i : RQuot S) : C.s i * C.e = C.s i :=
  (LPreorder.le_idempotent C.he _).mp (C.hsL i).1

/-- 𝓛-class representatives are right-absorbed by `e`: `e * r j = r j`. -/
theorem e_mul_r (j : LQuot S) : C.e * C.r j = C.r j :=
  (RPreorder.le_idempotent C.he _).mp (C.hrR j).1

variable [Finite S] [IsSimple S]

/-- The sandwich matrix: `P(i,j) = r j * s i`, which lies in the 𝓗-class of `e`. -/
noncomputable def sandwich : RQuot S → LQuot S → C.HClass := fun i j =>
  ⟨C.r j * C.s i, by
    simp only [HEquiv.set_def, Set.mem_setOf_eq]
    rw [HEquiv.iff_rEquiv_and_lEquiv]
    constructor
    · refine REquiv.of_rPreorder_and_jEquiv ?_ (JEquiv.ofSimple ..)
      use ↑(C.r j * C.s i)
      simp[← mul_assoc, ← WithOne.coe_mul, e_mul_r]
    · refine LEquiv.of_lPreorder_and_jEquiv ?_ (JEquiv.ofSimple ..)
      use ↑(C.r j * C.s i)
      simp[← WithOne.coe_mul, mul_assoc, s_mul_e]⟩

@[simp] theorem sandwich_val (i : RQuot S) (j : LQuot S) :
    (C.sandwich i j : S) = C.r j * C.s i := rfl

/-! ### Decomposition -/

omit [Finite S] [IsSimple S] in
/-- Every element of `S` decomposes as `s i * g * r j` for some `i, j, g`. -/
theorem decomp (x : S) :
    ∃ (i : RQuot S) (j : LQuot S) (g : C.HClass), x = C.s i * ↑g * C.r j := by
  let rS : Setoid S := ⟨(· 𝓡 ·), REquiv.isEquivalence⟩
  let lS : Setoid S := ⟨(· 𝓛 ·), LEquiv.isEquivalence⟩
  use Quotient.mk rS x, Quotient.mk lS x
  have hsiR : C.s ⟦x⟧ 𝓡 x := Quotient.exact (C.hsQ _)
  have hrjL : C.r ⟦x⟧ 𝓛 x := Quotient.exact (C.hrQ _)
  have hmem := (mul_in_inter_iff_exists_idempotent (C.s ⟦x⟧) (C.r ⟦x⟧)).mpr
      ⟨C.e, C.he, (C.hrR _).symm, (C.hsL _).symm⟩
  have hH : C.s ⟦x⟧ * C.r ⟦x⟧ 𝓗 x :=
    (HEquiv.iff_rEquiv_and_lEquiv _ _).mpr ⟨hmem.1.trans hsiR, hmem.2.trans hrjL⟩
  obtain ⟨h, hh_mem, hh_eq⟩ := hmem.1.symm.surjOn_hClass rfl hH.symm
  obtain ⟨g, hg_mem, hg_eq⟩ := (C.hsL ⟦x⟧).symm.surjOn_hClass (C.s_mul_e ⟦x⟧) hh_mem
  exact ⟨⟨g, hg_mem⟩, by
    simp_all only
    rw [hg_eq, hh_eq]⟩

/-! ### Uniqueness -/

/-- The Rees decomposition is unique. -/
theorem unique (x : S) (i i' : RQuot S) (j j' : LQuot S) (g g' : C.HClass)
    (hx : x = C.s i * ↑g * C.r j) (hx' : x = C.s i' * ↑g' * C.r j') :
    i = i' ∧ j = j' ∧ g = g' := by
  let rS : Setoid S := ⟨(· 𝓡 ·), REquiv.isEquivalence⟩
  let lS : Setoid S := ⟨(· 𝓛 ·), LEquiv.isEquivalence⟩
  have hgR : (↑g : S) 𝓡 C.e := g.prop.to_rEquiv
  have hgR' : (↑g' : S) 𝓡 C.e := g'.prop.to_rEquiv
  have h_xRsi : x 𝓡 C.s i := by
    rw [hx]
    refine (REquiv.of_rPreorder_and_jEquiv RPreorder.mul_right_self
      (JEquiv.ofSimple ..)).trans ?_
    have h := REquiv.lmul_compat hgR (C.s i)
    rwa [C.s_mul_e] at h
  have h_xRsi' : x 𝓡 C.s i' := by
    rw [hx']
    refine (REquiv.of_rPreorder_and_jEquiv RPreorder.mul_right_self
      (JEquiv.ofSimple ..)).trans ?_
    have h := REquiv.lmul_compat hgR' (C.s i')
    rwa [C.s_mul_e] at h
  have hi : i = i' := by
    have := @Quotient.sound S rS _ _ (h_xRsi.symm.trans h_xRsi')
    rwa [C.hsQ, C.hsQ] at this
  have h_xLrj : x 𝓛 C.r j := by
    rw [hx]
    exact LEquiv.of_lPreorder_and_jEquiv LPreorder.mul_left_self (JEquiv.ofSimple ..)
  have h_xLrj' : x 𝓛 C.r j' := by
    rw [hx']
    exact LEquiv.of_lPreorder_and_jEquiv LPreorder.mul_left_self (JEquiv.ofSimple ..)
  have hj : j = j' := by
    have := @Quotient.sound S lS _ _ (h_xLrj.symm.trans h_xLrj')
    rwa [C.hrQ, C.hrQ] at this
  refine ⟨hi, hj, ?_⟩
  have h_eq : C.s i * ↑g * C.r j = C.s i * ↑g' * C.r j := by
    rw [← hi, ← hj] at hx'; exact hx.symm.trans hx'
  have h_sir_Rsi := ((mul_in_inter_iff_exists_idempotent (C.s i) (C.r j)).2
    ⟨C.e, C.he, (C.hrR j).symm, (C.hsL i).symm⟩).1.symm
  have mk_h_mem (g₀ : C.HClass) : C.s i * ↑g₀ ∈ ⟦C.s i⟧𝓗 := by
    have h := (mul_in_inter_iff_exists_idempotent (C.s i) (↑g₀)).2
      ⟨C.e, C.he, g₀.prop.to_rEquiv.symm, (C.hsL i).symm⟩
    exact (HEquiv.iff_rEquiv_and_lEquiv _ _).2
      ⟨h.1, h.2.trans (g₀.prop.to_lEquiv.trans (C.hsL i).symm)⟩
  exact Subtype.ext ((LEquiv.injOn_hClass (C.hsL i).symm (C.s_mul_e i)) g.prop g'.prop
    ((REquiv.injOn_hClass h_sir_Rsi rfl) (mk_h_mem g) (mk_h_mem g') h_eq))

/-! ### Forward and inverse maps -/

/-- The forward map: decompose `x` and return the Rees matrix element. -/
noncomputable def toRees (x : S) : Rees C.sandwich :=
  ⟨(C.decomp x).choose, (C.decomp x).choose_spec.choose,
  (C.decomp x).choose_spec.choose_spec.choose⟩

/-- The inverse map: given a Rees element `⟨i, j, g⟩`, return `s i * g * r j`. -/
noncomputable def fromRees (z : Rees C.sandwich) : S :=
  C.s z.i * ↑z.g * C.r z.j

private theorem toRees_spec (x : S) :
    x = C.s (C.toRees x).i * ↑(C.toRees x).g * C.r (C.toRees x).j :=
  (C.decomp x).choose_spec.choose_spec.choose_spec

/-! ### The multiplicative equivalence -/

/-- The multiplicative equivalence `S ≃* Rees C.sandwich`. -/
noncomputable def mulEquiv : S ≃* Rees C.sandwich where
  toFun := C.toRees
  invFun := C.fromRees
  left_inv x := (C.toRees_spec x).symm
  right_inv z := by
    obtain ⟨hi, hj, hg⟩ := C.unique _ _ z.i _ z.j _ z.g (C.toRees_spec _) rfl
    exact Rees.ext (hi := hi) (hj := hj) (hg := hg)
  map_mul' x y := by
    have hx := C.toRees_spec x; have hy := C.toRees_spec y
    have hcoe : ∀ (a b : C.HClass), (↑(a * b) : S) = ↑a * ↑b := fun _ _ => rfl
    have hPval : ∀ i j, (↑(C.sandwich i j) : S) = C.r j * C.s i := fun _ _ => rfl
    have h_cand : x * y = C.s (C.toRees x).i *
        ↑((C.toRees x).g * C.sandwich (C.toRees y).i (C.toRees x).j * (C.toRees y).g) *
        C.r (C.toRees y).j := by
      calc x * y
          = (C.s (C.toRees x).i * ↑(C.toRees x).g * C.r (C.toRees x).j) *
            (C.s (C.toRees y).i * ↑(C.toRees y).g * C.r (C.toRees y).j) := by
              conv_lhs => rw [hx, hy]
          _ = C.s (C.toRees x).i *
              ↑((C.toRees x).g * C.sandwich (C.toRees y).i (C.toRees x).j * (C.toRees y).g) *
              C.r (C.toRees y).j := by simp only [hcoe, hPval, mul_assoc]
    obtain ⟨hi, hj, hg⟩ := C.unique _ _ _ _ _ _ _ (C.toRees_spec (x * y)) h_cand
    change C.toRees (x * y) = C.toRees x * C.toRees y
    have : C.toRees x * C.toRees y =
        ⟨(C.toRees x).i, (C.toRees y).j,
         (C.toRees x).g * C.sandwich (C.toRees y).i (C.toRees x).j * (C.toRees y).g⟩ := rfl
    rw [this]
    exact Rees.ext (hi := hi) (hj := hj) (hg := hg)

/-! ### Construction from simplicity -/

/-- Construct a `ReesData` for a finite simple semigroup. -/
noncomputable def ofSimple [Inhabited S] : ReesData S :=
  let e := (default : S) ^ (exists_idempotent_pow (default : S)).choose
  have he : IsIdempotentElem e := (exists_idempotent_pow (default : S)).choose_spec
  let h_r : ∀ j : LQuot S, ∃ z : S, z 𝓡 e ∧
      @Quotient.mk S ⟨(· 𝓛 ·), LEquiv.isEquivalence⟩ z = j := fun j => by
    obtain ⟨y, rfl⟩ := Quotient.exists_rep j
    obtain ⟨z, hzR, hzL⟩ : e 𝓓 y := DEquiv.ofSimple e y
    exact ⟨z, REquiv.symm hzR, Quotient.sound hzL⟩
  let h_s : ∀ i : RQuot S, ∃ z : S, z 𝓛 e ∧
      @Quotient.mk S ⟨(· 𝓡 ·), REquiv.isEquivalence⟩ z = i := fun i => by
    obtain ⟨y, rfl⟩ := Quotient.exists_rep i
    obtain ⟨z, hzR, hzL⟩ : y 𝓓 e := DEquiv.ofSimple y e
    exact ⟨z, hzL, Quotient.sound hzR.symm⟩
  { e := e
    he := he
    s := fun i => Classical.choose (h_s i)
    r := fun j => Classical.choose (h_r j)
    hsL := fun i => (Classical.choose_spec (h_s i)).1
    hrR := fun j => (Classical.choose_spec (h_r j)).1
    hsQ := fun i => (Classical.choose_spec (h_s i)).2
    hrQ := fun j => (Classical.choose_spec (h_r j)).2 }

end ReesData

/-! ## Top-level API -/

section ReesTheorem

variable {S : Type uS} [Finite S] [Semigroup S] [IsSimple S] [Inhabited S]

open Semigroup

/-- The Rees matrix semigroup type that is isomorphic to a finite simple semigroup `S`. -/
noncomputable abbrev reesOf (S : Type uS) [Finite S] [Semigroup S] [IsSimple S]
    [Inhabited S] : Type uS :=
  Rees (ReesData.ofSimple (S := S)).sandwich

/-- The explicit multiplicative equivalence from `S` to its Rees matrix semigroup. -/
noncomputable def reesEquiv (S : Type uS) [Finite S] [Semigroup S] [IsSimple S]
    [Inhabited S] : S ≃* reesOf S :=
  (ReesData.ofSimple (S := S)).mulEquiv

end ReesTheorem

/-! ## Rees semigroup is simple -/

section ReesIsSimple

open Semigroup MulTwoSidedIdeal

variable {I : Type*} {J : Type*} {G : Type*} [Group G] (P : I → J → G)

/-- Every Rees matrix semigroup (without zero) over a group is simple:
for any element `a`, the two-sided ideal generated by `a` is the whole semigroup. -/
theorem Rees.isSimple [Nonempty I] [Nonempty J] :
    ∀ (x y : Rees P), ∃ (s t : Rees P), s * x * t = y := by
  intro ⟨ix, jx, gx⟩ ⟨iy, jy, gy⟩
  exact ⟨⟨iy, jx, gy * (P ix jx)⁻¹ * gx⁻¹ * (P ix jx)⁻¹⟩, ⟨ix, jy, 1⟩, by simp [Rees.mul_def]⟩

/-- A Rees matrix semigroup is simple in the ideal-theoretic sense:
every two-sided ideal is either empty or the whole semigroup. -/
instance Rees.instIsSimple [Nonempty I] [Nonempty J] :
    IsSimple (Rees P) where
  j_total := by
    intro x y
    obtain ⟨s, t, hst⟩ := Rees.isSimple P y x
    exact ⟨↑s, ↑t, by simp [← WithOne.coe_mul, hst]⟩

end ReesIsSimple

end Semigroup
