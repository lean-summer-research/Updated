import Semigroup.Ideal.Defs
import Semigroup.Ideal.Basic
import Semigroup.Ideal.Green
import Semigroup.Greens.Finite

/-!
# Simple and 0-Simple Semigroups

This file defines simple and 0-simple semigroups and proves basic properties.

## Main Definitions

* `IsSimple` — a class for semigroups where all elements are 𝓙-related (no proper ideals).
* `IsZeroSimple` — a class for semigroups with zero where `S² ≠ 0` and every ideal
  is trivial.
* `mulImage` — `S²`, the set of all products `a * b` with `a, b ∈ S`.

## Main Results

* `IsSimple.ideal_trivial` — in a simple semigroup, every nonempty ideal is `⊤`.
* `JPreorder.ofZeroSimple` — in a 0-simple semigroup, `x ≤𝓙 y` for all nonzero `y`.
* `JEquiv.ofZeroSimple` — in a 0-simple semigroup, all nonzero elements are 𝓙-related.
* `DEquiv.ofZeroSimple` — in a finite 0-simple semigroup, all nonzero elements are 𝓓-related.
* `zero_simple_mulImage_eq_univ` — if `S` is 0-simple then `S² = S`.
-/

/-- A simple semigroup is one in which every element is 𝓙-above every other,
i.e. there is a single 𝓙-class. Equivalently, the semigroup has no proper
two-sided ideals. -/
class IsSimple (S : Type*) [Semigroup S] : Prop where
  /-- In a simple semigroup, `x ≤𝓙 y` for all `x y`. -/
  j_total : ∀ x y : S, x ≤𝓙 y

namespace Semigroup
variable {S : Type*} [Semigroup S] [IsSimple S]

/-- In a simple semigroup, any element is 𝓙-below any other. -/
@[simp] lemma JPreorder.ofSimple (x y : S) : x ≤𝓙 y := IsSimple.j_total x y

/-- In a simple semigroup, all elements are 𝓙-related. -/
@[simp] lemma JEquiv.ofSimple (x y : S) : x 𝓙 y :=
  ⟨IsSimple.j_total x y, IsSimple.j_total y x⟩

/-- In a finite simple semigroup, all elements are 𝓓-related. -/
@[simp] lemma DEquiv.ofSimple [Finite S] [Pow (WithOne S) ℕ+] [PNatPowAssoc (WithOne S)] (x y : S) :
    x 𝓓 y :=
  JEquiv.to_dEquiv <| JEquiv.ofSimple x y

/-- In a simple semigroup, every nonempty two-sided ideal is the whole semigroup. -/
theorem IsSimple.ideal_trivial (I : MulTwoSidedIdeal S) (hI : I ≠ ∅) : I = ⊤ := by
  ext x
  simp only [MulTwoSidedIdeal.mem_top, iff_true]
  obtain ⟨y, hy⟩ := MulTwoSidedIdeal.exists_mem_of_ne_empty hI
  exact JPreorder.le_in_mulTwoSidedIdeal hy (JPreorder.ofSimple x y)

end Semigroup

/-- A semigroup with zero is **0-simple** if `S² ≠ 0` and every ideal is `∅`, `{0}`, or `S`. -/
class IsZeroSimple (S : Type*) [SemigroupWithZero S] : Prop where
  /-- There exist elements whose product is nonzero. -/
  exists_nonzero_mul : ∃ a b : S, a * b ≠ 0
  /-- Every two-sided ideal is trivial. -/
  ideal_trivial : ∀ (I : MulTwoSidedIdeal S), I = ∅ ∨ (I : Set S) = ({0} : Set S) ∨ I = ⊤

namespace Semigroup
variable {S : Type*} [SemigroupWithZero S] [IsZeroSimple S]

/-- In a 0-simple semigroup, `x ≤𝓙 y` for every `x` and every nonzero `y`. -/
theorem JPreorder.ofZeroSimple (x y : S) (hy : y ≠ 0) : x ≤𝓙 y := by
  have h_ideal := IsZeroSimple.ideal_trivial (MulTwoSidedIdeal.ofSet {y})
  have hy_mem : y ∈ MulTwoSidedIdeal.ofSet {y} := by
    simp [MulTwoSidedIdeal.mem_ofSet]
  rcases h_ideal with hempty | hsingleton | htop
  · rw [hempty] at hy_mem; exact absurd hy_mem (by contradiction)
  · have : y ∈ ({0} : Set S) := hsingleton ▸ hy_mem
    exact absurd (Set.mem_singleton_iff.mp this) hy
  · have hx_mem : x ∈ (⊤ : MulTwoSidedIdeal S) := MulTwoSidedIdeal.mem_top
    rw [← htop] at hx_mem
    rwa [JPreorder.iff_in_mulTwoSidedIdeal] at hx_mem

/-- In a 0-simple semigroup, all nonzero elements are 𝓙-related. -/
theorem JEquiv.ofZeroSimple (x y : S) (hx : x ≠ 0) (hy : y ≠ 0) : x 𝓙 y :=
  ⟨JPreorder.ofZeroSimple x y hy, JPreorder.ofZeroSimple y x hx⟩

/-- In a finite 0-simple semigroup, all nonzero elements are 𝓓-related. -/
theorem DEquiv.ofZeroSimple [Finite S] [Pow (WithOne S) ℕ+] [PNatPowAssoc (WithOne S)]
    (x y : S) (hx : x ≠ 0) (hy : y ≠ 0) : x 𝓓 y :=
  JEquiv.to_dEquiv <| JEquiv.ofZeroSimple x y hx hy

end Semigroup


/-! ## 0-Simple Semigroups and S² -/

section zero_simple

variable (S : Type*)

open Pointwise

/-- `S²` is the set of all products `a * b` with `a, b ∈ S`. -/
abbrev mulImage [Semigroup S] : Set S := (Set.univ : Set S) * (Set.univ : Set S)

open MulTwoSidedIdeal

/-- `S²` is a two-sided ideal. -/
def mulImageIdeal [Semigroup S] : MulTwoSidedIdeal S where
  carrier := mulImage S
  mem_mul_mem := by
    intro x hx y
    obtain ⟨a, _, b, _, rfl⟩ := Set.mem_mul.1 hx
    exact Set.mem_mul.2 ⟨a, Set.mem_univ _, b * y, Set.mem_univ _, (mul_assoc _ _ _).symm⟩
  mul_mem_mem := by
    intro x hx y
    obtain ⟨a, _, b, _, rfl⟩ := Set.mem_mul.1 hx
    exact Set.mem_mul.2 ⟨y * a, Set.mem_univ _, b, Set.mem_univ _, mul_assoc _ _ _⟩

lemma mulImage_ne_singleton_zero_0simple [SemigroupWithZero S] [IsZeroSimple S] :
    (mulImage S : Set S) ≠ {0} := by
  obtain ⟨a, b, hab_ne⟩ := IsZeroSimple.exists_nonzero_mul (S := S)
  intro h_eq
  have : a * b ∈ mulImage S := Set.mul_mem_mul (Set.mem_univ _) (Set.mem_univ _)
  rw [h_eq, Set.mem_singleton_iff] at this
  exact hab_ne this

/-- If `S` is 0-simple then `S² = S`. -/
theorem zero_simple_mulImage_eq_univ [SemigroupWithZero S] [IsZeroSimple S] :
    (mulImage S : Set S) = Set.univ := by
  obtain ⟨a, b, hab_ne⟩ := IsZeroSimple.exists_nonzero_mul (S := S)
  have h_prop := IsZeroSimple.ideal_trivial (S := S)
  have hab_in : a * b ∈ (mulImage S : Set S) :=
    Set.mul_mem_mul (Set.mem_univ _) (Set.mem_univ _)
  rcases h_prop (mulImageIdeal S) with heq_empty | heq_singleton | heq_top
  · have hset : (mulImageIdeal S : Set S) = (∅ : Set S) :=
      congrArg (fun (K : MulTwoSidedIdeal S) => (K : Set S)) heq_empty
    change mulImage S = ∅ at hset; rw [hset] at hab_in; exact hab_in.elim
  · exact absurd heq_singleton (mulImage_ne_singleton_zero_0simple S)
  · have hset : (mulImageIdeal S : Set S) = Set.univ :=
      congrArg (fun (K : MulTwoSidedIdeal S) => (K : Set S)) heq_top
    change mulImage S = Set.univ at hset; exact hset

end zero_simple
