import Semigroup.ReesMatrix.Defs
import Semigroup.Simple
import Semigroup.Greens.Location
import Semigroup.Greens.Finite
import Semigroup.Ideal.Basic

/-!
# Rees–Suschkewitsch Theorem (0-Simple Case)

This file proves the backward direction of the Rees–Suschkewitsch theorem for
0-simple semigroups, and contains the (partial, sorry'd) forward direction.

## Main Results

* `Semigroup.ReesZero.instIsZeroSimple` — a regular Rees matrix semigroup
  with zero is 0-simple (backward direction).
* `Semigroup.zero_simple_implies_reesZero` — the forward direction.
-/

namespace Semigroup

open Semigroup MulTwoSidedIdeal

/-! ## Backward direction: Regular Rees Zero → 0-Simple -/

section ReesZeroBackward

variable {I : Type*} {J : Type*} {G : Type*} [Group G]

/-- **Rees–Suschkewitsch Theorem for 0-simple semigroups (backward direction).**
A regular Rees matrix semigroup with zero is 0-simple: for any nonzero elements
`x, y`, there exist `s, t` such that `s * x * t = y`. -/
instance ReesZero.instIsZeroSimple
    (P : I → J → WithZero G)
    [Nonempty I] [Nonempty J]
    (hrow : ∀ i : I, ∃ j : J, P i j ≠ 0)
    (hcol : ∀ j : J, ∃ i : I, P i j ≠ 0) : IsZeroSimple (Option (ReesZero P)) where
  exists_nonzero_mul := by
    obtain ⟨j₀, hj₀⟩ := hrow (Classical.arbitrary I)
    rw [WithZero.ne_zero_iff_exists] at hj₀
    obtain ⟨g₀, hg₀⟩ := hj₀
    refine ⟨some ⟨Classical.arbitrary I, j₀, 1⟩,
            some ⟨Classical.arbitrary I, j₀, 1⟩, ?_⟩
    change ¬ (some _ * some _ = none)
    rw [ReesZero.mul_def, ← hg₀]
    exact Option.isSome_iff_ne_none.mp rfl
  ideal_trivial := by
    intro K
    by_cases hK_ne : K = ∅
    · exact Or.inl hK_ne
    · right
      by_cases hK_has_nonzero : ∃ x : ReesZero P, (some x) ∈ K
      · right
        obtain ⟨x₀, hx₀⟩ := hK_has_nonzero
        have hK_all : ∀ a : Option (ReesZero P), a ∈ K := by
          intro a
          rcases a with (_ | a)
          · -- 0 ∈ K: none * some x₀ = none, and K is closed under left mult
            have h0 : (none : Option (ReesZero P)) * some x₀ ∈ K :=
              K.mul_mem_mem hx₀ none
            simpa using h0
          · -- For any nonzero a, show a ∈ K by finding s, t with s * x₀ * t = a
            obtain ⟨j', hj'⟩ := hrow x₀.i
            obtain ⟨i', hi'⟩ := hcol x₀.j
            rw [WithZero.ne_zero_iff_exists] at hj' hi'
            obtain ⟨pj, hpj⟩ := hj'
            obtain ⟨pi, hpi⟩ := hi'
            let s : Option (ReesZero P) := some ⟨a.i, j', x₀.g⁻¹ * pj⁻¹⟩
            let t : Option (ReesZero P) := some ⟨i', a.j, pi⁻¹ * a.g⟩
            have h1 : s * some x₀ ∈ K := K.mul_mem_mem hx₀ s
            have h2 : s * some x₀ * t ∈ K := K.mem_mul_mem h1 t
            convert h2 using 1
            simp only [s, t, ReesZero.mul_def, ← hpj, ← hpi]
            congr 1; simp [mul_assoc]
        exact SetLike.ext (fun a => ⟨fun _ => trivial, fun _ => hK_all a⟩)
      · left
        push Not at hK_has_nonzero
        ext a; simp only [Set.mem_singleton_iff]
        constructor
        · intro ha
          rcases a with (_ | a)
          · rfl
          · exact absurd ha (hK_has_nonzero a)
        · intro ha; rw [ha]
          obtain ⟨x, hx⟩ := MulTwoSidedIdeal.exists_mem_of_ne_empty hK_ne
          rcases x with (_ | x)
          · exact hx
          · exact absurd hx (hK_has_nonzero x)

end ReesZeroBackward

/-! ## Forward direction: 0-Simple → Rees Zero (WIP, contains sorry) -/

section ReesZeroForward

universe uS

variable {S : Type uS} [Finite S] [SemigroupWithZero S] [IsZeroSimple S] [Inhabited S]

/-- **Rees–Suschkewitsch Theorem for 0-simple semigroups (forward direction).**
A 0-simple semigroup is isomorphic to a regular Rees matrix semigroup with zero -/
theorem zero_simple_implies_reesZero (h : ∃ x : S, x ≠ 0) :
    ∃ (I J G : Type uS) (_ : Group G) (P : I → J → WithZero G),
    Nonempty (S ≃* Option (ReesZero P)) := by
  sorry

end ReesZeroForward

end Semigroup
