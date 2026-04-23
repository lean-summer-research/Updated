import Semigroup.Ideal.Defs

/-!
# Rees Congruence and Quotient Semigroups

Given an ideal `I` of a semigroup `S`, the **Rees congruence** is the equivalence relation
where `a ~ b` iff `a = b` or both `a, b ∈ I`. The quotient `S / I` is again a semigroup.

## Main Definitions

* `ReesCon` — the Rees congruence on a semigroup with respect to a two-sided ideal.
* `ReesCon.Con` — the Rees congruence as a `Con`.
* `ReesCon.Quotient` — the quotient semigroup `S / I`.
* `ReesCon.mulHom` — the canonical semigroup homomorphism `S →ₙ* S / I`.
* `ReesCon.monoidHom` — the canonical monoid homomorphism `M →* M / I`.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-- The Rees congruence: `x ~ y` iff `x = y` or both lie in `I`. -/
def ReesCon (I : MulTwoSidedIdeal S) (x y : S) : Prop := x = y ∨ (x ∈ I ∧ y ∈ I)

private lemma ReesCon.refl (I : MulTwoSidedIdeal S) (x : S) : ReesCon I x x := Or.inl rfl

private lemma ReesCon.symm (I : MulTwoSidedIdeal S) {x y : S} (h : ReesCon I x y) :
    ReesCon I y x := by
  rcases h with rfl | ⟨h₁, h₂⟩ <;> simp_all [ReesCon]

private lemma ReesCon.trans (I : MulTwoSidedIdeal S) {x y z : S}
  (hxy : ReesCon I x y) (hyz : ReesCon I y z) :
    ReesCon I x z := by
  rcases hxy with rfl | ⟨hx, _⟩
  · exact hyz
  · rcases hyz with rfl | ⟨_, hz⟩ <;> exact Or.inr ⟨hx, by assumption⟩

/-- The Rees congruence is compatible with multiplication. -/
private lemma ReesCon.mul' (I : MulTwoSidedIdeal S) {w x y z : S}
  (hwx : ReesCon I w x) (hyz : ReesCon I y z) :
    ReesCon I (w * y) (x * z) := by
  simp only [ReesCon] at *
  rcases hwx with rfl | ⟨hw, hx⟩ <;> rcases hyz with rfl | ⟨hy, hz⟩
  · left; rfl
  · right; exact ⟨MulTwoSidedIdeal.mul_left_mem hy, MulTwoSidedIdeal.mul_left_mem hz⟩
  · right; exact ⟨MulTwoSidedIdeal.mul_right_mem hw, MulTwoSidedIdeal.mul_right_mem hx⟩
  · right; exact ⟨MulTwoSidedIdeal.mul_left_mem hy, MulTwoSidedIdeal.mul_left_mem hz⟩

private instance ReesCon.equiv (I : MulTwoSidedIdeal S) : Equivalence (ReesCon I) where
  refl := ReesCon.refl I
  symm := ReesCon.symm I
  trans := ReesCon.trans I

/-- The Rees congruence as a `Con`. -/
instance ReesCon.Con (I : MulTwoSidedIdeal S) : Con S where
  r := ReesCon I
  iseqv := ReesCon.equiv I
  mul' := ReesCon.mul' I

@[simp] lemma ReesCon.Con_def (I : MulTwoSidedIdeal S) (x y : S) :
    (ReesCon.Con I) x y ↔ x = y ∨ (x ∈ I ∧ y ∈ I) := Iff.rfl

/-- The quotient semigroup `S / I`. -/
abbrev ReesCon.Quotient (I : MulTwoSidedIdeal S) := (ReesCon.Con I).Quotient

instance ReesCon.QuotSemigroup (I : MulTwoSidedIdeal S) : Semigroup (ReesCon.Quotient I) :=
  (ReesCon.Con I).semigroup

/-- The canonical semigroup homomorphism `S →ₙ* S / I`. -/
def ReesCon.mulHom (I : MulTwoSidedIdeal S) : S →ₙ* ReesCon.Quotient I := (ReesCon.Con I).mkMulHom

variable {M : Type*} [Monoid M]

instance ReesCon.QuotMonoid (I : MulTwoSidedIdeal M) : Monoid (ReesCon.Quotient I) :=
  (ReesCon.Con I).monoid

/-- The canonical monoid homomorphism `M →* M / I`. -/
def ReesCon.monoidHom (I : MulTwoSidedIdeal M) : M →* ReesCon.Quotient I := (ReesCon.Con I).mk'

/-- Two elements are identified by the Rees congruence iff they are equal or both in `I`. -/
@[simp] lemma ReesCon.mk_eq_mk_iff {I : MulTwoSidedIdeal S} {x y : S} :
    (ReesCon.mulHom I) x = (ReesCon.mulHom I) y ↔ x = y ∨ (x ∈ I ∧ y ∈ I) := by
  change (ReesCon.Con I).toQuotient x = (ReesCon.Con I).toQuotient y ↔ _
  rw [Con.eq]; rfl

/-- The canonical semigroup homomorphism `S →ₙ* S / I` is surjective. -/
lemma ReesCon.mulHom_surjective (I : MulTwoSidedIdeal S) :
    Function.Surjective (ReesCon.mulHom I) := Quot.exists_rep

end Semigroup
