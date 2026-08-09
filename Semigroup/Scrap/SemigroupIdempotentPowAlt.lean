
/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/

module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Logic.Denumerable
public import Mathlib.Tactic.PNatToNat
public import Mathlib.Tactic.Ring.RingNF
public import Semigroup.Scrap.PNatPowAssoc -- this replaces Mathlib's PNatPowAssoc because i am working in a different environment

/-!
# Idempotent Elements in Finite Semigroups

This file defines properties related to idempotent elements in finite semigroups and monoids.

This alternative version uses Fintype to obtain a more constructive version of the main result:
we prove that in any finite semigroup S, if x ∈ S,
then there is an idempotent x^m such that m ≤ |S|.

## Main theorems (modify these for Fintype)

* `Semigroup.exists_idempotent_ppow` - In finite semigroups,
  `∀ x, ∃ (m : ℕ+), IsIdempotentElem (x ^ m)`
* `Monoid.exists_idempotent_pow` - `∃ (n : ℕ), IsIdempotentElem (x ^ n) ∧ n ≠ 0` in finite monoids.
* `Monoid.exists_pow_sandwich_eq_self` - In finite monoids, if `a = x * a * y`, then there exists
 positive powers `n₁` and `n₂` such that `x ^ n₁ * a = a` and `a * y ^ n₂ = a`.

## Changes
`ppow_suc_eq`
- moved outside of the semigroup namespace
- changed `S` to `M` to follow variable conventions (it's a magma, not a semigroup)
`exists_lt_map_eq_of_card_lt`
- moved in the Fintype namespace (resolved unused instance issues)
- changed `S` to `α` to follow variable conventions (its an arbitrary type, not a semigroup)
- changed the comment to a doc-comment
- fixed indentation issues
- the previous calc block was replaced with `simp_all` and the have statment was removed
- Used wlog
`strong_induction_ppos` was replaced with Mathlib's `PNat.strongInductionOn`
Replaced `incnat` and `decnat` with the Mathlib functions `Nat.succPNat` and `PNat.natPred`
`exists_repeating_ppow_fintype`
- removed the `hexop` have statement
- used `aesop?` and omega to prove the 2nd obtain
- replaced `use m, constructor, exact` with refine
- replaced a calc block with `simp [ppow_add, heq]`
-/

public section PNatPow

variable {M : Type*} [Mul M] [Pow M ℕ+] [PNatPowAssoc M]

/-- Idempotent elements are stable under positive powers. -/
lemma ppow_succ_eq {x : M} (n : ℕ+) (h_idem : IsIdempotentElem x) : x ^ n = x := by
  induction n with
  | one => rw [ppow_one]
  | succ n' ih => rw [ppow_succ, ih, h_idem]

end PNatPow

namespace Fintype

variable {α : Type*} [Fintype α]

/-- A version of the pigeonhole principle for functions from
`Fin n` to a finite type `α` where `n > Fintype.card α`. -/
theorem exists_lt_map_eq_of_card_lt (n : ℕ+) (f : Fin ↑n → α) (h : Fintype.card α < n) :
    (∃ i j : Fin n, i < j ∧ f i = f j) := by
  obtain ⟨i, j, hne , hf ⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp_all)
  wlog hle : i < j
  · refine ⟨j, i, Fin.lt_iff_le_and_ne.mpr ?_, Eq.symm hf⟩
    simp_all [hne.symm]
  · exact ⟨i, j, hle, hf⟩

end Fintype

namespace Semigroup

variable {S : Type*} [Semigroup S] [Pow S ℕ+] [PNatPowAssoc S]


/-when you increment a natural number, you get a positive integer.
These are definitions of increment and decrement functions. -/

def incnat : ℕ → ℕ+ := fun (m : ℕ)↦ ⟨m+1,by omega ⟩

def decnat : ℕ+ → ℕ := fun (m : ℕ+) ↦ (m : ℕ) - 1

lemma incnat_monotone (m n : ℕ) (hlt : m < n) :
incnat m < incnat n := PNat.natPred_lt_natPred.mp hlt

@[simp] lemma incnat_inverse_decnat (x : ℕ+) : incnat (decnat x) = x :=  PNat.natPred_inj.mp rfl

-- FIX: Format
lemma decnat_inverse_incnat (x : ℕ) : decnat (incnat x)
= x := by
  exact Nat.add_zero (( (incnat x): ℕ ).sub 0).pred

lemma incnat_monotone' (m n : ℕ) (hlt : incnat m < incnat n) : m < n := Nat.succ_lt_succ_iff.mp hlt

/-
A version of strong induction for ℕ+, just transferring from the strong induction principle for ℕ.
Switch this to a strong induction principle for ℕ+ that's already present in Mathlib.

The proof is one line, but what does it mean?
What is the thing that exact? found? -/

theorem strong_induction_ppos {P : ℕ+ → Prop} (u : ℕ+)
 (ih : ∀ m : ℕ+, (∀ x : ℕ+, x < m → P x) → P m): P u :=  WellFounded.Nat.fix Subtype.val ih u




#check Nat.succPNat
#check PNat.natPred



/-
Here is a stronger statment of the existence of repeating powers:
Given any positive integer, n there is m no larger than the cardnality of the semigroup such that
x^m = x^n.

Proved by the strong induction principle above coupled with
pigeonhole principle
-/

lemma exists_repeating_ppow_fintype' [Fintype S] (n : ℕ+) (x : S) :
    ∃ m : ℕ+, m ≤ Fintype.card S ∧ x ^ m = x ^ n := by
  apply PNat.strongInductionOn n
  intro n ih
  by_cases n_le_card : n ≤ Fintype.card S
  · use n
  · obtain ⟨o, p, o_lt_p, heq⟩ :=
      Fintype.exists_lt_map_eq_of_card_lt n (fun i ↦ x ^ (i : ℕ).succPNat) (by simp_all)
    by_cases p_lt_n : (p : ℕ).succPNat < n
    · have p_add_n_sub_p : (p : ℕ).succPNat + (n - (p : ℕ).succPNat) = n := by
        exact PNat.add_sub_of_lt p_lt_n
      obtain ⟨m, hm₁, hm₂⟩ : ∃ m : ℕ+,
          m ≤ Fintype.card S ∧ x ^ m = x ^ ((o : ℕ).succPNat + (n - (p : ℕ).succPNat)) := by
        refine ih ((o : ℕ).succPNat + (n - (p : ℕ).succPNat)) ?_
        pnat_to_nat
        simp_all only [not_le, PNat.pos, PNat.coe_lt_coe, Nat.succPNat_coe, Nat.succ_eq_add_one]
        omega
      refine ⟨m, hm₁, ?_⟩
      rw [← p_add_n_sub_p, hm₂]
      simp [ppow_add, heq]
    · have p_eq_n : (p : ℕ).succPNat = n := by
        sorry
      sorry










lemma exists_repeating_ppow_fintype [Fintype S] (n : ℕ+) (x : S) :
 ∃ m : ℕ+, m ≤ Fintype.card S ∧ x^m = x^n := by
  apply strong_induction_ppos n
  intro n ih
  by_cases nlecard : n ≤ Fintype.card S
  · use n
  · have hexop : ∃ o p : (Fin  n), o < p ∧ x ^ (incnat (o : ℕ) ) = x ^(incnat (p : ℕ) ) := by
      apply Fintype.exists_lt_map_eq_of_card_lt
      exact Nat.lt_of_not_le nlecard
    obtain ⟨o, p, holtp, hxoxp⟩  := hexop
    by_cases hpltn : incnat (p : ℕ ) < n
    · let diff := n - (incnat (p : ℕ ))
      have hpdiffeqn : incnat (p : ℕ) + diff = n := PNat.add_sub_of_lt hpltn
      have : incnat (o : ℕ) + diff < n := by
        have :incnat (o : ℕ ) < incnat (p : ℕ) := incnat_monotone (↑o) (↑p) holtp
        calc
          incnat (o : ℕ ) + diff  < incnat (p : ℕ) + diff := add_lt_add_left this diff
          _ = n := hpdiffeqn
      have : ∃ (m : ℕ+), m ≤ Fintype.card S ∧ x^m = x ^ (incnat (o : ℕ) + diff ) :=
        ih (incnat (o:ℕ ) + diff) this
      obtain ⟨m,h₁,h₂⟩ := this
      use m
      constructor
      · exact h₁
      · rw [<-hpdiffeqn,h₂]
        calc
          x^(incnat ↑o + diff) = x^(incnat ↑o) * x^diff := PNatPowAssoc.ppow_add (incnat ↑o) diff x
          _ = x ^ (incnat ↑p) * x ^ diff := by rw [<-hxoxp]
          _ = x ^ (incnat ↑p + diff) := Eq.symm (PNatPowAssoc.ppow_add (incnat ↑p) diff x)
    · have hpeqn : incnat (p : ℕ) = n := by
        have pltn: p < (n : ℕ) :=  p.isLt
        have: incnat (p : ℕ) ≤ n := (PNat.coe_le_coe (incnat ↑p) n).mp pltn
        have: incnat (p : ℕ) < n ∨ incnat (p : ℕ) = n := Std.le_iff_lt_or_eq.mp pltn
        tauto
      have : incnat (o : ℕ) < n :=
        calc
          incnat (o : ℕ ) < incnat (p : ℕ ) := incnat_monotone (↑o) (↑p) holtp
          _               = n := hpeqn
      have : ∃ (m : ℕ+), m ≤ Fintype.card S ∧ x^m = x ^ (incnat (o : ℕ)) := ih (incnat (o:ℕ )) this
      obtain ⟨m,h₁,h₂⟩ := this
      use m
      constructor
      · exact h₁
      · rw [<-hpeqn,h₂,<-hxoxp]

/-
A simple corollary of the above: there exist m < n with m no more
 than the cardinality of S such that
 x^m = x^n.
-/

lemma exists_repeating_ppow_fintype' [Fintype S] (x : S) :
  ∃ (m n : ℕ+), m < n ∧ m ≤ Fintype.card S ∧  x^m = x^n := by
  let n := incnat (Fintype.card S)
  obtain ⟨m,h₁,h₂⟩ := exists_repeating_ppow_fintype n x
  use m , n
  constructor
  · calc
      m ≤ Fintype.card S := h₁
      _ < incnat (Fintype.card S ) := Nat.lt_succ_self (Fintype.card S)
  · exact ⟨h₁,h₂⟩




/- The main result is that there is an idempotent power
where the power is bounded by the cardinality of the semigroup. -/

theorem exists_idempotent_ppow_fintype [Fintype S] (x : S) :
   ∃ (m : ℕ+), m ≤ Fintype.card S ∧ IsIdempotentElem (x ^ m) := by
 obtain ⟨p,q,h₁,h₂,h₃⟩ := exists_repeating_ppow_fintype' x
 have loop : ∀ k : ℕ+ , x^(p + k * (q - p)) = x^p  := by
    intro k
    induction k with
    | one =>
       rw [one_mul, PNat.add_sub_of_lt h₁,h₃ ]
    | succ k =>
        expose_names
        pnat_to_nat
        rw [add_one_mul,<-add_assoc,ppow_add,h,<-ppow_add]
        rw [PNat.add_sub_of_lt,h₃]
        exact h₁
 have isid : IsIdempotentElem (x ^ ((p + 1) * (q - p))) := by
  unfold IsIdempotentElem
  rw [<-ppow_add]
  have ineq : p < (p + 1) * (q - p) := by
    pnat_to_nat
    ring_nf
    omega
  have : (p + 1) * (q - p) + (p + 1) * (q - p) =
        (p + 1) * (q - p) - p + (p + (p + 1) * (q - p)) := by
          pnat_to_nat
          ring_nf
          omega
  rw [this, ppow_add, loop (p + 1),<-ppow_add,(PNat.sub_add_of_lt ineq)]
 obtain ⟨m,h₄,h₅⟩ := exists_repeating_ppow_fintype  ((p + 1) * (q - p)) x
 use m
 constructor
 · exact h₄
 · rw [h₅]
   exact isid



/- If e is idempotent then so is e ^ m -/




/- The factorial function has type ℕ so we have to coerce it to ℕ+ -/

def pfactorial (n : ℕ) : ℕ+ := ⟨Nat.factorial n, by apply Nat.factorial_pos⟩

lemma L3 (m n : ℕ+) (h : m ≤ n) : m ∣ (pfactorial n) := by
  unfold pfactorial
  have : (m : ℕ ) ∣ (Nat.factorial (n :ℕ) ) := by
    apply Nat.dvd_factorial
    · exact PNat.pos m
    · exact (PNat.coe_le_coe m n).mpr h
  exact PNat.dvd_iff.mpr this

theorem idempotent_ppow_factorial_fintype [Fintype S] (x : S) :
 IsIdempotentElem (x^(pfactorial (Fintype.card S))) := by
  obtain ⟨ m , h₁, h₂ ⟩ := exists_idempotent_ppow_fintype x
  have h₃ : 0 < Fintype.card S :=
    calc
      (0 : ℕ)  < m := PNat.pos m
      _ ≤  Fintype.card S := h₁
  obtain ⟨ k₁ ,  h⟩ := L3 m ⟨ Fintype.card S , h₃ ⟩ h₁
  have  h₄ : PNat.val ⟨ Fintype.card S , h₃ ⟩  = Fintype.card S
    := Fintype.card_congr' rfl
  have : x ^ (pfactorial (Fintype.card S)) = x ^ m := by
     calc
      x ^ (pfactorial (Fintype.card S))
         = x^ pfactorial (PNat.val ⟨ Fintype.card S , h₃ ⟩) := by rw [h₄]
      _  = x ^ (m * k₁) := by rw [h]
      _  = (x ^ m) ^ k₁ :=  ppow_mul x m k₁
      _  = x ^ m := by exact ppow_succ_eq k₁ h₂
  rw [this]
  exact h₂


/- In a finite semigroup, powers of any element eventually repeat. -/
/- lemma exists_repeating_ppow [Finite S] (x : S) : ∃ (m n : ℕ+), x ^ m * x ^ n = x ^ m := by
  obtain ⟨o, p, hop, heq⟩ : ∃ o p : ℕ+, o ≠ p ∧ x ^ o = x ^ p := by
    apply Finite.exists_ne_map_eq_of_infinite
  simp_all only [ne_eq, ← ppow_add]
  rcases (lt_or_gt_of_ne hop) with (o_lt_p | p_lt_o)
  · use o, p - o
    rw [heq]
    congr
    pnat_to_nat; omega
  · use p, o - p
    rw [← heq]
    congr
    pnat_to_nat; omega -/

/-- If two powers of an element are both idempotent, then they are equal. -/
theorem ppow_idempotent_unique {x : S} {m n : ℕ+}
    (hm : IsIdempotentElem (x ^ m)) (hn : IsIdempotentElem (x ^ n)) : x ^ m = x ^ n := by
  rw [← ppow_succ_eq m hn, ← ppow_succ_eq n hm, ← ppow_mul, ← ppow_mul']

/- /-- In a finite semigroup, every element has an idempotent power. -/
theorem exists_idempotent_ppow [Finite S] (x : S) : ∃ (m : ℕ+), IsIdempotentElem (x ^ m) := by
  -- `n` is the length of the pre-period/tail, and `loop_size` is the length of the cycle.
  obtain ⟨n, loop_size, loop_eq⟩ := exists_repeating_ppow x
  -- Once powers of `x` enter the cycle,
  -- adding further multiples of `loop_size` to the exponent doesn't change the result.
  have loop : ∀ (loop_count start : ℕ+),
      n < start → x ^ (start + loop_count * loop_size) = x ^ start := by
    intro loop_count
    induction loop_count with
    | one =>
      intro start n_lt_start
      have exists_eq_sum : start = n + (start - n) := by
         pnat_to_nat; omega
      rw [exists_eq_sum]
      simp only [one_mul, ppow_add]
      rw [ppow_mul_comm, mul_assoc, loop_eq]
    | succ loop_count' ih =>
      intro start n_lt_start
      have exists_eq_sum : start = n + (start - n) := by
         pnat_to_nat; omega
      rw [exists_eq_sum] at n_lt_start ⊢
      specialize ih (start - n + n)
      rw [add_comm] at n_lt_start
      apply ih at n_lt_start
      rw [add_one_mul, add_comm n, ← add_assoc, ppow_add, n_lt_start,ppow_add, mul_assoc, loop_eq]
  -- We choose `2 * n * loop_size` as the exponent because it is
  -- beyond the pre-period `n` and is a multiple of `loop_size`.
  use 2 * n * loop_size
  unfold IsIdempotentElem
  specialize loop (2 * n) (2 * n * loop_size)
  simp_all only [ppow_add]
  apply loop
  have n_lt_2nm (n m : ℕ+) : n < 2 * n * m := by
    induction m with
    | one => pnat_to_nat; omega
    | succ m ih => pnat_to_nat; ring_nf; omega
  apply n_lt_2nm

 -/
end Semigroup

namespace Monoid

variable {M : Type*} [Monoid M]

/-- Idempotent elements are stable under positive powers in monoids. -/
lemma pow_succ_eq {x : M} {n : ℕ} (h_idem : IsIdempotentElem x) :
    x ^ (n + 1) = x := by
  induction n with
  | zero => simp_all
  | succ n' ih => rw [pow_succ, ih, h_idem]

variable [Pow M ℕ+] [PNatPowAssoc M]

/-- Every element in a finite monoid has a nonzero idempotent power. -/
theorem exists_idempotent_pow [Finite M] (x : M) :
    ∃ (n : ℕ), IsIdempotentElem (x ^ n) ∧ n ≠ 0 := by
  obtain ⟨m, hm⟩ := Semigroup.exists_idempotent_ppow x
  use m; simp_all only [IsIdempotentElem]
  constructor
  · rwa [← ppow_eq_pow]
  · simp [PNat.ne_zero]

/-- In finite monoids, if `x * a * y = a`, then `x` has a positive power that left-cancels,
and `y` has a positive power that right-cancels. -/
theorem exists_pow_sandwich_eq_self [Finite M] {x a y : M} (h : x * a * y = a) :
    ∃ n₁ n₂ : ℕ, n₁ ≠ 0 ∧ n₂ ≠ 0 ∧ x ^ n₁ * a = a ∧ a * y ^ n₂ = a := by
  have loop : ∀ k : ℕ, x ^ k * a * y ^ k = a := by
    intro k; induction k with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ']
      rw [← mul_assoc, mul_assoc _ a, mul_assoc _ x, ← mul_assoc x a y, h, ih]
  have ⟨n₁, ⟨hn₁, hneq₁⟩⟩ := Monoid.exists_idempotent_pow x
  have ⟨n₂, ⟨hn₂, hneq₂⟩⟩ := Monoid.exists_idempotent_pow y
  use n₁, n₂
  constructor
  · exact hneq₁
  constructor
  · exact hneq₂
  constructor
  · rw [← (loop n₁), ← mul_assoc, ← mul_assoc, hn₁]
  · rw [← (loop n₂), mul_assoc, hn₂]

end Monoid

/- scratch -//-- ### scratch paper for a different version

Here is an effort to produce a more constructive version of the theorems above.

The idea is to switch from Finite to Fintype and show that for all x in S,
x^(|S|!) is idempotent, so you obtain the idempotent value explicitly. Along the
way, we prove that x^k is idempotent for some k ≤ |S|.

Then we'll look at switching this back to Finite
-

/- TBC : version of pigeonhole to apply
theorem exists_ne_map_eq_of_card_lt (f : α → β) (h : Fintype.card β < Fintype.card α) :
    ∃ x y, x ≠ y ∧ f x = f y -/ -/

/- lemma exists_repeating_ppow_bd [Fintype S] (x : S) : ∃ (m n : ℕ+), m < Fintype.card S  ∧ x ^ m * x ^ n = x ^ m := by
  let scard  := Fintype.card S
  let incnat : ℕ → ℕ+ := fun (m : ℕ)↦ ⟨m+1,by omega ⟩
  let g : Fin  (scard + 1) → S := fun m   ↦ x^(incnat (m : ℕ) )
  have h : ∃ o p : (Fin  (scard + 1)), o ≠ p ∧ x ^ (incnat (o : ℕ) ) = x ^(incnat (p : ℕ) ) := by
    apply Fintype.exists_ne_map_eq_of_card_lt
    calc
      Fintype.card S < (Fintype.card S) + 1 := by omega
      _              = scard + 1 := Nat.add_right_cancel_iff.mpr rfl
      _              = Fintype.card (Fin (scard + 1)) := Eq.symm (Fintype.card_fin (scard + 1))
  obtain ⟨o,p,hne,hpow⟩ := h
  let minop := min (o : ℕ) (p : ℕ)
  let maxop := max (o : ℕ) (p : ℕ)
  have h : minop < maxop := by
    omega
  /- need to figure out which of o and p is smaller-/
  use (incnat minop) , (incnat maxop)
  constructor
  · sorry
  · sorry -/

  /- simp_all only [ne_eq, ← ppow_add]
  rcases (lt_or_gt_of_ne hop) with (o_lt_p | p_lt_o)
  · use o, p - o
    rw [heq]
    congr
    pnat_to_nat; omega
  · use p, o - p
    rw [← heq]
    congr
    pnat_to_nat; omega -/
