import Mathlib.Algebra.Group.Idempotent
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Denumerable
import Semigroup.Power

/-!
# Idempotent Elements in Finite Semigroups

This file defines properties related to idempotent elements in finite semigroups and monoids.

## Main theorems

Let `S` be a finite semigroup and `x : S`
* `Semigroup.exists_idempotent_pow` - `∃ (m : ℕ+), IsIdempotentElem (x ^ m)`
* `Monoid.exists_idempotent_pow` - `∃ (n : ℕ), IsIdempotentElem (x ^ n) ∧ n ≠ 0` in finite monoids.
* `Monoid.exists_pow_sandwich_eq_self` - If `a = x * a * y`, then
  `∃ n₁ n₂ : ℕ, n₁ ≠ 0 ∧ n₂ ≠ 0 ∧ x ^ n₁ * a = a ∧ a * y ^ n₂ = a`.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-- Idempotent elements are stable under positive powers. -/
lemma pow_succ_eq {x : S} (n : ℕ+) (h_idem : IsIdempotentElem x) : x ^ n = x := by
  induction n using PNat.recOn with
  | one => rfl
  | succ n' ih => rw [← pow_succ, ih, h_idem]

/-- In a finite semigroup, powers of any element eventually repeat. -/
lemma exists_repeating_pow [Finite S] (x : S) : ∃ (m n : ℕ+), x ^ m * x ^ n = x ^ m := by
  obtain ⟨o, p, hop, heq⟩ : ∃ o p : ℕ+, o ≠ p ∧ x ^ o = x ^ p := by
    apply Finite.exists_ne_map_eq_of_infinite
  simp_all only [ne_eq, pow_add]; pnat_to_nat
  rcases (Nat.lt_or_gt_of_ne hop) with (o_lt_p | p_lt_o)
  · use o, p - o; simp_all
  · use p, o - p; simp_all

/-- If two powers of an element are both idempotent, then they are equal. -/
theorem pow_idempotent_unique {x : S} {m n : ℕ+}
    (hm : IsIdempotentElem (x ^ m)) (hn : IsIdempotentElem (x ^ n)) : x ^ m = x ^ n := by
  rw [← pow_succ_eq n hm, pow_right_comm, pow_succ_eq m hn]

/-- In a finite semigroup, every element has an idempotent power. -/
theorem exists_idempotent_pow [Finite S] (x : S) : ∃ (m : ℕ+), IsIdempotentElem (x ^ m) := by
  -- `n` is the length of the pre-period (tail),
  -- `loop_size` is the length of the cycle.
  obtain ⟨n, loop_size, loop_eq⟩ := exists_repeating_pow x
  -- The `loop` lemma formalizes that once powers of `x` enter the cycle,
  -- adding further multiples of `loop_size` to the exponent doesn't change the result.
  have loop : ∀ (loop_count start : ℕ+),
      n < start → x ^ (start + loop_count * loop_size) = x ^ start := by
    intro loop_count
    induction loop_count using PNat.recOn with
    | one =>
      intro start n_lt_start
      obtain ⟨diff, hdiff⟩ := PNat.exists_eq_add_of_lt n_lt_start
      simp_all only [one_mul, ← pow_add, mul_assoc]
    | succ loop_count' ih =>
      intro start n_lt_start
      obtain ⟨diff, hdiff⟩ := PNat.exists_eq_add_of_lt n_lt_start
      subst hdiff
      specialize ih (diff + n)
      apply ih at n_lt_start
      have h_arith :
        (loop_count' + 1) * loop_size = (loop_count' * loop_size) + loop_size := by ring
      simp_rw [h_arith, ← add_assoc, ← pow_add] at *
      rw [n_lt_start, mul_assoc, loop_eq]
  -- We choose `2 * n * loop_size` as the exponent for our idempotent element.
  -- This ensures the exponent is beyond the pre-period `n` and is a multiple of `loop_size`.
  use 2 * n * loop_size
  unfold IsIdempotentElem
  specialize loop (2 * n) (2 * n * loop_size)
  simp_all only [pow_add]
  -- Apply the `loop` lemma. The condition `n < 2 * n * loop_size` is met by `PNat.n_lt_2nm`.
  apply loop
  exact PNat.n_lt_2nm n loop_size

end Semigroup

namespace Monoid

variable {M : Type*} [Monoid M]

/-- Idempotent elements are stable under positive powers in monoids. -/
lemma pow_succ_eq {x : M} {n : ℕ} (h_idem : IsIdempotentElem x) :
    x ^ (n + 1) = x := by
  induction n with
  | zero => simp_all
  | succ n' ih => rw [pow_succ, ih, h_idem]

/-- Every element in a finite monoid has a nonzero idempotent power. -/
theorem exists_idempotent_pow [Finite M] (x : M) :
    ∃ (n : ℕ), IsIdempotentElem (x ^ n) ∧ n ≠ 0 := by
  obtain ⟨m, hm⟩ := Semigroup.exists_idempotent_pow x
  use m; simp_all only [IsIdempotentElem]
  constructor
  · rwa [← pow_pNat_to_nat]
  · simp [PNat.ne_zero]

/-- In finite monoids, elements satisfying a sandwich property have powers that left-cancel
and right-cancel the sandwich factors. -/
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
