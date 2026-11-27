/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Algebra.Operations

/-!
# Powers of `1 ⊔ M`

For a submodule `M` of an algebra, the powers of `1 ⊔ M` are an increasing filtration: the `n`-th
is spanned by the products of at most `n` elements of `M`, and it is obtained from the previous
one by adding the products of exactly `n` elements (`Submodule.one_sup_pow_succ`).

`[UPSTREAM]` candidate.
-/

@[expose] public section

namespace Submodule

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (M : Submodule R A)

theorem pow_le_one_sup_pow (k : ℕ) : M ^ k ≤ (1 ⊔ M) ^ k :=
  pow_le_pow_left' le_sup_right k

theorem one_sup_pow_mono {m n : ℕ} (h : m ≤ n) : (1 ⊔ M) ^ m ≤ (1 ⊔ M) ^ n :=
  pow_le_pow_right' le_sup_left h

/-- The products of at most `m + 1` elements are those of at most `m` together with those of
exactly `m + 1`. -/
theorem one_sup_pow_succ (m : ℕ) : (1 ⊔ M) ^ (m + 1) = (1 ⊔ M) ^ m ⊔ M ^ (m + 1) := by
  refine le_antisymm ?_ (sup_le (one_sup_pow_mono M m.le_succ) (pow_le_one_sup_pow M _))
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Submodule.mul_sup, mul_one]
    refine sup_le le_sup_left ?_
    refine (mul_le_mul' ih le_rfl).trans ?_
    rw [Submodule.sup_mul, ← pow_succ]
    exact sup_le (le_sup_of_le_left ((mul_le_mul' le_rfl le_sup_right).trans (pow_succ _ _).ge))
      le_sup_right

end Submodule
