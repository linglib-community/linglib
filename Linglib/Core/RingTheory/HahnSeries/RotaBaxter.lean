/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RotaBaxter
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.Tactic.NoncommRing

/-!
# The polar part of a Hahn series

For a linearly ordered cancellative monoid `Γ`, the truncation `HahnSeries.truncLT 0` keeps the
coefficients of a Hahn series at the negative exponents. On Laurent series it is the projection
onto the polar part, and it is a Rota–Baxter operator of weight `-1`: since exponents add under
multiplication, the series supported on the negative exponents form a subring, and so do the
series supported on the nonnegative ones.

## Main results

* `HahnSeries.isRotaBaxter_truncLT`: `truncLT 0` is a Rota–Baxter operator of weight `-1`.
* `HahnSeries.truncLT_truncLT`, `HahnSeries.truncLT_single`: truncation is idempotent, and it keeps
  or kills a monomial.
* `HahnSeries.truncLT_neg`, `HahnSeries.truncLT_sub`: truncation commutes with negation and
  subtraction.

The four truncation lemmas are `[UPSTREAM]` candidates for
`Mathlib/RingTheory/HahnSeries/Basic.lean` and `Mathlib/RingTheory/HahnSeries/Addition.lean`,
beside `truncLT_add`.

## References

* [connes-kreimer-2000]
* [ebrahimi-fard-guo-kreimer-2004]
-/

@[expose] public section

namespace HahnSeries

variable {Γ R : Type*}

section Zero

variable [PartialOrder Γ] [DecidableLT Γ] [Zero R]

@[simp] theorem truncLT_truncLT (c : Γ) (x : R⟦Γ⟧) : truncLT c (truncLT c x) = truncLT c x := by
  ext i
  simp only [HahnSeries.coeff_truncLT]
  split_ifs <;> rfl

theorem truncLT_single (c d : Γ) (r : R) :
    truncLT c (single d r) = if d < c then single d r else 0 := by
  ext i
  rcases eq_or_ne i d with rfl | hi <;> split_ifs <;> simp_all

end Zero

section AddGroup

variable [PartialOrder Γ] [DecidableLT Γ] [AddGroup R]

theorem truncLT_neg (c : Γ) (x : R⟦Γ⟧) : truncLT c (-x) = -truncLT c x := by
  ext i
  simp only [HahnSeries.coeff_truncLT, coeff_neg]
  split_ifs <;> simp

theorem truncLT_sub (c : Γ) (x y : R⟦Γ⟧) : truncLT c (x - y) = truncLT c x - truncLT c y := by
  rw [sub_eq_add_neg, truncLT_add, truncLT_neg, ← sub_eq_add_neg]

end AddGroup

theorem truncLT_single_eq_zero_iff [LinearOrder Γ] [Zero R] {c d : Γ} {r : R} (hr : r ≠ 0) :
    truncLT c (single d r) = 0 ↔ c ≤ d := by
  rw [truncLT_single]
  split_ifs with h
  · simp [hr, h.not_ge]
  · simp [not_lt.mp h]

section Ring

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [Ring R]

private theorem truncLT_truncLT_mul_truncLT (x y : R⟦Γ⟧) :
    truncLT 0 (truncLT 0 x * truncLT 0 y) = truncLT (0 : Γ) x * truncLT 0 y := by
  ext i
  rw [HahnSeries.coeff_truncLT, ite_eq_left_iff, not_lt]
  refine fun hi ↦ (by_contra fun hne ↦ ?_)
  obtain ⟨j, hj, l, hl, rfl⟩ := support_mul_subset ((mem_support _ _).mpr (Ne.symm hne))
  rw [support_truncLT] at hj hl
  exact (add_neg hj.2 hl.2).not_ge hi

private theorem truncLT_sub_truncLT_mul (x y : R⟦Γ⟧) :
    truncLT (0 : Γ) ((x - truncLT 0 x) * (y - truncLT 0 y)) = 0 := by
  have hnonneg (z : R⟦Γ⟧) {j : Γ} (hj : j ∈ (z - truncLT 0 z).support) : 0 ≤ j := by
    by_contra h
    simp [not_le.mp h] at hj
  ext i
  rw [HahnSeries.coeff_truncLT, coeff_zero, ite_eq_right_iff]
  refine fun hi ↦ by_contra fun hne ↦ ?_
  obtain ⟨j, hj, l, hl, rfl⟩ := support_mul_subset ((mem_support _ _).mpr hne)
  exact (add_nonneg (hnonneg x hj) (hnonneg y hl)).not_gt hi

/-- The projection onto the polar part is a Rota–Baxter operator of weight `-1`, from the ring
identity `R a * b + a * R b - a * b = R a * R b - (a - R a) * (b - R b)`: `R` fixes the first
term, a product of polar parts, and kills the second, a product of nonpolar parts. -/
theorem isRotaBaxter_truncLT (k : Type*) [Ring k] [Module k R⟦Γ⟧] :
    IsRotaBaxter (-1 : k) ⇑(truncLT (0 : Γ) : ZeroHom R⟦Γ⟧ R⟦Γ⟧) := by
  refine isRotaBaxter_neg_one_iff.2 fun a b ↦ ?_
  rw [show truncLT 0 a * b + a * truncLT 0 b - a * b
      = truncLT 0 a * truncLT 0 b - (a - truncLT 0 a) * (b - truncLT 0 b) by noncomm_ring,
    truncLT_sub, truncLT_truncLT_mul_truncLT, truncLT_sub_truncLT_mul, sub_zero]

end Ring

end HahnSeries
