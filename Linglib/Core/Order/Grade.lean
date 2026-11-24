/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Order.Atoms
public import Mathlib.Order.Grade
public import Mathlib.Order.SuccPred.Nat

/-!
# Orders graded by the natural numbers

In an order graded by `ℕ` every element below `a` lies below an element that `a` covers, so the
grades of the elements below `a` are all the numbers up to the grade of `a`. With a least element,
the atoms are the elements of grade one.

## Main results

* `GradeOrder.isStronglyCoatomic`: an element below `a` lies below one that `a` covers.
* `exists_le_grade_eq`: below an element there is an element of each smaller grade.
* `isAtom_grade_iff`: an element is an atom exactly when its grade is.
* `Nat.isAtom_iff_eq_one`: the atom of `ℕ` is one.
-/

public section

/-- In an order graded by `ℕ` an element below `a` lies below one that `a` covers. -/
instance GradeOrder.isStronglyCoatomic {α : Type*} [Preorder α] [GradeOrder ℕ α] :
    IsStronglyCoatomic α where
  exists_le_covBy_of_lt b a h := by
    induction hn : grade ℕ a - grade ℕ b using Nat.strong_induction_on generalizing b with
    | _ n ih =>
      by_cases hc : b ⋖ a
      · exact ⟨b, le_rfl, hc⟩
      · obtain ⟨z, hbz, hza⟩ := (not_covBy_iff h).1 hc
        have h₁ : grade ℕ b < grade ℕ z := grade_strictMono hbz
        have h₂ : grade ℕ z < grade ℕ a := grade_strictMono hza
        obtain ⟨c, hzc, hca⟩ := ih (grade ℕ a - grade ℕ z) (by omega) z hza rfl
        exact ⟨c, hbz.le.trans hzc, hca⟩

variable {α : Type*} [PartialOrder α] [GradeMinOrder ℕ α] {a b : α} {k : ℕ}

/-- Below an element of an order graded by `ℕ` there is an element of each smaller grade. -/
theorem exists_le_grade_eq (h : k ≤ grade ℕ a) : ∃ c ≤ a, grade ℕ c = k := by
  induction hn : grade ℕ a - k generalizing a with
  | zero => exact ⟨a, le_rfl, by omega⟩
  | succ n ih =>
    have hmin : ¬ IsMin a := fun hm ↦ by
      have h0 : grade ℕ a = 0 := isMin_iff_eq_bot.1 (hm.grade ℕ)
      omega
    obtain ⟨b, hb⟩ := not_isMin_iff.1 hmin
    obtain ⟨c, -, hc⟩ := exists_le_covBy_of_lt hb
    have := Order.covBy_iff_add_one_eq.1 (hc.grade ℕ)
    obtain ⟨d, hd, hk⟩ := ih (a := c) (by omega) (by omega)
    exact ⟨d, hd.trans hc.le, hk⟩

/-- In an order graded by `ℕ` with a least element, the atoms are the elements whose grade is an
atom. -/
theorem isAtom_grade_iff [OrderBot α] : IsAtom (grade ℕ a) ↔ IsAtom a := by
  rw [← bot_covBy_iff, ← bot_covBy_iff (a := a)]
  exact ⟨fun h ↦ (covBy_iff_lt_covBy_grade (𝕆 := ℕ)).2
    ⟨bot_lt_iff_ne_bot.2 fun ha ↦ h.ne (by rw [ha, grade_bot]), by rwa [grade_bot]⟩,
    fun h ↦ by simpa only [grade_bot] using h.grade ℕ⟩

theorem Nat.isAtom_iff_eq_one : IsAtom k ↔ k = 1 := by
  rw [← bot_covBy_iff, Nat.bot_eq_zero, Order.covBy_iff_add_one_eq, zero_add, eq_comm]
