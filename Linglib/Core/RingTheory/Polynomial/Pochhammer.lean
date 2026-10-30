/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The rising factorial as a product, and its order

`ascPochhammer_eval_eq_prod_range`: `(ascPochhammer R n).eval r = r (r + 1) ⋯ (r + n - 1)`, the
rising-factorial counterpart of mathlib's `descPochhammer_eval_eq_prod_range`. On the nonnegative
elements of an ordered semiring the rising factorial `(x)ₙ` is monotone in `x`, strictly once
`n ≠ 0`, and `(x)ₘ (x)ₙ ≤ (x)ₘ₊ₙ`, strictly when `0 < x` and neither index is zero.

[UPSTREAM] candidate for `Mathlib.RingTheory.Polynomial.Pochhammer`.
-/

@[expose] public section

open Polynomial

theorem ascPochhammer_eval_eq_prod_range {R : Type*} [CommSemiring R] (n : ℕ) (r : R) :
    (ascPochhammer R n).eval r = ∏ j ∈ Finset.range n, (r + j) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]

section StrictOrderedSemiring

variable {S : Type*} [Semiring S] [PartialOrder S] [IsStrictOrderedRing S]

theorem ascPochhammer_nonneg (n : ℕ) {s : S} (h : 0 ≤ s) : 0 ≤ (ascPochhammer S n).eval s := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval]; exact mul_nonneg ih (add_nonneg h n.cast_nonneg)

theorem monotoneOn_ascPochhammer_eval (n : ℕ) :
    MonotoneOn (ascPochhammer S n).eval (Set.Ici 0) := by
  intro x hx y hy hxy
  show (ascPochhammer S n).eval x ≤ (ascPochhammer S n).eval y
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    exact mul_le_mul ih (add_le_add hxy le_rfl) (add_nonneg (Set.mem_Ici.1 hx) n.cast_nonneg)
      (ascPochhammer_nonneg n (Set.mem_Ici.1 hy))

theorem strictMonoOn_ascPochhammer_eval {n : ℕ} (hn : n ≠ 0) :
    StrictMonoOn (ascPochhammer S n).eval (Set.Ici 0) := by
  intro x hx y hy hxy
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  show (ascPochhammer S (n + 1)).eval x < (ascPochhammer S (n + 1)).eval y
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
  exact mul_lt_mul' (monotoneOn_ascPochhammer_eval n hx hy hxy.le)
    (add_lt_add_of_lt_of_le hxy le_rfl)
    (add_nonneg (Set.mem_Ici.1 hx) n.cast_nonneg)
    (ascPochhammer_pos n y ((Set.mem_Ici.1 hx).trans_lt hxy))

end StrictOrderedSemiring

section StrictOrderedCommSemiring

variable {S : Type*} [CommSemiring S] [PartialOrder S] [IsStrictOrderedRing S] {x : S}

theorem ascPochhammer_eval_mul_le (hx : 0 ≤ x) (m n : ℕ) :
    (ascPochhammer S m).eval x * (ascPochhammer S n).eval x ≤
      (ascPochhammer S (m + n)).eval x := by
  rw [← ascPochhammer_mul, eval_mul, eval_comp]
  simp only [eval_add, eval_X, eval_natCast]
  exact mul_le_mul_of_nonneg_left (monotoneOn_ascPochhammer_eval n (Set.mem_Ici.2 hx)
    (Set.mem_Ici.2 (add_nonneg hx m.cast_nonneg)) (le_add_of_nonneg_right m.cast_nonneg))
    (ascPochhammer_nonneg m hx)

theorem ascPochhammer_eval_mul_lt (hx : 0 < x) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (ascPochhammer S m).eval x * (ascPochhammer S n).eval x <
      (ascPochhammer S (m + n)).eval x := by
  rw [← ascPochhammer_mul, eval_mul, eval_comp]
  simp only [eval_add, eval_X, eval_natCast]
  exact mul_lt_mul_of_pos_left (strictMonoOn_ascPochhammer_eval hn (Set.mem_Ici.2 hx.le)
    (Set.mem_Ici.2 (add_nonneg hx.le m.cast_nonneg))
    (lt_add_of_pos_right x (Nat.cast_pos.2 (Nat.pos_of_ne_zero hm))))
    (ascPochhammer_pos m x hx)

theorem prod_ascPochhammer_eval_le {ι : Type*} (hx : 0 ≤ x) (s : Finset ι) (c : ι → ℕ) :
    ∏ i ∈ s, (ascPochhammer S (c i)).eval x ≤ (ascPochhammer S (∑ i ∈ s, c i)).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (mul_le_mul_of_nonneg_left ih (ascPochhammer_nonneg _ hx)).trans
      (ascPochhammer_eval_mul_le hx _ _)

end StrictOrderedCommSemiring
