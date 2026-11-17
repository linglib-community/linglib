/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Algebra.NonAssoc.PreLie.Basic
public import Mathlib.Tactic.Abel

/-!
# Symmetric braces of a pre-Lie ring

In a right pre-Lie ring the product extends to operations `brace x M` of an element `x` and a
finite multiset `M`, with `brace x 0 = x` and `brace x {y} = x * y`, by the
[recursion](##RightPreLieRing.brace_cons)
`brace x (y ::ₘ M) = brace x M * y - ∑ brace x M'`, the sum over the multisets `M'` obtained from
`M` by multiplying one element on the right by `y`. The recursion removes one element of the
multiset, and the pre-Lie identity is what makes the result independent of the element removed.
On two elements the brace is [the associator](##RightPreLieRing.brace_pair), and it is
[additive in each element](##RightPreLieRing.brace_add_cons) of the multiset.

## Implementation notes

`brace` is defined by removing an element chosen by `Classical.choice`; `brace_cons` then holds
for every element.

## References

* [oudom-guin-2008]
-/

@[expose] public section

namespace Multiset

variable {A : Type*} [Mul A]

open Classical in
/-- The multisets obtained from `M` by multiplying one of its elements on the right by `y`. -/
noncomputable def mulOnce (M : Multiset A) (y : A) : Multiset (Multiset A) :=
  M.map fun b ↦ (b * y) ::ₘ M.erase b

@[simp] theorem mulOnce_zero (y : A) : (0 : Multiset A).mulOnce y = 0 := rfl

theorem mulOnce_cons (b : A) (M : Multiset A) (y : A) :
    (b ::ₘ M).mulOnce y = ((b * y) ::ₘ M) ::ₘ (M.mulOnce y).map (b ::ₘ ·) := by
  classical
  rw [mulOnce, map_cons, erase_cons_head, mulOnce, map_map]
  refine congrArg _ (map_congr rfl fun c hc ↦ ?_)
  by_cases h : c = b
  · subst h
    rw [erase_cons_head, Function.comp_apply, cons_swap, cons_erase hc]
  · rw [erase_cons_tail _ (Ne.symm h), Function.comp_apply, cons_swap]

theorem card_of_mem_mulOnce {M D : Multiset A} {y : A} (h : D ∈ M.mulOnce y) :
    card D = card M := by
  classical
  obtain ⟨b, hb, rfl⟩ := mem_map.mp h
  rw [card_cons, card_erase_of_mem hb, Nat.pred_eq_sub_one,
    Nat.sub_add_cancel (card_pos_iff_exists_mem.mpr ⟨b, hb⟩)]

end Multiset

namespace RightPreLieRing

variable {A : Type*} [RightPreLieRing A]

open Classical in
/-- `braceAux x n M` is the brace of `x` and `M` when `M` has `n` elements, and `0` otherwise. -/
private noncomputable def braceAux (x : A) : ℕ → Multiset A → A
  | 0, M => if M = 0 then x else 0
  | n + 1, M => if h : M = 0 then 0 else
      (fun w ↦ braceAux x n (M.erase w) * w - (((M.erase w).mulOnce w).map (braceAux x n)).sum)
        (Multiset.exists_mem_of_ne_zero h).choose

/-- Additivity in an element of the multiset. -/
private def IsAddCons (g : Multiset A → A) : Prop :=
  ∀ u v M, g ((u + v) ::ₘ M) = g (u ::ₘ M) + g (v ::ₘ M)

variable {g : Multiset A → A}

private theorem IsAddCons.cons (hg : IsAddCons g) (b : A) : IsAddCons fun M ↦ g (b ::ₘ M) :=
  fun u v M ↦ by
    change g (b ::ₘ (u + v) ::ₘ M) = g (b ::ₘ u ::ₘ M) + g (b ::ₘ v ::ₘ M)
    rw [Multiset.cons_swap b (u + v), Multiset.cons_swap b u, Multiset.cons_swap b v]
    exact hg u v _

private theorem sum_map_mulOnce_cons (g : Multiset A → A) (b : A) (M : Multiset A) (y : A) :
    (((b ::ₘ M).mulOnce y).map g).sum =
      g ((b * y) ::ₘ M) + ((M.mulOnce y).map fun D ↦ g (b ::ₘ D)).sum := by
  rw [Multiset.mulOnce_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_map]
  rfl

private theorem sum_map_mulOnce_add (hg : IsAddCons g) (M : Multiset A) (u v : A) :
    ((M.mulOnce (u + v)).map g).sum = ((M.mulOnce u).map g).sum + ((M.mulOnce v).map g).sum := by
  induction M using Multiset.induction_on generalizing g with
  | empty => simp
  | cons b M ih =>
    rw [sum_map_mulOnce_cons, sum_map_mulOnce_cons, sum_map_mulOnce_cons, mul_add, hg,
      ih (hg.cons b)]
    abel

private theorem mul_mul_add_mul_mul (b y z : A) :
    b * y * z + b * (z * y) = b * z * y + b * (y * z) := by
  have h := assoc_symm b y z
  rwa [associator_apply, associator_apply, sub_eq_sub_iff_add_eq_add] at h

/-- Multiplying one element by `z * y`, or one by `y` and then one by `z`, is symmetric in `y`
and `z`. -/
private theorem sum_map_mulOnce_mulOnce (hg : IsAddCons g) (M : Multiset A) (y z : A) :
    ((M.mulOnce (z * y)).map g).sum + ((M.mulOnce y).map fun D ↦ ((D.mulOnce z).map g).sum).sum =
      ((M.mulOnce (y * z)).map g).sum +
        ((M.mulOnce z).map fun D ↦ ((D.mulOnce y).map g).sum).sum := by
  induction M using Multiset.induction_on generalizing g with
  | empty => simp
  | cons b M ih =>
    have h := ih (hg.cons b)
    have h1 : g ((b * y * z) ::ₘ M) + g ((b * (z * y)) ::ₘ M) =
        g ((b * z * y) ::ₘ M) + g ((b * (y * z)) ::ₘ M) := by
      rw [← hg, ← hg, mul_mul_add_mul_mul]
    simp only [sum_map_mulOnce_cons, Multiset.sum_map_add]
    rw [← sub_eq_zero] at h h1 ⊢
    rw [← add_zero (0 : A)]
    nth_rewrite 1 [← h]
    nth_rewrite 1 [← h1]
    abel

/-- The step of the recursion at the element `y`, after the step at `z`, is symmetric in `y` and
`z`. -/
private theorem step_step_symm (hg : IsAddCons g) (M : Multiset A) (y z : A) :
    (g M * z - ((M.mulOnce z).map g).sum) * y -
        (g M * (z * y) - ((M.mulOnce (z * y)).map g).sum +
          ((M.mulOnce y).map fun D ↦ g D * z - ((D.mulOnce z).map g).sum).sum) =
      (g M * y - ((M.mulOnce y).map g).sum) * z -
        (g M * (y * z) - ((M.mulOnce (y * z)).map g).sum +
          ((M.mulOnce z).map fun D ↦ g D * y - ((D.mulOnce y).map g).sum).sum) := by
  have h := sum_map_mulOnce_mulOnce hg M y z
  have h1 := (mul_mul_add_mul_mul (g M) y z).symm
  simp only [Multiset.sum_map_sub, sub_mul, Multiset.sum_map_mul_right]
  rw [← sub_eq_zero] at h h1 ⊢
  rw [← add_zero (0 : A)]
  nth_rewrite 1 [← h]
  nth_rewrite 1 [← h1]
  abel

private theorem braceAux_zero (x : A) {M : Multiset A} (h : M ≠ 0) : braceAux x 0 M = 0 := by
  simp [braceAux, h]

private theorem sum_map_braceAux_zero (x : A) (M : Multiset A) (y : A) :
    ((M.mulOnce y).map (braceAux x 0)).sum = 0 := by
  refine Multiset.sum_eq_zero fun a ha ↦ ?_
  obtain ⟨D, hD, rfl⟩ := Multiset.mem_map.mp ha
  refine braceAux_zero x fun h0 ↦ ?_
  have hc := Multiset.card_of_mem_mulOnce hD
  rw [h0, Multiset.card_zero] at hc
  rw [Multiset.card_eq_zero.mp hc.symm] at hD
  simp at hD

/-- The recursion holds at the element `w` once removing `w` and then `w'` agrees with removing
`w'` and then `w`. -/
private theorem braceAux_succ_cons (x : A) (n : ℕ)
    (hsymm : ∀ w w' M, braceAux x n (w ::ₘ M) * w' -
        (((w ::ₘ M).mulOnce w').map (braceAux x n)).sum =
      braceAux x n (w' ::ₘ M) * w - (((w' ::ₘ M).mulOnce w).map (braceAux x n)).sum)
    (w : A) (M : Multiset A) :
    braceAux x (n + 1) (w ::ₘ M) =
      braceAux x n M * w - ((M.mulOnce w).map (braceAux x n)).sum := by
  classical
  simp only [braceAux, Multiset.cons_ne_zero, ↓reduceDIte]
  have hne : w ::ₘ M ≠ 0 := Multiset.cons_ne_zero
  have hmem := (Multiset.exists_mem_of_ne_zero hne).choose_spec
  generalize (Multiset.exists_mem_of_ne_zero hne).choose = w' at hmem
  by_cases h : w' = w
  · subst h
    simp only [Multiset.erase_cons_head]
  · obtain ⟨M, rfl⟩ := Multiset.exists_cons_of_mem ((Multiset.mem_cons.mp hmem).resolve_left h)
    simp only [Multiset.erase_cons_tail _ (Ne.symm h), Multiset.erase_cons_head]
    exact hsymm w w' M

private theorem braceAux_cons_and_isAddCons (x : A) (n : ℕ) :
    (∀ w M, braceAux x (n + 1) (w ::ₘ M) =
      braceAux x n M * w - ((M.mulOnce w).map (braceAux x n)).sum) ∧
    IsAddCons (braceAux x n) := by
  induction n with
  | zero =>
    refine ⟨braceAux_succ_cons x 0 fun w w' M ↦ ?_, fun u v M ↦ ?_⟩
    · rw [braceAux_zero x Multiset.cons_ne_zero, braceAux_zero x Multiset.cons_ne_zero,
        sum_map_braceAux_zero, sum_map_braceAux_zero]
      simp
    · rw [braceAux_zero x Multiset.cons_ne_zero, braceAux_zero x Multiset.cons_ne_zero,
        braceAux_zero x Multiset.cons_ne_zero, add_zero]
  | succ n ih =>
    obtain ⟨hcons, hadd⟩ := ih
    refine ⟨braceAux_succ_cons x (n + 1) fun w w' M ↦ ?_, fun u v M ↦ ?_⟩
    · simp only [sum_map_mulOnce_cons, hcons]
      exact step_step_symm hadd M w' w
    · rw [hcons, hcons, hcons, mul_add, sum_map_mulOnce_add hadd]
      abel

/-- The brace `x{y₁, …, yₙ}` of an element and a multiset, the symmetric extension of the
product of a pre-Lie ring. -/
@[no_expose] noncomputable def brace (x : A) (M : Multiset A) : A :=
  braceAux x (Multiset.card M) M

@[simp] theorem brace_zero (x : A) : brace x 0 = x := by
  simp [brace, braceAux]

/-- The brace with one more element `y` multiplies the brace by `y` and removes the terms in
which `y` multiplies an element of the multiset. -/
theorem brace_cons (x y : A) (M : Multiset A) :
    brace x (y ::ₘ M) = brace x M * y - ((M.mulOnce y).map (brace x)).sum := by
  rw [brace, Multiset.card_cons, (braceAux_cons_and_isAddCons x _).1, brace]
  refine congrArg _ (congrArg _ (Multiset.map_congr rfl fun D hD ↦ ?_))
  rw [brace, Multiset.card_of_mem_mulOnce hD]

@[simp] theorem brace_singleton (x y : A) : brace x {y} = x * y := by
  rw [← Multiset.cons_zero, brace_cons]
  simp

/-- The brace with two elements is the associator. -/
theorem brace_pair (x y z : A) : brace x {y, z} = associator x y z := by
  rw [Multiset.insert_eq_cons, brace_cons, brace_singleton, ← Multiset.cons_zero z,
    Multiset.mulOnce_cons, Multiset.mulOnce_zero, Multiset.map_zero, Multiset.cons_zero,
    Multiset.cons_zero, Multiset.map_singleton, Multiset.sum_singleton, brace_singleton,
    assoc_symm, associator_apply]

theorem brace_add_cons (x u v : A) (M : Multiset A) :
    brace x ((u + v) ::ₘ M) = brace x (u ::ₘ M) + brace x (v ::ₘ M) := by
  simp only [brace, Multiset.card_cons]
  exact (braceAux_cons_and_isAddCons x _).2 u v M

@[simp] theorem brace_zero_cons (x : A) (M : Multiset A) : brace x (0 ::ₘ M) = 0 := by
  have h := brace_add_cons x 0 0 M
  rwa [add_zero, left_eq_add] at h

theorem brace_sum_cons (x : A) (s M : Multiset A) :
    brace x (s.sum ::ₘ M) = (s.map fun u ↦ brace x (u ::ₘ M)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons u s ih => rw [Multiset.sum_cons, brace_add_cons, ih, Multiset.map_cons, Multiset.sum_cons]

end RightPreLieRing
