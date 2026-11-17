/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
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

[The same recursion](##RightPreLieRing.braceWith_cons) defines `braceWith ρ n M` for `n` in a
[right module over the commutator Lie ring](##RightPreLieRing.IsRightLieAction) of the pre-Lie
ring, with the action `ρ` in place of the product; `brace` is the case of the ring acting on
itself by right multiplication.

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

variable {L N : Type*} [RightPreLieRing L] [AddCommGroup N]

theorem mul_mul_add_mul_mul (b y z : L) :
    b * y * z + b * (z * y) = b * z * y + b * (y * z) := by
  have h := assoc_symm b y z
  rwa [associator_apply, associator_apply, sub_eq_sub_iff_add_eq_add] at h

/-- A biadditive `ρ`, read as a right action `n • y = ρ y n`, makes `N` a right module over the
commutator Lie ring of `L` when `(n • y) • z - (n • z) • y = n • (y * z - z * y)`, here stated
without subtraction. -/
def IsRightLieAction (ρ : L →+ N →+ N) : Prop :=
  ∀ n y z, ρ z (ρ y n) + ρ (z * y) n = ρ y (ρ z n) + ρ (y * z) n

/-- Right multiplication makes a right pre-Lie ring a right module over its commutator Lie
ring. -/
theorem isRightLieAction_mul : IsRightLieAction (AddMonoidHom.mul.flip : L →+ L →+ L) :=
  fun n y z ↦ mul_mul_add_mul_mul n y z

variable (ρ : L →+ N →+ N)

open Classical in
/-- `braceAux ρ x n M` is the brace of `x` and `M` when `M` has `n` elements, and `0`
otherwise. -/
private noncomputable def braceAux (x : N) : ℕ → Multiset L → N
  | 0, M => if M = 0 then x else 0
  | n + 1, M => if h : M = 0 then 0 else
      (fun w ↦ ρ w (braceAux x n (M.erase w)) -
          (((M.erase w).mulOnce w).map (braceAux x n)).sum)
        (Multiset.exists_mem_of_ne_zero h).choose

/-- Additivity in an element of the multiset. -/
private def IsAddCons (g : Multiset L → N) : Prop :=
  ∀ u v M, g ((u + v) ::ₘ M) = g (u ::ₘ M) + g (v ::ₘ M)

variable {ρ} {g : Multiset L → N}

private theorem IsAddCons.cons (hg : IsAddCons g) (b : L) : IsAddCons fun M ↦ g (b ::ₘ M) :=
  fun u v M ↦ by
    change g (b ::ₘ (u + v) ::ₘ M) = g (b ::ₘ u ::ₘ M) + g (b ::ₘ v ::ₘ M)
    rw [Multiset.cons_swap b (u + v), Multiset.cons_swap b u, Multiset.cons_swap b v]
    exact hg u v _

private theorem sum_map_mulOnce_cons (g : Multiset L → N) (b : L) (M : Multiset L) (y : L) :
    (((b ::ₘ M).mulOnce y).map g).sum =
      g ((b * y) ::ₘ M) + ((M.mulOnce y).map fun D ↦ g (b ::ₘ D)).sum := by
  rw [Multiset.mulOnce_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_map]
  rfl

private theorem sum_map_mulOnce_add (hg : IsAddCons g) (M : Multiset L) (u v : L) :
    ((M.mulOnce (u + v)).map g).sum = ((M.mulOnce u).map g).sum + ((M.mulOnce v).map g).sum := by
  induction M using Multiset.induction_on generalizing g with
  | empty => simp
  | cons b M ih =>
    rw [sum_map_mulOnce_cons, sum_map_mulOnce_cons, sum_map_mulOnce_cons, mul_add, hg,
      ih (hg.cons b)]
    abel

/-- Multiplying one element by `z * y`, or one by `y` and then one by `z`, is symmetric in `y`
and `z`. -/
private theorem sum_map_mulOnce_mulOnce (hg : IsAddCons g) (M : Multiset L) (y z : L) :
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
    rw [← add_zero (0 : N)]
    nth_rewrite 1 [← h]
    nth_rewrite 1 [← h1]
    abel

/-- The step of the recursion at the element `y`, after the step at `z`, is symmetric in `y` and
`z`. -/
private theorem step_step_symm (hρ : IsRightLieAction ρ) (hg : IsAddCons g) (M : Multiset L)
    (y z : L) :
    ρ y (ρ z (g M) - ((M.mulOnce z).map g).sum) -
        (ρ (z * y) (g M) - ((M.mulOnce (z * y)).map g).sum +
          ((M.mulOnce y).map fun D ↦ ρ z (g D) - ((D.mulOnce z).map g).sum).sum) =
      ρ z (ρ y (g M) - ((M.mulOnce y).map g).sum) -
        (ρ (y * z) (g M) - ((M.mulOnce (y * z)).map g).sum +
          ((M.mulOnce z).map fun D ↦ ρ y (g D) - ((D.mulOnce y).map g).sum).sum) := by
  have h := sum_map_mulOnce_mulOnce hg M y z
  have h1 := (hρ (g M) y z).symm
  simp only [Multiset.sum_map_sub, map_sub, map_multiset_sum, Multiset.map_map,
    Function.comp_def]
  rw [← sub_eq_zero] at h h1 ⊢
  rw [← add_zero (0 : N)]
  nth_rewrite 1 [← h]
  nth_rewrite 1 [← h1]
  abel

private theorem braceAux_zero (x : N) {M : Multiset L} (h : M ≠ 0) : braceAux ρ x 0 M = 0 := by
  simp [braceAux, h]

private theorem sum_map_braceAux_zero (x : N) (M : Multiset L) (y : L) :
    ((M.mulOnce y).map (braceAux ρ x 0)).sum = 0 := by
  refine Multiset.sum_eq_zero fun a ha ↦ ?_
  obtain ⟨D, hD, rfl⟩ := Multiset.mem_map.mp ha
  refine braceAux_zero x fun h0 ↦ ?_
  have hc := Multiset.card_of_mem_mulOnce hD
  rw [h0, Multiset.card_zero] at hc
  rw [Multiset.card_eq_zero.mp hc.symm] at hD
  simp at hD

/-- The recursion holds at the element `w` once removing `w` and then `w'` agrees with removing
`w'` and then `w`. -/
private theorem braceAux_succ_cons (x : N) (n : ℕ)
    (hsymm : ∀ w w' M, ρ w' (braceAux ρ x n (w ::ₘ M)) -
        (((w ::ₘ M).mulOnce w').map (braceAux ρ x n)).sum =
      ρ w (braceAux ρ x n (w' ::ₘ M)) - (((w' ::ₘ M).mulOnce w).map (braceAux ρ x n)).sum)
    (w : L) (M : Multiset L) :
    braceAux ρ x (n + 1) (w ::ₘ M) =
      ρ w (braceAux ρ x n M) - ((M.mulOnce w).map (braceAux ρ x n)).sum := by
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

private theorem braceAux_cons_and_isAddCons (hρ : IsRightLieAction ρ) (x : N) (n : ℕ) :
    (∀ w M, braceAux ρ x (n + 1) (w ::ₘ M) =
      ρ w (braceAux ρ x n M) - ((M.mulOnce w).map (braceAux ρ x n)).sum) ∧
    IsAddCons (braceAux ρ x n) := by
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
      exact step_step_symm hρ hadd M w' w
    · rw [hcons, hcons, hcons, map_add, AddMonoidHom.add_apply, sum_map_mulOnce_add hadd]
      abel

/-! ### Braces in a module -/

variable (ρ) in
/-- The brace `n{y₁, …, yₖ}` of an element of a right module over the commutator Lie ring of `L`
and a multiset of elements of `L`. -/
@[no_expose] noncomputable def braceWith (n : N) (M : Multiset L) : N :=
  braceAux ρ n (Multiset.card M) M

@[simp] theorem braceWith_zero (n : N) : braceWith ρ n 0 = n := by
  simp [braceWith, braceAux]

/-- The brace with one more element `y` acts by `y` on the brace and removes the terms in which
`y` multiplies an element of the multiset. -/
theorem braceWith_cons (hρ : IsRightLieAction ρ) (n : N) (y : L) (M : Multiset L) :
    braceWith ρ n (y ::ₘ M) = ρ y (braceWith ρ n M) - ((M.mulOnce y).map (braceWith ρ n)).sum := by
  rw [braceWith, Multiset.card_cons, (braceAux_cons_and_isAddCons hρ n _).1, braceWith]
  refine congrArg _ (congrArg _ (Multiset.map_congr rfl fun D hD ↦ ?_))
  rw [braceWith, Multiset.card_of_mem_mulOnce hD]

@[simp] theorem braceWith_singleton (hρ : IsRightLieAction ρ) (n : N) (y : L) :
    braceWith ρ n {y} = ρ y n := by
  rw [← Multiset.cons_zero, braceWith_cons hρ]
  simp

theorem braceWith_add_cons (hρ : IsRightLieAction ρ) (n : N) (u v : L) (M : Multiset L) :
    braceWith ρ n ((u + v) ::ₘ M) = braceWith ρ n (u ::ₘ M) + braceWith ρ n (v ::ₘ M) := by
  simp only [braceWith, Multiset.card_cons]
  exact (braceAux_cons_and_isAddCons hρ n _).2 u v M

@[simp] theorem braceWith_zero_cons (hρ : IsRightLieAction ρ) (n : N) (M : Multiset L) :
    braceWith ρ n (0 ::ₘ M) = 0 := by
  have h := braceWith_add_cons hρ n 0 0 M
  rwa [add_zero, left_eq_add] at h

theorem braceWith_sum_cons (hρ : IsRightLieAction ρ) (n : N) (s M : Multiset L) :
    braceWith ρ n (s.sum ::ₘ M) = (s.map fun u ↦ braceWith ρ n (u ::ₘ M)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [hρ]
  | cons u s ih =>
    rw [Multiset.sum_cons, braceWith_add_cons hρ, ih, Multiset.map_cons, Multiset.sum_cons]

/-- The brace commutes with scalars in an element of the multiset. -/
theorem braceWith_smul_cons {R : Type*} [Monoid R] [DistribMulAction R L] [DistribMulAction R N]
    [SMulCommClass R L L] (hρ : IsRightLieAction ρ) (hsmul : ∀ (r : R) y n, ρ (r • y) n = r • ρ y n)
    (n : N) (r : R) (u : L) (M : Multiset L) :
    braceWith ρ n ((r • u) ::ₘ M) = r • braceWith ρ n (u ::ₘ M) := by
  classical
  induction hc : Multiset.card M using Nat.strong_induction_on generalizing M u with | _ k ih =>
  rw [braceWith_cons hρ, braceWith_cons hρ, hsmul, smul_sub, Multiset.smul_sum, Multiset.map_map]
  refine congrArg _ (congrArg _ ?_)
  rw [Multiset.mulOnce, Multiset.mulOnce, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun b hb ↦ ?_
  simp only [Function.comp_apply, mul_smul_comm]
  exact ih _ (by rw [← hc, Multiset.card_erase_of_mem hb]
                 exact Nat.pred_lt (Multiset.card_pos_iff_exists_mem.mpr ⟨b, hb⟩).ne') _ _ rfl

/-! ### Braces in the ring -/

/-- The brace `x{y₁, …, yₙ}` of an element and a multiset, the symmetric extension of the
product of a pre-Lie ring. -/
noncomputable def brace (x : L) (M : Multiset L) : L :=
  braceWith AddMonoidHom.mul.flip x M

@[simp] theorem brace_zero (x : L) : brace x 0 = x := braceWith_zero x

/-- The brace with one more element `y` multiplies the brace by `y` and removes the terms in
which `y` multiplies an element of the multiset. -/
theorem brace_cons (x y : L) (M : Multiset L) :
    brace x (y ::ₘ M) = brace x M * y - ((M.mulOnce y).map (brace x)).sum :=
  braceWith_cons isRightLieAction_mul x y M

@[simp] theorem brace_singleton (x y : L) : brace x {y} = x * y :=
  braceWith_singleton isRightLieAction_mul x y

/-- The brace with two elements is the associator. -/
theorem brace_pair (x y z : L) : brace x {y, z} = associator x y z := by
  rw [Multiset.insert_eq_cons, brace_cons, brace_singleton, ← Multiset.cons_zero z,
    Multiset.mulOnce_cons, Multiset.mulOnce_zero, Multiset.map_zero, Multiset.cons_zero,
    Multiset.cons_zero, Multiset.map_singleton, Multiset.sum_singleton, brace_singleton,
    assoc_symm, associator_apply]

theorem brace_add_cons (x u v : L) (M : Multiset L) :
    brace x ((u + v) ::ₘ M) = brace x (u ::ₘ M) + brace x (v ::ₘ M) :=
  braceWith_add_cons isRightLieAction_mul x u v M

@[simp] theorem brace_zero_cons (x : L) (M : Multiset L) : brace x (0 ::ₘ M) = 0 :=
  braceWith_zero_cons isRightLieAction_mul x M

theorem brace_sum_cons (x : L) (s M : Multiset L) :
    brace x (s.sum ::ₘ M) = (s.map fun u ↦ brace x (u ::ₘ M)).sum :=
  braceWith_sum_cons isRightLieAction_mul x s M

end RightPreLieRing
