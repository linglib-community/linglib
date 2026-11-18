/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.OffDiag
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Abel

/-!
# Sums over the off-diagonal pairs of a list

A sum over the ordered pairs of distinct positions of `l₁ ++ l₂` splits into the sums over the
pairs of `l₁`, the pairs of `l₂`, and the pairs with one member in each. `List.offDiag_cons_perm`
is the case of a singleton `l₁`.

[UPSTREAM] candidate for `Mathlib/Data/List/OffDiag.lean`.
-/

public section

namespace List

variable {α M : Type*} [AddCommMonoid M]

theorem sum_map_offDiag_cons (f : α × α → M) (a : α) (l : List α) :
    ((a :: l).offDiag.map f).sum =
      (l.map fun b ↦ f (a, b) + f (b, a)).sum + (l.offDiag.map f).sum := by
  rw [((offDiag_cons_perm a l).map f).sum_eq]
  simp [sum_map_add, Function.comp_def, add_assoc]

theorem sum_map_offDiag_append (f : α × α → M) (l₁ l₂ : List α) :
    ((l₁ ++ l₂).offDiag.map f).sum = (l₁.offDiag.map f).sum + (l₂.offDiag.map f).sum +
      (l₁.map fun a ↦ (l₂.map fun b ↦ f (a, b) + f (b, a)).sum).sum := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    rw [cons_append, sum_map_offDiag_cons, sum_map_offDiag_cons, ih, map_append, sum_append,
      map_cons, sum_cons]
    abel

/-- A sum over the off-diagonal pairs vanishes when every term does. -/
theorem sum_map_offDiag_eq_zero {f : α × α → M} {l : List α}
    (h : ∀ a ∈ l, ∀ b ∈ l, f (a, b) = 0) : (l.offDiag.map f).sum = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [sum_map_offDiag_cons,
      ih fun b hb c hc ↦ h b (mem_cons_of_mem _ hb) c (mem_cons_of_mem _ hc), add_zero]
    refine sum_eq_zero fun x hx ↦ ?_
    obtain ⟨b, hb, rfl⟩ := mem_map.1 hx
    rw [h a mem_cons_self b (mem_cons_of_mem _ hb), h b (mem_cons_of_mem _ hb) a mem_cons_self,
      add_zero]

end List
