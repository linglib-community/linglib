/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Data.Finset.Lattice.Fold`.
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Finite sets as a free join-semilattice

The finite sets of a type are the free join-semilattice with a bottom on it: a function into such
a semilattice [extends uniquely](##Finset.supBotLift) to a map out of the finite sets preserving
joins and the bottom, the join of the function over the set, and two such maps that
[agree on singletons](##Finset.supBotHom_ext) are equal. The extension of `singleton` is
[the identity](##Finset.coe_supBotLift_singleton).
-/

@[expose] public section

namespace Finset

variable {α β : Type*} [DecidableEq α] [SemilatticeSup β] [OrderBot β]

/-- Maps out of the finite sets of `α` that preserve joins and the bottom agree if they agree on
singletons. -/
@[ext]
theorem supBotHom_ext {f g : SupBotHom (Finset α) β} (h : ∀ a, f {a} = g {a}) : f = g := by
  refine DFunLike.ext _ _ fun s ↦ ?_
  induction s using Finset.induction_on with
  | empty => rw [← bot_eq_empty, map_bot, map_bot]
  | insert a s _ ih => rw [insert_eq, map_sup, map_sup, h, ih]

/-- A function into a join-semilattice with a bottom extends uniquely to a map out of the finite
sets preserving joins and the bottom, the join of the function over the set. -/
def supBotLift : (α → β) ≃ SupBotHom (Finset α) β where
  toFun g :=
    { toFun := fun s ↦ s.sup g
      map_sup' := fun _ _ ↦ sup_union
      map_bot' := sup_empty }
  invFun f a := f {a}
  left_inv _ := funext fun _ ↦ sup_singleton
  right_inv _ := supBotHom_ext fun _ ↦ sup_singleton

@[simp] theorem supBotLift_apply (g : α → β) (s : Finset α) : supBotLift g s = s.sup g := rfl

theorem supBotLift_singleton (g : α → β) (a : α) : supBotLift g {a} = g a := sup_singleton

@[simp] theorem supBotLift_symm_apply (f : SupBotHom (Finset α) β) (a : α) :
    supBotLift.symm f a = f {a} :=
  rfl

/-- The extension of `singleton` is the identity. -/
@[simp] theorem coe_supBotLift_singleton :
    ⇑(supBotLift (singleton : α → Finset α)) = id :=
  funext fun s ↦ sup_singleton_eq_self s

end Finset
