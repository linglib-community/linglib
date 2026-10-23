/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.Filter

/-!
# Maps and filters of a product of multisets

The `Multiset` analogues of `Finset.prodMap_image_product` and `Finset.filter_product`: mapping
`s ×ˢ t` by a function on each coordinate maps each factor, and filtering it by a predicate on
each coordinate filters each factor. `[UPSTREAM]` candidates; eventual mathlib home
`Mathlib.Data.Multiset.Bind`.
-/

@[expose] public section

namespace Multiset

variable {α β γ δ : Type*} {s : Multiset α} {t : Multiset β}

theorem prodMap_map_product (f : α → γ) (g : β → δ) (s : Multiset α) (t : Multiset β) :
    (s ×ˢ t).map (Prod.map f g) = s.map f ×ˢ t.map g := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [cons_product, ih]

theorem map_map_product_distrib {α' β' : Type*} {f : α × β → γ} {g : γ → δ} {f' : α' × β' → δ}
    {g₁ : α → α'} {g₂ : β → β'} (h : ∀ a b, g (f (a, b)) = f' (g₁ a, g₂ b))
    (s : Multiset α) (t : Multiset β) :
    ((s ×ˢ t).map f).map g = (s.map g₁ ×ˢ t.map g₂).map f' := by
  rw [map_map, ← prodMap_map_product, map_map]
  exact map_congr rfl fun p _ ↦ h p.1 p.2

theorem filter_product (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q] :
    (s ×ˢ t).filter (fun x ↦ p x.1 ∧ q x.2) = s.filter p ×ˢ t.filter q := by
  induction s using Multiset.induction with
  | empty => rfl
  | cons a s ih =>
    by_cases ha : p a <;>
      simp [cons_product, filter_add, ih, filter_map, ha, filter_cons_of_neg, filter_cons_of_pos]

end Multiset
