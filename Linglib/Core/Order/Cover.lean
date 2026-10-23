/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.List.Chain
public import Mathlib.Order.Cover

/-!
# Chains of covers

This file proves a discrete intermediate value property. A list in which each element is weakly
covered by the next moves up a linear order one step at a time, so it cannot pass over a value.
The file also decides the covering relations on a finite order, which mathlib does only for
`Bool`. `[UPSTREAM]`

## Main results

* `List.IsChain.mem_of_le_of_le`: a chain of weak covers that starts at or below `x` and reaches
  an element at or above `x` contains `x`.
-/

@[expose] public section

variable {α : Type*}

section Decidable

variable [Fintype α] [Preorder α] [DecidableLE α] [DecidableLT α]

instance WCovBy.instDecidableRelOfFintype : DecidableRel (α := α) (· ⩿ ·) := fun a b ↦
  decidable_of_iff (a ≤ b ∧ ∀ c, a < c → ¬c < b)
    ⟨fun h ↦ ⟨h.1, fun c ↦ h.2 c⟩, fun h ↦ ⟨h.1, fun c ↦ h.2 (c := c)⟩⟩

instance CovBy.instDecidableRelOfFintype : DecidableRel (α := α) (· ⋖ ·) := fun a b ↦
  decidable_of_iff (a < b ∧ ∀ c, a < c → ¬c < b)
    ⟨fun h ↦ ⟨h.1, fun c ↦ h.2 c⟩, fun h ↦ ⟨h.1, fun c ↦ h.2 (c := c)⟩⟩

end Decidable

/-- A chain of weak covers that starts at or below `x` and reaches an element at or above `x`
contains `x`. -/
theorem List.IsChain.mem_of_le_of_le [LinearOrder α] {x m : α} :
    ∀ {a : α} {l : List α}, (a :: l).IsChain (· ⩿ ·) → a ≤ x → m ∈ a :: l → x ≤ m → x ∈ a :: l
  | a, [], _, hax, hm, hxm => by
    obtain rfl := List.mem_singleton.1 hm
    exact List.mem_singleton.2 (le_antisymm hxm hax)
  | a, b :: l, hc, hax, hm, hxm => by
    rw [List.isChain_cons_cons] at hc
    rcases hax.eq_or_lt with rfl | hlt
    · exact List.mem_cons_self
    · rcases List.mem_cons.1 hm with rfl | hm'
      · exact absurd (hlt.trans_le hxm) (lt_irrefl _)
      · exact List.mem_cons_of_mem _
          (mem_of_le_of_le hc.2 (not_lt.1 fun hxb ↦ hc.1.2 hlt hxb) hm' hxm)
