/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.WithTopBot

/-!
# Lower sets carried by finsets

The lower-set predicate on the coercion of a finset, `IsLowerSet (↑s : Set α)`, is decidable over
a finite type with decidable order, and the lower sets contained in a finset form a finset. In a
linear order a lower finset is empty or the initial segment up to its maximum, so the lower finsets
are order-isomorphic to `WithBot α` by their maximum, and a finite chain of `n` elements has
`n + 1` of them.

## Main definitions

* `Fintype.toLocallyFiniteOrderBot`: the bottom intervals of a finite order.
* `IsLowerSet.orderIsoWithBot`: the lower finsets of a linear order as `WithBot α`.
* `Finset.lowerSubsets`: the lower sets contained in a finset.

## Main results

* `IsLowerSet.mem_iff_le_max`: a lower finset of a linear order is `Iic` of its maximum.
* `IsLowerSet.eq_empty_or_eq_Iic`: a lower finset of a linear order is empty or an `Iic`.
* `Fintype.card_subtype_isLowerSet`: a finite chain has one more lower finset than elements.
-/

@[expose] public section

open Finset

section LinearOrder

variable {α : Type*} [LinearOrder α] {s : Finset α} {a : α}

/-- A lower finset of a linear order is the initial segment up to its maximum. [UPSTREAM] -/
theorem IsLowerSet.mem_iff_le_max (h : IsLowerSet (↑s : Set α)) : a ∈ s ↔ ↑a ≤ s.max := by
  refine ⟨le_max, fun ha ↦ ?_⟩
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 (ne_bot_of_le_ne_bot WithBot.coe_ne_bot ha)
  exact h (WithBot.coe_le_coe.1 (hm ▸ ha)) (mem_of_max hm.symm)

variable {t : Finset α}

theorem IsLowerSet.subset_or_subset (hs : IsLowerSet (↑s : Set α))
    (ht : IsLowerSet (↑t : Set α)) : s ⊆ t ∨ t ⊆ s := by
  simpa using hs.total ht

/-- The lower finsets of a linear order form a chain under inclusion. [UPSTREAM] -/
instance : LinearOrder {s : Finset α // IsLowerSet (↑s : Set α)} where
  __ := (inferInstance : PartialOrder {s : Finset α // IsLowerSet (↑s : Set α)})
  le_total s t := s.2.subset_or_subset t.2
  toDecidableLE s t := inferInstanceAs (Decidable (s.1 ⊆ t.1))
  toDecidableEq := inferInstance
  toDecidableLT s t := inferInstanceAs (Decidable (s.1 ⊂ t.1))

end LinearOrder

/-- A finite order has finite bottom intervals. This mirrors `Fintype.toLocallyFiniteOrder` and is
not an instance for the same reason. [UPSTREAM] -/
abbrev Fintype.toLocallyFiniteOrderBot {α : Type*} [Preorder α] [Fintype α] [DecidableLT α]
    [DecidableLE α] : LocallyFiniteOrderBot α where
  finsetIio a := univ.filter (· < a)
  finsetIic a := univ.filter (· ≤ a)
  finset_mem_Iic a x := by simp
  finset_mem_Iio a x := by simp

theorem isLowerSet_coe_empty {α : Type*} [LE α] : IsLowerSet (↑(∅ : Finset α) : Set α) := by
  rw [coe_empty]; exact isLowerSet_empty

section LocallyFiniteOrderBot

variable {α : Type*} [LinearOrder α] [LocallyFiniteOrderBot α] {s : Finset α} {a : α}

theorem isLowerSet_coe_Iic (a : α) : IsLowerSet (↑(Iic a) : Set α) := by
  rw [coe_Iic]; exact isLowerSet_Iic a

@[simp] theorem Finset.max_Iic (a : α) : (Iic a).max = a :=
  le_antisymm (Finset.max_le fun _ hb ↦ WithBot.coe_le_coe.2 (mem_Iic.1 hb))
    (le_max (mem_Iic.2 le_rfl))

theorem IsLowerSet.eq_Iic_of_max_eq (h : IsLowerSet (↑s : Set α)) (ha : s.max = a) :
    s = Iic a := by
  ext x; rw [h.mem_iff_le_max, ha, mem_Iic, WithBot.coe_le_coe]

/-- A lower finset of a linear order is empty or an initial segment. -/
theorem IsLowerSet.eq_empty_or_eq_Iic (h : IsLowerSet (↑s : Set α)) :
    s = ∅ ∨ ∃ a, s = Iic a := by
  rcases hm : s.max with _ | a
  · exact .inl (max_eq_bot.1 hm)
  · exact .inr ⟨a, h.eq_Iic_of_max_eq hm⟩

/-- The lower finsets of a linear order are `WithBot α` by their maximum, `∅` going to `⊥` and
`Iic a` to `a`. [UPSTREAM] -/
def IsLowerSet.orderIsoWithBot : {s : Finset α // IsLowerSet (↑s : Set α)} ≃o WithBot α where
  toFun s := s.1.max
  invFun := WithBot.recBotCoe ⟨∅, isLowerSet_coe_empty⟩ fun a ↦ ⟨Iic a, isLowerSet_coe_Iic a⟩
  left_inv s := Subtype.ext <| by
    dsimp only
    rcases hm : s.1.max with _ | a
    · exact (max_eq_bot.1 hm).symm
    · exact (s.2.eq_Iic_of_max_eq hm).symm
  right_inv a := by cases a <;> simp
  map_rel_iff' {s t} :=
    ⟨fun h x hx ↦ t.2.mem_iff_le_max.2 ((s.2.mem_iff_le_max.1 hx).trans h),
      fun h ↦ max_mono h⟩

@[simp] theorem IsLowerSet.orderIsoWithBot_apply
    (s : {s : Finset α // IsLowerSet (↑s : Set α)}) :
    IsLowerSet.orderIsoWithBot s = s.1.max := rfl

@[simp] theorem IsLowerSet.orderIsoWithBot_symm_bot :
    (IsLowerSet.orderIsoWithBot (α := α)).symm ⊥ = ⟨∅, isLowerSet_coe_empty⟩ := rfl

@[simp] theorem IsLowerSet.orderIsoWithBot_symm_coe (a : α) :
    IsLowerSet.orderIsoWithBot.symm ↑a = ⟨Iic a, isLowerSet_coe_Iic a⟩ := rfl

/-- A finite chain of `n` elements has `n + 1` lower finsets. [UPSTREAM] -/
theorem Fintype.card_subtype_isLowerSet [Fintype α]
    [Fintype {s : Finset α // IsLowerSet (↑s : Set α)}] :
    Fintype.card {s : Finset α // IsLowerSet (↑s : Set α)} = Fintype.card α + 1 :=
  (Fintype.card_congr IsLowerSet.orderIsoWithBot.toEquiv).trans Fintype.card_option

end LocallyFiniteOrderBot

variable {α : Type*} [Preorder α] [Fintype α] [DecidableEq α] [DecidableLE α] {s t : Finset α}

instance (s : Finset α) : Decidable (IsLowerSet (↑s : Set α)) :=
  decidable_of_iff (∀ a ∈ s, ∀ b, b ≤ a → b ∈ s) <| by
    simp only [IsLowerSet, mem_coe]
    exact ⟨fun h _ _ hb ha => h _ ha _ hb, fun h a ha b hb => h hb ha⟩

/-- `t.lowerSubsets` is the finset of lower sets contained in `t`. -/
def Finset.lowerSubsets (t : Finset α) : Finset (Finset α) :=
  t.powerset.filter fun s => IsLowerSet (↑s : Set α)

@[simp] theorem Finset.mem_lowerSubsets :
    s ∈ t.lowerSubsets ↔ s ⊆ t ∧ IsLowerSet (↑s : Set α) := by
  simp [lowerSubsets]

theorem Finset.filter_not_le_mem_lowerSubsets (h : s ∈ t.lowerSubsets) (a : α) :
    (s.filter fun b => ¬ a ≤ b) ∈ t.lowerSubsets := by
  rw [mem_lowerSubsets] at h ⊢
  refine ⟨(filter_subset _ _).trans h.1, ?_⟩
  convert h.2.sdiff_of_isUpperSet (isUpperSet_Ici a) using 1
  ext; simp
