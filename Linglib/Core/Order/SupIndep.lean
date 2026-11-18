/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.SupIndep

/-!
# Sums of an independent set

[UPSTREAM] candidate for `Mathlib/Order/SupIndep.lean`.

Summing a set of elements of `s` is left adjoint to taking the elements of `s` below a given
element. When `s` is independent and does not contain `⊥`, the elements of `s` below a sum are
[the elements summed](##sSupIndep.Iic_sSup_inter), so the adjunction is a coinsertion and sums of
distinct subsets of `s` are distinct. This is the complete counterpart of
`Finset.SupIndep.le_sup_iff`.
-/

public section

open Set

variable {α : Type*} [CompleteLattice α] {s t : Set α} {a : α}

/-- Taking the supremum of a set of elements of `s` is left adjoint to taking the elements of
`s` below an element. -/
theorem gc_sSup_Iic_inter (s : Set α) :
    GaloisConnection (fun t : 𝒫 s ↦ sSup t.1)
      (fun a ↦ (⟨Iic a ∩ s, inter_subset_right⟩ : 𝒫 s)) :=
  fun t _ ↦ ⟨fun h _ hb ↦ ⟨(le_sSup hb).trans h, t.2 hb⟩, fun h ↦ sSup_le fun _ hb ↦ (h hb).1⟩

namespace sSupIndep

variable (hs : sSupIndep s)
include hs

theorem le_sSup_iff (hts : t ⊆ s) (ha : a ∈ s) (ha0 : a ≠ ⊥) : a ≤ sSup t ↔ a ∈ t :=
  ⟨fun h ↦ by_contra fun hat ↦ ha0 (le_bot_iff.1 (hs.disjoint_sSup ha hts hat le_rfl h)), le_sSup⟩

/-- The elements of an independent set below a supremum of its elements are the elements the
supremum is taken over. -/
theorem Iic_sSup_inter (hbot : ⊥ ∉ s) (hts : t ⊆ s) : Iic (sSup t) ∩ s = t :=
  Set.ext fun _ ↦ ⟨fun ⟨h, hb⟩ ↦ (hs.le_sSup_iff hts hb fun h0 ↦ hbot (h0 ▸ hb)).1 h,
    fun h ↦ ⟨le_sSup h, hts h⟩⟩

/-- Over an independent set without `⊥`, the adjunction between suprema and the elements below
is a coinsertion. -/
def gciSSupIicInter (hbot : ⊥ ∉ s) :
    GaloisCoinsertion (fun t : 𝒫 s ↦ sSup t.1)
      (fun a ↦ (⟨Iic a ∩ s, inter_subset_right⟩ : 𝒫 s)) :=
  (gc_sSup_Iic_inter s).toGaloisCoinsertion fun t ↦ (hs.Iic_sSup_inter hbot t.2).le

theorem injOn_sSup (hbot : ⊥ ∉ s) : InjOn sSup (𝒫 s) := fun _ ht _ ht' h ↦
  congrArg Subtype.val
    ((hs.gciSSupIicInter hbot).l_injective (a₁ := ⟨_, ht⟩) (a₂ := ⟨_, ht'⟩) h)

end sSupIndep
