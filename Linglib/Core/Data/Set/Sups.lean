/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Sups
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.SupClosed
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Suprema of pointwise sups

Mirror of `Mathlib/Data/Set/Sups.lean`. Pointwise sups preserve sup-closure and the bottom element
in any semilattice, and downward closure and order-convexity (the latter given sup-closure) in a
distributive lattice, where `c ≤ a ⊔ b` splits as `c = (c ⊓ a) ⊔ (c ⊓ b)`. In a complete lattice,
the supremum of `s ⊻ t` is the join of the suprema of two nonempty sets. The indexed form of
`s ⊻ t` is `Set.iSups s`, the set of suprema of choices of an element from each member of a family
`s`. [UPSTREAM]
-/

@[expose] public section

open SetFamily

section Closure

variable {α : Type*}

section SemilatticeSup

variable [SemilatticeSup α] {s t : Set α}

theorem SupClosed.sups (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s ⊻ t) := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sups.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := Set.mem_sups.mp hy
  exact Set.mem_sups.mpr ⟨a ⊔ c, hs ha hc, b ⊔ d, ht hb hd, (sup_sup_sup_comm a b c d).symm⟩

theorem Set.bot_mem_sups [OrderBot α] (hs : ⊥ ∈ s) (ht : ⊥ ∈ t) : ⊥ ∈ s ⊻ t :=
  Set.mem_sups.mpr ⟨⊥, hs, ⊥, ht, bot_sup_eq ⊥⟩

end SemilatticeSup

section DistribLattice

variable [DistribLattice α] {s t : Set α}

theorem IsLowerSet.sups (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ⊻ t) := by
  intro x c hc hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sups.mp hx
  exact Set.mem_sups.mpr ⟨c ⊓ a, hs inf_le_right ha, c ⊓ b, ht inf_le_right hb,
    by rw [← inf_sup_left, inf_eq_left.mpr hc]⟩

theorem Set.OrdConnected.sups (hs : s.OrdConnected) (ht : t.OrdConnected) (hs' : SupClosed s)
    (ht' : SupClosed t) : (s ⊻ t).OrdConnected := by
  rw [Set.ordConnected_iff]
  intro y hy z hz hle x ⟨hx₁, hx₂⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sups.mp hy
  obtain ⟨c, hc, d, hd, rfl⟩ := Set.mem_sups.mp hz
  refine Set.mem_sups.mpr ⟨(a ⊔ c) ⊓ x, hs.out ha (hs' ha hc)
      ⟨le_inf le_sup_left (le_sup_left.trans hx₁), inf_le_left⟩, (b ⊔ d) ⊓ x,
      ht.out hb (ht' hb hd) ⟨le_inf le_sup_left (le_sup_right.trans hx₁), inf_le_left⟩, ?_⟩
  rw [← inf_sup_right, sup_sup_sup_comm, sup_eq_right.mpr hle, inf_eq_right.mpr hx₂]

end DistribLattice

end Closure

namespace Set

variable {α : Type*} [CompleteLattice α] {s t : Set α}

theorem sSup_sups (hs : s.Nonempty) (ht : t.Nonempty) : sSup (s ⊻ t) = sSup s ⊔ sSup t := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  refine le_antisymm (sSup_le <| forall_sups_iff.2 fun c hc d hd ↦
    sup_le_sup (le_sSup hc) (le_sSup hd)) (sup_le (sSup_le fun c hc ↦ ?_) (sSup_le fun d hd ↦ ?_))
  · exact le_sup_left.trans (le_sSup (sup_mem_sups hc hb))
  · exact le_sup_right.trans (le_sSup (sup_mem_sups ha hd))

section iSups

variable {ι : Type*} {s : ι → Set α} {a : α}

/-- The pointwise supremum of a family of sets is the set of suprema of choices of an element from
each member of the family. [UPSTREAM] -/
def iSups (s : ι → Set α) : Set α :=
  (fun f : ι → α ↦ ⨆ i, f i) '' univ.pi s

theorem mem_iSups : a ∈ iSups s ↔ ∃ f : ι → α, (∀ i, f i ∈ s i) ∧ ⨆ i, f i = a := by
  simp [iSups]

theorem iSup_mem_iSups {f : ι → α} (hf : ∀ i, f i ∈ s i) : ⨆ i, f i ∈ iSups s :=
  mem_iSups.2 ⟨f, hf, rfl⟩

theorem exists_mem_iSups_ge (hs : ∀ j, (s j).Nonempty) {i : ι} (ha : a ∈ s i) :
    ∃ b ∈ iSups s, a ≤ b := by
  classical
  let f : ι → α := Function.update (fun j ↦ (hs j).some) i a
  have hf : ∀ j, f j ∈ s j := fun j ↦ by
    by_cases h : j = i
    · subst h
      simpa [f] using ha
    · simpa [f, h] using (hs j).some_mem
  exact ⟨_, iSup_mem_iSups hf, by simpa [f] using le_iSup f i⟩

theorem sSup_iSups (hs : ∀ i, (s i).Nonempty) : sSup (iSups s) = ⨆ i, sSup (s i) := by
  refine le_antisymm (sSup_le fun _ ha ↦ ?_) (iSup_le fun i ↦ sSup_le fun b hb ↦ ?_)
  · obtain ⟨f, hf, rfl⟩ := mem_iSups.1 ha
    exact iSup_mono fun i ↦ le_sSup (hf i)
  · obtain ⟨c, hc, hbc⟩ := exists_mem_iSups_ge hs hb
    exact hbc.trans (le_sSup hc)

theorem upperClosure_iSups : upperClosure (iSups s) = ⨆ i, upperClosure (s i) := by
  refine SetLike.ext fun a ↦ ?_
  rw [mem_upperClosure, UpperSet.mem_iSup_iff]
  simp only [mem_upperClosure]
  refine ⟨fun ⟨_, hb, hba⟩ i ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨f, hf, rfl⟩ := mem_iSups.1 hb
    exact ⟨f i, hf i, (le_iSup f i).trans hba⟩
  · choose f hf hfa using h
    exact ⟨_, iSup_mem_iSups hf, iSup_le hfa⟩

end iSups

end Set
