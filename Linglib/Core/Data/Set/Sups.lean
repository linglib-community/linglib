/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Sups
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.SupClosed
public import Mathlib.Order.Interval.Set.OrdConnected
public import Linglib.Core.Order.DistribSemilattice

/-!
# Suprema of pointwise sups

Mirror of `Mathlib/Data/Set/Sups.lean`. Pointwise sups preserve sup-closure and the bottom element
in any semilattice, and their sups with `univ` are the upper closure. They preserve downward
closure and, given sup-closure, order-convexity in a distributive semilattice, and preserving
downward closure characterizes distributivity. They respect any relation along which splits
transport both ways. In a complete lattice, the supremum of `s ⊻ t` is the join of the suprema of
two nonempty sets. The indexed form of `s ⊻ t` is `Set.iSups s`, the set of suprema of choices of
an element from each member of a family `s`. [UPSTREAM]
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

/-- The pointwise sups of a set with everything are its upper closure. -/
theorem Set.sups_univ (s : Set α) : s ⊻ Set.univ = upperClosure s :=
  Set.ext fun x ↦ ⟨fun hx ↦ let ⟨a, ha, _, _, h⟩ := Set.mem_sups.1 hx
    mem_upperClosure.2 ⟨a, ha, h ▸ le_sup_left⟩,
    fun hx ↦ let ⟨a, ha, hax⟩ := mem_upperClosure.1 hx
      Set.mem_sups.2 ⟨a, ha, x, trivial, sup_eq_right.2 hax⟩⟩

/-- Pointwise sups respect a relation between semilattices along which splits transport both ways:
if `r` relates `a` to `c`, a split of `a` gives a split of `c` into related parts and conversely,
then membership in `s₁ ⊻ s₂` and in `t₁ ⊻ t₂` agree on `r` when membership in each pair does. -/
theorem Set.mem_sups_congr {β : Type*} [SemilatticeSup β] {r : α → β → Prop}
    (hl : ∀ {a₁ a₂ c}, r (a₁ ⊔ a₂) c → ∃ c₁ c₂, c₁ ⊔ c₂ = c ∧ r a₁ c₁ ∧ r a₂ c₂)
    (hr : ∀ {a c₁ c₂}, r a (c₁ ⊔ c₂) → ∃ a₁ a₂, a₁ ⊔ a₂ = a ∧ r a₁ c₁ ∧ r a₂ c₂)
    {s₁ s₂ : Set α} {t₁ t₂ : Set β} (h₁ : ∀ ⦃a c⦄, r a c → (a ∈ s₁ ↔ c ∈ t₁))
    (h₂ : ∀ ⦃a c⦄, r a c → (a ∈ s₂ ↔ c ∈ t₂)) {a : α} {c : β} (h : r a c) :
    a ∈ s₁ ⊻ s₂ ↔ c ∈ t₁ ⊻ t₂ := by
  simp only [Set.mem_sups]
  refine ⟨?_, ?_⟩
  · rintro ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    obtain ⟨c₁, c₂, rfl, hr₁, hr₂⟩ := hl h
    exact ⟨c₁, (h₁ hr₁).1 ha₁, c₂, (h₂ hr₂).1 ha₂, rfl⟩
  · rintro ⟨c₁, hc₁, c₂, hc₂, rfl⟩
    obtain ⟨a₁, a₂, rfl, hr₁, hr₂⟩ := hr h
    exact ⟨a₁, (h₁ hr₁).2 hc₁, a₂, (h₂ hr₂).2 hc₂, rfl⟩

end SemilatticeSup

section IsDistribSemilatticeSup

variable [SemilatticeSup α] {s t : Set α}

theorem IsLowerSet.sups [IsDistribSemilatticeSup α] (hs : IsLowerSet s) (ht : IsLowerSet t) :
    IsLowerSet (s ⊻ t) := by
  intro x c hc hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sups.mp hx
  obtain ⟨a', ha', b', hb', rfl⟩ := exists_sup_eq_of_le_sup hc
  exact Set.sup_mem_sups (hs ha' ha) (ht hb' hb)

theorem Set.OrdConnected.sups [IsDistribSemilatticeSup α] (hs : s.OrdConnected)
    (ht : t.OrdConnected) (hs' : SupClosed s) (ht' : SupClosed t) : (s ⊻ t).OrdConnected := by
  rw [Set.ordConnected_iff]
  intro y hy z hz hle x ⟨hx₁, hx₂⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sups.mp hy
  obtain ⟨c, hc, d, hd, rfl⟩ := Set.mem_sups.mp hz
  obtain ⟨e, he, f, hf, rfl⟩ := exists_sup_eq_of_le_sup
    (hx₂.trans_eq (sup_sup_sup_comm a b c d ▸ sup_eq_right.2 hle).symm)
  refine Set.mem_sups.mpr ⟨a ⊔ e, hs.out ha (hs' ha hc) ⟨le_sup_left, sup_le le_sup_left he⟩,
    b ⊔ f, ht.out hb (ht' hb hd) ⟨le_sup_left, sup_le le_sup_left hf⟩, ?_⟩
  rw [sup_sup_sup_comm, sup_eq_right.2 hx₁]

/-- A semilattice is distributive exactly when pointwise sups of lower sets are lower sets. -/
theorem isDistribSemilatticeSup_iff_isLowerSet_sups : IsDistribSemilatticeSup α ↔
    ∀ s t : Set α, IsLowerSet s → IsLowerSet t → IsLowerSet (s ⊻ t) := by
  refine ⟨fun _ _ _ hs ht ↦ hs.sups ht, fun h ↦ ⟨fun {a b c} hle ↦ ?_⟩⟩
  exact Set.mem_sups.1 <| h _ _ (isLowerSet_Iic b) (isLowerSet_Iic c) hle
    (Set.sup_mem_sups Set.self_mem_Iic Set.self_mem_Iic)

end IsDistribSemilatticeSup

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
