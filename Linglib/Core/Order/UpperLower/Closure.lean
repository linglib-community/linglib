module

public import Mathlib.Data.Set.Sups
public import Mathlib.Order.Minimal
public import Mathlib.Order.UpperLower.Closure

/-!
# Minimal elements of upper closures

`[UPSTREAM]` candidate for `Mathlib/Order/UpperLower/Closure.lean`: in a partial order, the
minimal elements of an upper closure are those of the generating set, and so is its least element.
mathlib has the minimal-element lemma only for antichains,
`IsAntichain.minimal_mem_upperClosure_iff_mem`, which follows from the general one with
`IsAntichain.minimal_mem_iff`. In a join-semilattice the meet of two upper closures is the upper
closure of the pairwise joins, so its minimal elements are those of the pairwise joins.
-/

@[expose] public section

open Set

variable {α : Type*}

section PartialOrder
variable [PartialOrder α] {s : Set α} {x : α}

@[to_dual /-- The maximal elements of the lower closure of `s` are those of `s`. -/]
theorem minimal_mem_upperClosure_iff : Minimal (· ∈ upperClosure s) x ↔ Minimal (· ∈ s) x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨subset_upperClosure h.prop, fun y ⟨a, has, hay⟩ hyx ↦
    (h.eq_of_ge has (hay.trans hyx)).symm ▸ hay⟩⟩
  obtain ⟨a, has, hax⟩ := h.prop
  obtain rfl := h.eq_of_ge (subset_upperClosure has) hax
  exact h.mono (fun _ ↦ (subset_upperClosure ·)) has

@[to_dual /-- A set and its lower closure have the same greatest element. -/]
theorem isLeast_upperClosure_iff : IsLeast (upperClosure s : Set α) x ↔ IsLeast s x := by
  refine ⟨fun ⟨⟨a, has, hax⟩, hx⟩ ↦ ?_, fun ⟨hx, hlb⟩ ↦ ⟨subset_upperClosure hx, ?_⟩⟩
  · exact ⟨(hax.antisymm (hx (subset_upperClosure has))).symm ▸ has,
      fun b hb ↦ hx (subset_upperClosure hb)⟩
  · rintro b ⟨a, has, hab⟩
    exact (hlb has).trans hab

end PartialOrder

section SemilatticeSup
variable [SemilatticeSup α] {s t : Set α} {x : α}

open SetFamily in
/-- The minimal elements of the meet of two upper closures are those of the pairwise joins of
their generators. -/
theorem minimal_mem_inter_upperClosure_iff :
    Minimal (· ∈ (upperClosure s : Set α) ∩ upperClosure t) x ↔ Minimal (· ∈ s ⊻ t) x := by
  rw [← UpperSet.coe_sup, ← upperClosure_sups]
  exact minimal_mem_upperClosure_iff

end SemilatticeSup
