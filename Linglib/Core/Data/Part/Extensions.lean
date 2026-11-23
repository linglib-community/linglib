/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Part
public import Linglib.Core.Order.BoundedComplete

/-!
# Total extensions of partial values

A family `s : ∀ v, Part (α v)` of partial values is a piece of information about the total
families `x : ∀ v, α v`: it holds of those that extend it, `Part.piExtensions s`, the `x` with
`s ≤ fun v ↦ Part.some (x v)`. A family that says more has fewer extensions; the extensions of a
join are the common extensions (`Part.piExtensions_of_isLUB`); and two families have a common
extension exactly when they are compatible (`Part.piExtensions_inter_nonempty_iff`). So with a
failed join adjoined as a top element with no extensions, the extensions of a join are the
intersection of the extensions (`Part.piExtensionsTop_sup`).
-/

@[expose] public section

open scoped IsBoundedComplete

/-- Partial values are bounded complete: two with a common extension are comparable. -/
instance {β : Type*} : IsBoundedComplete (Part β) where
  exists_isLUB_of_bddAbove a b h := by
    classical
    obtain ⟨u, hu⟩ := h
    obtain ⟨hau, hbu⟩ := mem_upperBounds_pair.mp hu
    refine ⟨if a.Dom then a else b, isLUB_pair_iff_forall_le.mpr ?_⟩
    split_ifs with hd
    · refine ⟨le_rfl, fun i hi ↦ ?_, fun _ h _ ↦ h⟩
      rw [Part.mem_unique (hbu i hi) (hau _ (Part.get_mem hd))]
      exact Part.get_mem hd
    · exact ⟨fun i hi ↦ (hd hi.fst).elim, le_rfl, fun _ _ h ↦ h⟩

namespace Part

variable {β V : Type*} {α : V → Type*} {s t c : ∀ v, Part (α v)}

/-- The values that extend a partial value: its own, or every value when it is undefined. -/
def extensions (p : Part β) : Set β := {a | p ≤ Part.some a}

@[simp] theorem mem_extensions {p : Part β} {a : β} : a ∈ p.extensions ↔ p ≤ Part.some a :=
  Iff.rfl

@[simp] theorem extensions_bot : (⊥ : Part β).extensions = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ mem_extensions.mpr bot_le

/-- The total families that extend a family of partial values. -/
def piExtensions (s : ∀ v, Part (α v)) : Set (∀ v, α v) := {x | s ≤ fun v ↦ Part.some (x v)}

@[simp] theorem mem_piExtensions {x : ∀ v, α v} :
    x ∈ piExtensions s ↔ s ≤ fun v ↦ Part.some (x v) :=
  Iff.rfl

theorem piExtensions_eq_pi (s : ∀ v, Part (α v)) :
    piExtensions s = Set.pi Set.univ fun v ↦ (s v).extensions :=
  Set.ext fun _ ↦ by simp only [mem_piExtensions, Pi.le_def, Set.mem_univ_pi, mem_extensions]

@[simp] theorem piExtensions_bot : piExtensions (⊥ : ∀ v, Part (α v)) = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ mem_piExtensions.mpr bot_le

theorem piExtensions_anti : Antitone (piExtensions : (∀ v, Part (α v)) → Set (∀ v, α v)) :=
  fun _ _ h _ hx ↦ h.trans hx

/-- The extensions of a join are the common extensions. -/
theorem piExtensions_of_isLUB (h : IsLUB {s, t} c) :
    piExtensions c = piExtensions s ∩ piExtensions t :=
  Set.ext fun _ ↦ (isLUB_le_iff h).trans mem_upperBounds_pair

/-- Two families have a common total extension exactly when they are compatible. -/
theorem piExtensions_inter_nonempty_iff [∀ v, Nonempty (α v)] :
    (piExtensions s ∩ piExtensions t).Nonempty ↔ Compat s t := by
  classical
  refine ⟨fun ⟨_, hs, ht⟩ ↦ .of_le hs ht, fun ⟨u, hu⟩ ↦ ?_⟩
  obtain ⟨hsu, htu⟩ := mem_upperBounds_pair.mp hu
  have hx : u ≤ fun v ↦ Part.some
      (if h : (u v).Dom then (u v).get h else Classical.arbitrary (α v)) := fun v a ha ↦ by
    have hd : (u v).Dom := ha.fst
    simp only [hd, ↓reduceDIte, Part.mem_some_iff]
    exact (Part.get_eq_of_mem ha hd).symm
  exact ⟨_, hsu.trans hx, htu.trans hx⟩

/-- The extensions of a family, a failed join having none. -/
def piExtensionsTop (a : WithTop (∀ v, Part (α v))) : Set (∀ v, α v) :=
  a.recTopCoe ∅ piExtensions

theorem piExtensionsTop_sup [∀ v, Nonempty (α v)] (a b : WithTop (∀ v, Part (α v))) :
    piExtensionsTop (a ⊔ b) = piExtensionsTop a ∩ piExtensionsTop b := by
  induction a using WithTop.recTopCoe with
  | top => rw [top_sup_eq]; exact (Set.empty_inter _).symm
  | coe s =>
    induction b using WithTop.recTopCoe with
    | top => rw [sup_top_eq]; exact (Set.inter_empty _).symm
    | coe t =>
      by_cases h : Compat s t
      · obtain ⟨c, hc⟩ := IsBoundedComplete.exists_isLUB_of_bddAbove s t h
        rw [IsBoundedComplete.coe_sup_coe_eq_coe_iff.mpr hc]
        exact piExtensions_of_isLUB hc
      · rw [IsBoundedComplete.coe_sup_coe_eq_top_iff.mpr h]
        exact (Set.not_nonempty_iff_eq_empty.mp
          (mt piExtensions_inter_nonempty_iff.mp h)).symm

end Part
