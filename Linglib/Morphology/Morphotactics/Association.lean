/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Morphotactics.TemplateMatch

/-!
# The association conventions

This file defines the universal conventions that associate the melodic elements of a tier with
the slots of a template, as McCarthy states them after Clements and Ford. First, the
unassociated melodic elements associate one to one, from left to right, with the free slots.
Second, a single unassociated melodic element that remains associates with every free slot.
Third, a slot still free takes the melodic element on the nearest slot to its left. A slot with
a line from any tier is unavailable to every other tier, the prohibition against many-to-one
association. A language-particular rule that erases a line is followed by the conventions again,
which restore or respread it.

## Main definitions

* `Morphology.TemplateMatch.associateOneToOne`, `associateRemaining`, `spread`: the three
  conventions on one tier.
* `Morphology.TemplateMatch.associate`: the three in order.

## Main results

* `Morphology.TemplateMatch.associate_map`: the conventions never look at the melodic
  elements, so they commute with relabeling them.

## References

* [mccarthy-1981]
* [clements-ford-1979]
-/

@[expose] public section

namespace Morphology.TemplateMatch

variable {α β : Type*} (m : TemplateMatch α) (s : AssocSource)

/-- The slots that bear a tier's melody, which are the V-slots for the vocalism and the C-slots
for the root and the affixes. -/
def bearers : List ℕ := if s = .vocalism then m.template.vSlots else m.template.cSlots

/-- Slot `i` is filled when a line from any tier reaches it. -/
def IsFilled (i : ℕ) : Prop := ∃ a ∈ m.associations, a.slotIndex = i

instance (i : ℕ) : Decidable (m.IsFilled i) :=
  inferInstanceAs (Decidable (∃ a ∈ m.associations, _))

/-- Element `k` of a tier is associated when a line leaves it. -/
def IsAssociated (k : ℕ) : Prop := ∃ a ∈ m.associations, a.source = s ∧ a.melodyIndex = k

instance (k : ℕ) : Decidable (m.IsAssociated s k) :=
  inferInstanceAs (Decidable (∃ a ∈ m.associations, _))

/-- The unassociated elements of a tier, left to right. -/
def unassociated : List ℕ := (List.range (m.melody s).length).filter (¬ m.IsAssociated s ·)

/-- The free slots that bear a tier's melody, left to right. A slot with a line from any tier is
unavailable. -/
def freeBearers : List ℕ := (m.bearers s).filter (¬ m.IsFilled ·)

/-- The match with some lines added. -/
def link (l : List Association) : TemplateMatch α :=
  { m with associations := m.associations ++ l }

/-- The line of a tier on the nearest slot left of `i` that has one. -/
def leftLine (i : ℕ) : Option Association :=
  (m.associations.filter fun a ↦ a.source == s && a.slotIndex < i).foldl
    (fun acc a ↦ match acc with
      | some b => if b.slotIndex < a.slotIndex then some a else some b
      | none => some a) none

/-- The first convention associates the unassociated melodic elements one to one, from left to
right, with the free slots. -/
def associateOneToOne : TemplateMatch α :=
  m.link (((m.unassociated s).zip (m.freeBearers s)).map fun (k, i) ↦ ⟨s, k, i⟩)

/-- The second convention associates a single unassociated melodic element with every free
slot. After the first convention no element is left with a free slot, so this changes only a
match the first has not been applied to. -/
def associateRemaining : TemplateMatch α :=
  match m.unassociated s with
  | [k] => m.link ((m.freeBearers s).map fun i ↦ ⟨s, k, i⟩)
  | _ => m

/-- The third convention gives a free slot the melodic element of the tier on the nearest slot
to its left. -/
def spread : TemplateMatch α :=
  m.link ((m.freeBearers s).filterMap fun i ↦ (m.leftLine s i).map fun a ↦ ⟨s, a.melodyIndex, i⟩)

/-- The three conventions, in order. -/
def associate : TemplateMatch α := ((m.associateOneToOne s).associateRemaining s).spread s

/-! ### Relabeling -/

variable (f : α → β)

@[simp] theorem unassociated_map : (m.map f).unassociated s = m.unassociated s := by
  simp [unassociated, IsAssociated]

@[simp] theorem freeBearers_map : (m.map f).freeBearers s = m.freeBearers s := by
  simp [freeBearers, bearers, IsFilled]

theorem link_map (l : List Association) : (m.map f).link l = (m.link l).map f := rfl

theorem associateOneToOne_map :
    (m.map f).associateOneToOne s = (m.associateOneToOne s).map f := by
  unfold associateOneToOne
  rw [unassociated_map, freeBearers_map]
  rfl

theorem associateRemaining_map :
    (m.map f).associateRemaining s = (m.associateRemaining s).map f := by
  unfold associateRemaining
  rw [unassociated_map, freeBearers_map]
  split <;> rfl

theorem spread_map : (m.map f).spread s = (m.spread s).map f := by
  unfold spread
  rw [freeBearers_map]
  rfl

/-- The conventions never look at the melodic elements. -/
theorem associate_map : (m.map f).associate s = (m.associate s).map f := by
  rw [associate, associateOneToOne_map, associateRemaining_map, spread_map, associate]

end Morphology.TemplateMatch
