/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Morphotactics.TemplateMatch

/-!
# The association conventions

This file defines the universal conventions that associate the melodic elements of a plane with
the slots of a template, as McCarthy states them after Clements and Ford. Each tier takes a
natural class of slots as its melody-bearing elements, the C-slots for a root or an affix and the
V-slots for a vocalism. First, the unassociated melodic elements associate one to one, from left
to right, with the free bearing slots. Second, a single unassociated melodic element that remains
associates with every free bearing slot. Third, a bearing slot still free takes the melodic
element on the nearest slot to its left. A slot with a line from any plane is unavailable to
every other, the prohibition against many-to-one association. A language-particular rule that
erases a line is followed by the conventions again, which restore or respread it.

## Main definitions

* `AR.associateOneToOne`, `associateRemaining`, `spread`: the three conventions on
  one plane.
* `AR.associate`: the three in order.
* `AR.link`, `AR.delink`: lines added to a plane, and the erasure of the
  lines of a plane on a slot.

## Main results

* `AR.associate_mapMelody`: the conventions never look at the melodic elements, so they
  commute with relabeling them.

## References

* [mccarthy-1981]
* [clements-ford-1979]
-/

@[expose] public section

namespace Autosegmental.AR

variable {ι : Type*} {α β M : Type} (f :
    AR (Multiplanar ι (Sponsored α M) (Sponsored Slot M))) (i : ι) (b : Slot) (φ : α → β)

/-- The slots of class `b`, which bear the melody of a tier that takes them ([mccarthy-1981],
p. 383). -/
def bearers : List ℕ := f.template.findIdxs (· == b)

/-- Element `k` of plane `i` is associated when a line leaves it. -/
def IsAssociated (k : ℕ) : Prop := ∃ l ∈ (f.lines (some i) none), l.1 = k

instance (k : ℕ) : Decidable (f.IsAssociated i k) :=
  inferInstanceAs (Decidable (∃ _ ∈ (f.lines (some i) none), _))

/-- The unassociated elements of plane `i`, left to right. -/
def unassociated : List ℕ := (List.range ((f.word (some i))).length).filter (¬ f.IsAssociated i ·)

/-- The line of plane `i` on the nearest slot left of `s` that has one. -/
def leftLine (s : ℕ) : Option (ℕ × ℕ) :=
  (List.range s).reverse.findSome? fun q ↦
    ((List.range ((f.word (some i))).length).find? fun p ↦ (p, q) ∈ (f.lines (some i) none)).map
        (·, q)

@[simp] theorem unassociated_mapMelody : (f.mapMelody φ).unassociated i = f.unassociated i := by
  simp [unassociated, IsAssociated]

@[simp] theorem leftLine_mapMelody (s : ℕ) : (f.mapMelody φ).leftLine i s = f.leftLine i s := by
  simp [leftLine]

section Link

variable [DecidableEq ι]

/-- The match with the lines `L` added to plane `i`. -/
def link (L : List (ℕ × ℕ)) : AR (Multiplanar ι (Sponsored α M) (Sponsored Slot M)) :=
  f.addLines i L.toFinset

/-- The match with the lines of plane `i` on slot `s` erased, as a language-particular rule erases
them before the conventions apply again. -/
def delink (s : ℕ) : AR (Multiplanar ι (Sponsored α M) (Sponsored Slot M)) :=
  f.filterLines i (·.2 ≠ s)

theorem link_mapMelody (L : List (ℕ × ℕ)) : (f.mapMelody φ).link i L = (f.link i L).mapMelody φ :=
  (mapMelody_addLines f φ i _).symm

theorem delink_mapMelody (s : ℕ) : (f.mapMelody φ).delink i s = (f.delink i s).mapMelody φ :=
  (mapMelody_filterLines f φ i _).symm

end Link

variable [Fintype ι]

/-- The free slots of class `b`, left to right. A slot with a line from any plane is
unavailable. -/
def freeBearers : List ℕ := (f.bearers b).filter (¬ f.IsFilled ·)

@[simp] theorem freeBearers_mapMelody : (f.mapMelody φ).freeBearers b = f.freeBearers b := rfl

variable [DecidableEq ι]

/-- The first convention associates the unassociated melodic elements one to one, from left to
right, with the free bearing slots. -/
def associateOneToOne : AR (Multiplanar ι (Sponsored α M) (Sponsored Slot M)) :=
  f.link i ((f.unassociated i).zip (f.freeBearers b))

/-- The second convention associates a single unassociated melodic element with every free
bearing slot. After the first convention no element is left with a free slot, so this changes
only a match the first has not been applied to. -/
def associateRemaining : AR (Multiplanar ι (Sponsored α M) (Sponsored Slot M)) :=
  match f.unassociated i with
  | [k] => f.link i ((f.freeBearers b).map (k, ·))
  | _ => f

/-- The third convention gives a free bearing slot the melodic element of the plane on the
nearest slot to its left. -/
def spread : AR (Multiplanar ι (Sponsored α M) (Sponsored Slot M)) :=
  f.link i ((f.freeBearers b).filterMap fun s ↦ (f.leftLine i s).map fun l ↦ (l.1, s))

/-- The three conventions, in order. -/
def associate : AR (Multiplanar ι (Sponsored α M) (Sponsored Slot M)) :=
  ((f.associateOneToOne i b).associateRemaining i b).spread i b

/-! ### Relabeling -/

theorem associateOneToOne_mapMelody :
    (f.mapMelody φ).associateOneToOne i b = (f.associateOneToOne i b).mapMelody φ := by
  rw [associateOneToOne, unassociated_mapMelody, freeBearers_mapMelody, link_mapMelody]
  rfl

theorem associateRemaining_mapMelody :
    (f.mapMelody φ).associateRemaining i b = (f.associateRemaining i b).mapMelody φ := by
  unfold associateRemaining
  rw [unassociated_mapMelody, freeBearers_mapMelody]
  split
  · exact link_mapMelody ..
  · rfl

theorem spread_mapMelody : (f.mapMelody φ).spread i b = (f.spread i b).mapMelody φ := by
  unfold spread
  simp only [freeBearers_mapMelody, leftLine_mapMelody]
  exact link_mapMelody ..

/-- The conventions never look at the melodic elements. -/
theorem associate_mapMelody : (f.mapMelody φ).associate i b = (f.associate i b).mapMelody φ := by
  rw [associate, associateOneToOne_mapMelody, associateRemaining_mapMelody, spread_mapMelody,
      associate]

end Autosegmental.AR
