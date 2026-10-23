/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Root.Consonantal
public import Linglib.Phonology.Autosegmental.NonCrossing
public import Linglib.Phonology.Autosegmental.Skeleton

/-!
# Template matches

In McCarthy's prosodic theory of nonconcatenative morphology, a word is built by associating
melodies on separate morphemic tiers, a consonantal root, a vocalism, and affixal material, with
the slots of a prosodic template, a CV skeleton. A `TemplateMatch` records the three melodies,
the template, and the association lines, and `spellout` reads off the surface segments.
Gemination is one melody element associated to several slots, and a slot with no association
line receives no phonetic realization. The association conventions that draw the lines are in
`Morphology/Morphotactics/Association.lean`.

## Main definitions

* `AssocSource`: the morphemic tier of a melody.
* `Association`: an association line from a melody element to a template slot.
* `TemplateMatch`: a root, vocalism, and affix associated with a template.
* `TemplateMatch.spellout`, `TemplateMatch.map`: the surface segments of a match, and the
  relabelling of its melodies.
* `TemplateMatch.OrderedOn`: the association lines of a tier do not cross.
* `TemplateMatch.links`: the lines of a tier as pairs of positions.

## Main results

* `TemplateMatch.orderedOn_iff`: `OrderedOn` is `Autosegmental.IsNonCrossing` with each slot
  hosting at most one element of the tier.
* `TemplateMatch.spellout_map`: relabelling the melodies relabels the surface segments.

## References

* [mccarthy-1981]
* [faust-2026]
* [goldsmith-1976]
-/

@[expose] public section

namespace Morphology

open Autosegmental

/-- The morphemic tier that the melody element at one end of an association line belongs to,
which is the consonantal root, the vocalism, or affixal material ([mccarthy-1981]). -/
inductive AssocSource where
  /-- The consonantal root tier. -/
  | root
  /-- The vocalic melody tier. -/
  | vocalism
  /-- An affixal tier ([faust-2026]'s intruders are sister-exponent affixal
  material in this sense). -/
  | affix
  deriving DecidableEq, Repr

/-- An association line from element `melodyIndex` of the melody of `source` to slot `slotIndex`
of the template ([mccarthy-1981]). The source defaults to `.root`. -/
structure Association where
  /-- The tier the associated melody element lives on. -/
  source : AssocSource := .root
  /-- The index of the melody element on its tier. -/
  melodyIndex : ℕ
  /-- The index of the template slot. -/
  slotIndex : ℕ
  deriving DecidableEq, Repr

/-- A consonantal root, a vocalism, and affixal material associated with a template. Candidate
realizations of the same morphemes differ only in their association lines. -/
structure TemplateMatch (α : Type*) where
  /-- The consonantal root. -/
  root : ConsonantalRoot α
  /-- The vocalic melody. -/
  vocalism : List α := []
  /-- The affixal material. -/
  affix : List α := []
  /-- The template. -/
  template : Skeleton
  /-- The association lines. -/
  associations : List Association
  deriving Repr, DecidableEq

namespace TemplateMatch

variable {α : Type*} (m : TemplateMatch α)

/-- The melody of a tier. -/
def melody : AssocSource → List α
  | .root => m.root.segments
  | .vocalism => m.vocalism
  | .affix => m.affix

/-- The segment an association line contributes, if its index is in range. -/
def segmentAt (a : Association) : Option α := (m.melody a.source)[a.melodyIndex]?

/-- The surface segments of the match. Each slot contributes the segment of its first
association line, and a slot with no association receives no phonetic realization
([mccarthy-1981]). -/
def spellout : List α :=
  (List.range m.template.length).filterMap fun i ↦
    (m.associations.find? (·.slotIndex == i)).bind m.segmentAt

/-- The C-slot positions not filled by any association. -/
def unfilledCSlots : List ℕ :=
  m.template.cSlots.filter fun i ↦ !m.associations.any (·.slotIndex == i)

/-- `m.allCSlotsFilled` asserts that every C-slot is filled by some
association line. -/
abbrev allCSlotsFilled : Prop := m.unfilledCSlots = []

/-- `m.OrderedOn s` asserts that distinct melody elements of tier `s` associate to slots in
melody order, so that the association lines from `s` do not cross ([goldsmith-1976]'s
no-crossing condition, within one tier). -/
def OrderedOn (s : AssocSource) : Prop :=
  ∀ a ∈ m.associations, ∀ b ∈ m.associations,
    a.source = s → b.source = s →
    a.melodyIndex < b.melodyIndex → a.slotIndex < b.slotIndex

instance : Decidable (m.allCSlotsFilled) := inferInstanceAs (Decidable (_ = _))

/-- `OrderedOn` is decided by one Boolean pass, which kernel `decide` evaluates faster than the
nested bounded quantifiers. -/
instance (s : AssocSource) : Decidable (m.OrderedOn s) :=
  decidable_of_iff (m.associations.all fun a ↦ m.associations.all fun b ↦
      !(a.source == s && b.source == s && decide (a.melodyIndex < b.melodyIndex)) ||
        decide (a.slotIndex < b.slotIndex)) <| by
    simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      beq_eq_false_iff_ne, decide_eq_false_iff_not, decide_eq_true_eq, OrderedOn]
    refine forall₂_congr fun a _ ↦ forall₂_congr fun b _ ↦ ?_
    by_cases h₁ : a.source = s <;> by_cases h₂ : b.source = s <;>
      simp [h₁, h₂, Decidable.imp_iff_not_or]

/-- The match with each melodic element relabeled. -/
def map {β : Type*} (f : α → β) : TemplateMatch β :=
  { root := m.root.map f, vocalism := m.vocalism.map f, affix := m.affix.map f,
    template := m.template, associations := m.associations }

section map

variable {β : Type*} (f : α → β)

@[simp] theorem associations_map : (m.map f).associations = m.associations := rfl

@[simp] theorem template_map : (m.map f).template = m.template := rfl

@[simp] theorem melody_map (s : AssocSource) : (m.map f).melody s = (m.melody s).map f := by
  cases s <;> rfl

theorem segmentAt_map (a : Association) : (m.map f).segmentAt a = (m.segmentAt a).map f := by
  simp [segmentAt, List.getElem?_map]

/-- Relabeling the melodic elements relabels the surface segments. -/
theorem spellout_map : (m.map f).spellout = m.spellout.map f := by
  simp only [spellout, associations_map, template_map, List.map_filterMap, segmentAt_map]
  congr 1
  funext i
  cases m.associations.find? (·.slotIndex == i) <;> simp

end map

/-! ### Interpretation into the autosegmental substrate -/

/-- The lines of tier `s` as `(melodyIndex, slotIndex)` pairs. -/
def links (s : AssocSource) : Finset (ℕ × ℕ) :=
  ((m.associations.filter (·.source = s)).map fun a ↦ (a.melodyIndex, a.slotIndex)).toFinset

@[simp] theorem mem_links {s : AssocSource} {p : ℕ × ℕ} :
    p ∈ m.links s ↔ ∃ a ∈ m.associations, a.source = s ∧ (a.melodyIndex, a.slotIndex) = p := by
  simp [links, and_assoc]

/-- A tier is `OrderedOn` iff its lines are non-crossing and each slot hosts at most one element
of the tier, which is [goldsmith-1976]'s No-Crossing Constraint plus [mccarthy-1981]'s
prohibition against many-to-one associations. -/
theorem orderedOn_iff (s : AssocSource) :
    m.OrderedOn s ↔ IsNonCrossing (m.links s : SetRel ℕ ℕ) ∧
      Set.InjOn Prod.snd (m.links s : Set (ℕ × ℕ)) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hnc, hinj⟩ a ha b hb has hbs hlt ↦ ?_⟩
  · rintro _ hp _ hq hlt
    obtain ⟨a, ha, has, rfl⟩ := m.mem_links.1 hp
    obtain ⟨b, hb, hbs, rfl⟩ := m.mem_links.1 hq
    exact (h a ha b hb has hbs hlt).le
  · rintro _ hp _ hq (hslot : _ = _)
    obtain ⟨a, ha, has, rfl⟩ := m.mem_links.1 hp
    obtain ⟨b, hb, hbs, rfl⟩ := m.mem_links.1 hq
    have := h a ha b hb has hbs
    have := h b hb a ha hbs has
    simp only [Prod.mk.injEq] at hslot ⊢
    omega
  · have hp : (a.melodyIndex, a.slotIndex) ∈ m.links s := m.mem_links.2 ⟨a, ha, has, rfl⟩
    have hq : (b.melodyIndex, b.slotIndex) ∈ m.links s := m.mem_links.2 ⟨b, hb, hbs, rfl⟩
    exact (hnc hp hq hlt).lt_of_ne fun h ↦ hlt.ne (congrArg Prod.fst (hinj hp hq h))

end TemplateMatch

end Morphology
