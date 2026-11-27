/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Verbal.LittleV

/-!
# Applicative heads

This file defines the applicative heads, which introduce applied arguments such as benefactives,
recipients and affected datives, and the sites in an event structure where they merge. Pylkkänen
distinguishes a high applicative, relating the applied argument to the event, from a low one,
relating it to the theme; Cuervo adds a low applicative of static possession and the affected
applicative, a head of the high kind that takes a result state as its complement under the
dynamic event that embeds it. A head is thus high or low by what it relates the applied argument
to, and affected by where it merges: a site is a position in the chain of little v heads, and
its type is read off its two neighbours, the head that takes ApplP as its complement and the head
of Appl's own complement.

## Main definitions

* `Minimalist.Appl.Head`: the high and low applicative heads.
* `Minimalist.Appl.Site`: a position in an event structure, with neighbours `selector` and
  `complementHead`.
* `Minimalist.Appl.Site.Low`, `Minimalist.Appl.Site.Affected`, `Minimalist.Appl.Site.High`: the
  three types of site.

## Main results

* `Minimalist.Appl.Site.low_or_affected_or_high`: every site in a nonempty structure has a type.

## Implementation notes

Cuervo defines the affected applicative as one taking a stative vP. Any site with two neighbours
counts as affected here, as her remark on causatives embedding an activity or a change has it.
Pylkkänen's high applicative takes a VP and Cuervo's a vP, so the category of Appl's complement is
left to the studies.

## References

* [pylkkanen-2008]
* [cuervo-2003]
-/

@[expose] public section

namespace Minimalist.Appl

/-! ### Applicative heads -/

/-- The relation a low applicative establishes between the applied argument and the theme: a
transfer to a recipient or from a source, or static possession. -/
inductive LowRelation where
  | recipient
  | source
  | possessor
  deriving DecidableEq, Repr

/-- An applicative head is high, relating the applied argument to the eventuality its complement
describes, or low, relating it to the theme. -/
inductive Head where
  | high
  | low (relation : LowRelation)
  deriving DecidableEq, Repr

/-! ### Sites -/

/-- A site in an event structure: the verbal heads above ApplP and the verbal heads of Appl's
complement, each highest first. -/
structure Site where
  above : List LittleV
  below : List LittleV
  deriving DecidableEq, Repr

namespace Site

variable (s : Site)

/-- The event structure the site is in. -/
def heads : List LittleV := s.above ++ s.below

/-- The head that takes ApplP as its complement, `none` when Voice or Tense takes it. -/
def selector : Option LittleV := s.above.getLast?

/-- The head of Appl's complement, `none` when the complement is the theme DP. -/
def complementHead : Option LittleV := s.below.head?

/-- A site is low when Appl takes the theme DP as its complement. -/
def Low : Prop := s.below = []

/-- A site is high when no verbal head takes ApplP as its complement. -/
def High : Prop := s.above = []

/-- A site is affected when Appl takes a vP as its complement and a verbal head takes ApplP, so
the applied argument participates in two events. -/
def Affected : Prop := s.above ≠ [] ∧ s.below ≠ []

instance : DecidablePred Low := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred High := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred Affected := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The sites in the structure `l`, from the highest. -/
def all (l : List LittleV) : List Site :=
  (List.range (l.length + 1)).map fun i ↦ ⟨l.take i, l.drop i⟩

variable {s} {l : List LittleV} {r : LowRelation}

theorem complementHead_eq_none_iff : s.complementHead = none ↔ s.Low := List.head?_eq_none_iff

theorem selector_eq_none_iff : s.selector = none ↔ s.High := List.getLast?_eq_none_iff

theorem Affected.not_low (h : s.Affected) : ¬ s.Low := h.2

theorem Affected.not_high (h : s.Affected) : ¬ s.High := h.1

/-- The types exhaust the sites in a nonempty structure. -/
theorem low_or_affected_or_high (h : s.heads ≠ []) : s.Low ∨ s.Affected ∨ s.High := by
  by_cases hb : s.below = [] <;> by_cases ha : s.above = [] <;>
    simp_all [heads, Low, Affected, High]

theorem mem_all_iff : s ∈ all l ↔ s.heads = l := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    exact List.take_append_drop i l
  · subst h
    exact List.mem_map.2 ⟨s.above.length,
      List.mem_range.2 (by simp only [heads, List.length_append]; omega), by simp [heads]⟩

end Site

end Minimalist.Appl
