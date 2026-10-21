/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Agreement.Geometry
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Person segments

The person features that Agree manipulates are the person nodes of Harley and Ritter's feature
geometry: the root `π`, which every nominal bears, [participant], and its dependents [speaker]
and [addressee]. Béjar and Rezac call them the segments of an articulated person probe. The
segments a person bears are read off the geometry, a bare [participant] receiving [speaker] by
default.

## Main definitions

* `Minimalist.PersonSegment`: the person segments, ordered by the dominance of the geometry.
* `Minimalist.PersonSegment.toNode`: a segment as a node of the geometry.
* `Minimalist.PersonSegment.spec`: the segments a person bears.

## Main results

* `Minimalist.PersonSegment.spec_isLowerSet`: a person bears whatever its segments depend on.
* `Minimalist.PersonSegment.participant_mem_spec_iff`,
  `Minimalist.PersonSegment.speaker_mem_spec_iff`: the segments [participant] and [speaker] are
  `Person.IsSAP` and `Person.IncludesSpeaker`.

## Implementation notes

`π` is Harley and Ritter's root Referring Expression node, which Deal writes `[φ]`.

## References

* [harley-ritter-2002]
* [bejar-rezac-2009]
* [deal-2024]
-/

@[expose] public section

namespace Minimalist

open Phi.Geometry

/-- A segment of the person feature, a person node of the geometry of [harley-ritter-2002]. -/
inductive PersonSegment where
  /-- `π`, the root, borne by every nominal. -/
  | pi
  /-- [participant], borne by the first and second persons. -/
  | participant
  /-- [speaker], borne by the persons that include the speaker. -/
  | speaker
  /-- [addressee], borne by the persons that include the addressee. -/
  | addressee
  deriving DecidableEq, Repr, Fintype

namespace PersonSegment

/-- The node of the geometry a segment is. -/
def toNode : PersonSegment → Node
  | .pi => ⊥
  | .participant => .participant
  | .speaker => .speaker
  | .addressee => .addressee

theorem toNode_injective : Function.Injective toNode := by decide

/-- Segments are ordered by the dominance of the geometry, `a ≤ b` when `b` depends on `a`. -/
instance : PartialOrder PersonSegment := PartialOrder.lift toNode toNode_injective

instance : DecidableLE PersonSegment := fun a b ↦ inferInstanceAs (Decidable (a.toNode ≤ b.toNode))

instance : OrderBot PersonSegment where
  bot := .pi
  bot_le := by decide

/-- `Finset.Ici a` is the segment `a` and the segments it dominates. -/
instance : LocallyFiniteOrderTop PersonSegment :=
  .ofIci' PersonSegment (fun a ↦ Finset.univ.filter (a ≤ ·)) fun _ _ ↦ by simp

/-- The segments a person bears, the nodes of its geometry. -/
def spec (p : Person) : Finset PersonSegment := Finset.univ.filter (·.toNode ∈ personFeatures p)

theorem mem_spec {s : PersonSegment} {p : Person} : s ∈ spec p ↔ s.toNode ∈ personFeatures p := by
  simp [spec]

@[simp] theorem pi_mem_spec (p : Person) : pi ∈ spec p := mem_spec.2 (bot_mem_personFeatures p)

/-- A person bears whatever its segments depend on. -/
theorem spec_isLowerSet (p : Person) : IsLowerSet (↑(spec p) : Set PersonSegment) :=
  fun _ _ h ha ↦ mem_spec.2 (personFeatures_isLowerSet p h (mem_spec.1 ha))

/-- A person bears [participant] iff it includes a speech-act participant. -/
theorem participant_mem_spec_iff {p : Person} : participant ∈ spec p ↔ p.IsSAP := by
  revert p; decide

/-- A person bears [speaker] iff it includes the speaker, a bare [participant] receiving [speaker]
by default. -/
theorem speaker_mem_spec_iff {p : Person} : speaker ∈ spec p ↔ p.IncludesSpeaker := by
  revert p; decide

end PersonSegment

end Minimalist
