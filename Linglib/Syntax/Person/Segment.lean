/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.ForestOrder
public import Linglib.Syntax.Person.Features
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Tactic.DeriveFintype

/-!
# Person segments

Béjar and Rezac articulate the person probe into segments: the root `π`, which every nominal
bears, and the person features [participant], [speaker] and [addressee], each depending on the
one before it as in Harley and Ritter's geometry. A segment is thus
[a person feature or the root](##PersonSegment.ofFeature), and the segments a person bears are
the root and [its features](##PersonSegment.ofFeature_mem_spec) in the full inventory, so that
the second person bears [addressee] and the general first person [speaker] alone. They form a
tree, [a segment and those it depends on a chain](##PersonSegment.isChain_Iic). A language
specifies its persons on one such chain, [speaker] or [addressee], and
[what a probe over an inventory sees of a person](##PersonSegment.inter_spec) is the person's
bundle in that inventory.

## Implementation notes

`π` is Harley and Ritter's root Referring Expression node, which Deal writes `[φ]`, and the
segments are the person nodes of their geometry (`Morphology/FeatureGeometry.lean`). The order is
defined here and not read off that geometry, so that the person features do not depend on it.

## References

* [harley-ritter-2002]
* [bejar-rezac-2009]
* [deal-2024]
-/

@[expose] public section

/-- A segment of the person feature: the root or a person feature. -/
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

/-- Segments are ordered by dependency, `a ≤ b` when `b` depends on `a`: the root below
[participant], and [participant] below [speaker] and [addressee]. -/
instance : PartialOrder PersonSegment where
  le a b := a = b ∨ a = pi ∨ (a = participant ∧ b ≠ pi)
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE PersonSegment :=
  fun a b ↦ inferInstanceAs (Decidable (a = b ∨ a = pi ∨ (a = participant ∧ b ≠ pi)))

instance : OrderBot PersonSegment where
  bot := .pi
  bot_le := by decide

/-- `Finset.Ici a` is the segment `a` and the segments that depend on it. -/
instance : LocallyFiniteOrderTop PersonSegment :=
  .ofIci' PersonSegment (fun a ↦ Finset.univ.filter (a ≤ ·)) fun _ _ ↦ by simp

/-- `Finset.Iic a` is the segment `a` and the segments it depends on, the least feature structure
containing `a`. -/
instance : LocallyFiniteOrderBot PersonSegment :=
  .ofIic' PersonSegment (fun a ↦ Finset.univ.filter (· ≤ a)) fun _ _ ↦ by simp

/-- The segments form a tree: the segments a segment depends on are comparable. -/
instance : IsForestOrder PersonSegment := ⟨by decide⟩

/-- A segment and the segments it depends on form a chain. -/
theorem isChain_Iic (a : PersonSegment) : IsChain (· ≤ ·) (↑(Finset.Iic a) : Set PersonSegment) :=
  fun _ hb _ hc _ ↦
    IsForestOrder.le_total_of_le_of_le (Finset.mem_Iic.1 hb) (Finset.mem_Iic.1 hc)

/-- A person feature as a segment, the dependency of the features being that of the segments. -/
def ofFeature : Person.Feature ↪o PersonSegment where
  toFun
    | .participant => participant
    | .speaker => speaker
    | .addressee => addressee
  inj' := by decide
  map_rel_iff' := by decide

/-- The segments a person bears: the root and its features in the full inventory. -/
def spec (p : Person) : Finset PersonSegment :=
  insert pi ((p.toFeatures Finset.univ).map ofFeature.toEmbedding)

@[simp] theorem pi_mem_spec (p : Person) : pi ∈ spec p := Finset.mem_insert_self _ _

/-- A person bears a feature as a segment exactly when the feature is in its bundle. -/
@[simp] theorem ofFeature_mem_spec {p : Person} {f : Person.Feature} :
    ofFeature f ∈ spec p ↔ f ∈ p.toFeatures Finset.univ := by
  revert p f; decide

/-- The segments of a probe over the features `F` that a person bears are the root and the
person's bundle in `F`. A probe articulated to [speaker] thus sees a second person as [participant]
alone, and one articulated to [addressee] sees a first person so, the two person specifications
of [bejar-rezac-2009]. -/
theorem inter_spec (F : Person.Features) (p : Person) :
    insert pi (F.map ofFeature.toEmbedding) ∩ spec p =
      insert pi ((p.toFeatures F).map ofFeature.toEmbedding) := by
  revert F p; decide

/-- A person bears whatever its segments depend on. -/
theorem spec_isLowerSet (p : Person) : IsLowerSet (↑(spec p) : Set PersonSegment) := by
  revert p; decide

/-- A person bears [participant] iff it includes a speech-act participant. -/
theorem participant_mem_spec_iff {p : Person} : participant ∈ spec p ↔ p.IsSAP :=
  (ofFeature_mem_spec (f := .participant)).trans Person.isSAP_iff_participant.symm

/-- A person bears [speaker] iff it includes the speaker. -/
theorem speaker_mem_spec_iff {p : Person} : speaker ∈ spec p ↔ p.IncludesSpeaker :=
  (ofFeature_mem_spec (f := .speaker)).trans Person.includesSpeaker_iff_speaker.symm

end PersonSegment
