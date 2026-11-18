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
public import Mathlib.Order.WithBot
public import Mathlib.Data.Fintype.Option

/-!
# Person segments

Béjar and Rezac articulate the person probe into segments: the root `π`, which every nominal
bears, and the person features [participant], [speaker] and [addressee], each depending on the
one before it as in Harley and Ritter's geometry. A segment is thus
[a person feature or the root](##Person.Segment.ofFeature), and the segments a person bears are
the root and [its features](##Person.Segment.ofFeature_mem_spec) in the full inventory, so that
the second person bears [addressee] and the general first person [speaker] alone. They form a
tree, [a segment and those it depends on a chain](##Person.Segment.isChain_Iic). A language
specifies its persons on one such chain, [speaker] or [addressee], and
[what a probe over an inventory sees of a person](##Person.Segment.inter_spec) is the person's
bundle in that inventory.

## Implementation notes

`π` is Harley and Ritter's root Referring Expression node, which Deal writes `[φ]`, and the
segments are the person nodes of their geometry (`Morphology/FeatureGeometry.lean`). A segment
is a `WithBot Person.Feature`, so the order is that of the features with the root below them and
is not read off that geometry.

## References

* [harley-ritter-2002]
* [bejar-rezac-2009]
* [deal-2024]
-/

@[expose] public section

/-- A segment of the person feature: the root `π` or a person feature, ordered by dependency with
the root below the features. -/
abbrev Person.Segment := WithBot Person.Feature

namespace Person.Segment

/-- `π`, the root, borne by every nominal. -/
abbrev pi : Person.Segment := ⊥

/-- [participant], borne by the first and second persons. -/
abbrev participant : Person.Segment := WithBot.some .participant

/-- [speaker], borne by the persons that include the speaker. -/
abbrev speaker : Person.Segment := WithBot.some .speaker

/-- [addressee], borne by the persons that include the addressee. -/
abbrev addressee : Person.Segment := WithBot.some .addressee

/-- Case analysis on a segment: the root, [participant], [speaker] or [addressee]. -/
@[elab_as_elim]
def casesOn' {motive : Person.Segment → Sort*} (a : Person.Segment) (pi : motive pi)
    (participant : motive participant) (speaker : motive speaker) (addressee : motive addressee) :
    motive a :=
  match a with
  | ⊥ => pi
  | (f : Person.Feature) => f.casesOn' participant speaker addressee

/-- `Finset.Ici a` is the segment `a` and the segments that depend on it. -/
instance : LocallyFiniteOrderTop Person.Segment :=
  .ofIci' Person.Segment (fun a ↦ Finset.univ.filter (a ≤ ·)) fun _ _ ↦ by simp

/-- `Finset.Iic a` is the segment `a` and the segments it depends on, the least feature structure
containing `a`. -/
instance : LocallyFiniteOrderBot Person.Segment :=
  .ofIic' Person.Segment (fun a ↦ Finset.univ.filter (· ≤ a)) fun _ _ ↦ by simp

/-- The segments form a tree: the segments a segment depends on are comparable. -/
instance : IsForestOrder Person.Segment := ⟨by decide⟩

/-- A segment and the segments it depends on form a chain. -/
theorem isChain_Iic (a : Person.Segment) : IsChain (· ≤ ·) (↑(Finset.Iic a) : Set Person.Segment) :=
  fun _ hb _ hc _ ↦
    IsForestOrder.le_total_of_le_of_le (Finset.mem_Iic.1 hb) (Finset.mem_Iic.1 hc)

/-- A person feature as a segment, the dependency of the features being that of the segments. -/
def ofFeature : Person.Feature ↪o Person.Segment where
  toFun := WithBot.some
  inj' := WithBot.coe_injective
  map_rel_iff' := WithBot.coe_le_coe

/-- The segments a person bears: the root and its features in the full inventory. -/
def spec (p : Person) : Finset Person.Segment :=
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
theorem spec_isLowerSet (p : Person) : IsLowerSet (↑(spec p) : Set Person.Segment) := by
  revert p; decide

/-- A person bears [participant] iff it includes a speech-act participant. -/
theorem participant_mem_spec_iff {p : Person} : participant ∈ spec p ↔ p.IsSAP :=
  (ofFeature_mem_spec (f := .participant)).trans Person.isSAP_iff_participant.symm

/-- A person bears [speaker] iff it includes the speaker. -/
theorem speaker_mem_spec_iff {p : Person} : speaker ∈ spec p ↔ p.IncludesSpeaker :=
  (ofFeature_mem_spec (f := .speaker)).trans Person.includesSpeaker_iff_speaker.symm

end Person.Segment
