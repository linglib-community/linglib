/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Agreement.Geometry
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Tactic.DeriveFintype

/-!
# Person segments

The person features that Agree manipulates are the person nodes of Harley and Ritter's feature
geometry: the root `π`, which every nominal bears, [participant], and its dependents [speaker]
and [addressee]. Béjar and Rezac call them the segments of an articulated person probe. The
segments a person bears are read off the geometry, a bare [participant] receiving [speaker] by
default.

## Main definitions

* `Phi.PersonSegment`: the person segments, ordered by the dominance of the geometry.
* `Phi.PersonSegment.toNode`: a segment as a node of the geometry.
* `Phi.PersonSegment.spec`: the segments a person bears.
* `Phi.PersonSegment.SpecLE`: one person is at least as specified as another relative to a set
  of segments.

## Main results

* `Phi.PersonSegment.spec_isLowerSet`: a person bears whatever its segments depend on.
* `Phi.PersonSegment.isChain_Iic`: a segment and the segments it depends on form a chain.
* `Phi.PersonSegment.specLE_total`, `Phi.PersonSegment.specLE_iff_card_le`: on a chain of segments
  persons are totally ordered, by the number of the segments they bear.
* `Phi.PersonSegment.participant_mem_spec_iff`,
  `Phi.PersonSegment.speaker_mem_spec_iff`: the segments [participant] and [speaker] are
  `Person.IsSAP` and `Person.IncludesSpeaker`.

## Implementation notes

`π` is Harley and Ritter's root Referring Expression node, which Deal writes `[φ]`.

## References

* [harley-ritter-2002]
* [bejar-rezac-2009]
* [deal-2024]
* [coon-keine-2021]
-/

@[expose] public section

namespace Phi

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

/-- `Finset.Iic a` is the segment `a` and the segments it depends on, the least feature structure
containing `a`. -/
instance : LocallyFiniteOrderBot PersonSegment :=
  .ofIic' PersonSegment (fun a ↦ Finset.univ.filter (· ≤ a)) fun _ _ ↦ by simp

/-- The geometry is a tree: the segments a segment depends on are comparable. -/
theorem le_total_of_le {a b c : PersonSegment} : a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a := by
  decide +revert

/-- A segment and the segments it depends on form a chain. -/
theorem isChain_Iic (a : PersonSegment) : IsChain (· ≤ ·) (↑(Finset.Iic a) : Set PersonSegment) :=
  fun _ hb _ hc _ ↦ le_total_of_le (Finset.mem_Iic.1 hb) (Finset.mem_Iic.1 hc)

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

/-! ### Specification relative to a set of segments -/

/-- Relative to the segments `P`, the person `q` is at least as specified as `p`: it bears every
segment of `P` that `p` bears. With `P` the segments of a probe, this compares two goals
"relative to the specification of the probe" ([coon-keine-2021]). -/
def SpecLE (P : Finset PersonSegment) (p q : Person) : Prop := P ∩ spec p ⊆ spec q

variable {P Q : Finset PersonSegment} {p q r : Person}

instance : Decidable (SpecLE P p q) := inferInstanceAs (Decidable (P ∩ spec p ⊆ spec q))

theorem specLE_iff : SpecLE P p q ↔ ∀ x ∈ P, x ∈ spec p → x ∈ spec q := by
  simp [SpecLE, Finset.subset_iff]

@[refl] theorem SpecLE.refl (P : Finset PersonSegment) (p : Person) : SpecLE P p p :=
  Finset.inter_subset_right

@[trans] theorem SpecLE.trans (h₁ : SpecLE P p q) (h₂ : SpecLE P q r) : SpecLE P p r :=
  fun _ hx ↦ h₂ (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).1, h₁ hx⟩)

/-- Fewer segments compare fewer persons apart. -/
theorem SpecLE.anti (h : P ⊆ Q) (hq : SpecLE Q p q) : SpecLE P p q :=
  (Finset.inter_subset_inter_right h).trans hq

theorem SpecLE.of_subset (h : spec p ⊆ spec q) : SpecLE P p q := Finset.inter_subset_right.trans h

@[simp] theorem specLE_univ : SpecLE Finset.univ p q ↔ spec p ⊆ spec q := by simp [SpecLE]

/-- The third person, bearing the root alone, is the least specified person on any segments. -/
theorem specLE_third (P : Finset PersonSegment) (q : Person) : SpecLE P .third q :=
  .of_subset fun x hx ↦ by
    rw [show spec Person.third = {pi} by decide, Finset.mem_singleton] at hx
    exact hx ▸ pi_mem_spec q

/-- On a chain of segments any two persons are comparable, since a person's segments are closed
under dependence. -/
theorem specLE_total (hP : IsChain (· ≤ ·) (P : Set PersonSegment)) (p q : Person) :
    SpecLE P p q ∨ SpecLE P q p := by
  by_contra! h
  simp only [SpecLE, Finset.not_subset, Finset.mem_inter] at h
  obtain ⟨⟨x, ⟨hx, hxp⟩, hxq⟩, y, ⟨hy, hyq⟩, hyp⟩ := h
  rcases hP.total hx hy with hxy | hyx
  · exact hxq (spec_isLowerSet q hxy hyq)
  · exact hyp (spec_isLowerSet p hyx hxp)

theorem SpecLE.card_le (h : SpecLE P p q) : (P ∩ spec p).card ≤ (P ∩ spec q).card :=
  Finset.card_le_card (Finset.subset_inter Finset.inter_subset_left h)

/-- On a chain of segments persons are compared by how many of the segments they bear. -/
theorem specLE_iff_card_le (hP : IsChain (· ≤ ·) (P : Set PersonSegment)) :
    SpecLE P p q ↔ (P ∩ spec p).card ≤ (P ∩ spec q).card := by
  refine ⟨SpecLE.card_le, fun h ↦ (specLE_total hP p q).elim id fun hqp ↦ ?_⟩
  rw [SpecLE, ← Finset.eq_of_subset_of_card_le (Finset.subset_inter Finset.inter_subset_left hqp) h]
  exact Finset.inter_subset_right

end PersonSegment

end Phi
