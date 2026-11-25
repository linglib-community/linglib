/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Feature.Person.Segment
public import Linglib.Syntax.Clause.Scenario
public import Linglib.Syntax.Minimalist.Probe.Agree

/-!
# Cyclic Agree over articulated person probes

An articulated person probe is a set of unvalued person segments, in the simplest case a segment
together with the segments it entails, `Finset.Iic x`. A probe on v first meets the internal
argument, which checks every segment it bears; the segments left over, the residue, probe again
from the next projection of v, where the external argument is the closest goal. A context, the
scenario of the external over the internal argument, is inverse when the internal argument is at
least as specified as the external one relative to the probe (`Minimalist.SpecLE`), so that
nothing is left for the external argument to check, and direct otherwise.

## Implementation notes

Béjar and Rezac specify persons per language, a second person as [participant] alone where
the first bears [speaker] and a first person so where the second bears [addressee]. Here a
person bears its whole specification `Person.Segment.spec`, and a probe sees of it the segments
the probe has, which are the person's specification in the probe's features
(`Person.Segment.inter_spec`). The language's choice is therefore carried by its probe,
`Finset.Iic .speaker` or `Finset.Iic .addressee`, and not by a second parameter.

## References

* [bejar-rezac-2009]
* [harley-ritter-2002]
* [coon-keine-2021]
-/

@[expose] public section

namespace Minimalist

/-! ### Specification relative to a set of features -/

section SpecLE

variable {F : Type*} [DecidableEq F] {P Q s t u : Finset F}

/-- Relative to the features `P`, the feature set `t` is at least as specified as `s`: it has
every feature of `P` that `s` has. With `P` the segments of a probe, this compares two goals
"relative to the specification of the probe" ([coon-keine-2021]). -/
def SpecLE (P s t : Finset F) : Prop := P ∩ s ⊆ t

instance : Decidable (SpecLE P s t) := inferInstanceAs (Decidable (P ∩ s ⊆ t))

theorem specLE_iff : SpecLE P s t ↔ ∀ x ∈ P, x ∈ s → x ∈ t := by
  simp [SpecLE, Finset.subset_iff]

@[refl] theorem SpecLE.refl (P s : Finset F) : SpecLE P s s := Finset.inter_subset_right

@[trans] theorem SpecLE.trans (h₁ : SpecLE P s t) (h₂ : SpecLE P t u) : SpecLE P s u :=
  fun _ hx ↦ h₂ (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).1, h₁ hx⟩)

/-- Fewer features tell fewer feature sets apart. -/
theorem SpecLE.anti (h : P ⊆ Q) (hQ : SpecLE Q s t) : SpecLE P s t :=
  (Finset.inter_subset_inter_right h).trans hQ

theorem SpecLE.of_subset (h : s ⊆ t) : SpecLE P s t := Finset.inter_subset_right.trans h

@[simp] theorem specLE_univ [Fintype F] : SpecLE Finset.univ s t ↔ s ⊆ t := by simp [SpecLE]

theorem SpecLE.card_le (h : SpecLE P s t) : (P ∩ s).card ≤ (P ∩ t).card :=
  Finset.card_le_card (Finset.subset_inter Finset.inter_subset_left h)

variable [Preorder F]

/-- On a chain of features any two lower sets are comparable. -/
theorem specLE_total (hP : IsChain (· ≤ ·) (P : Set F)) (hs : IsLowerSet (s : Set F))
    (ht : IsLowerSet (t : Set F)) : SpecLE P s t ∨ SpecLE P t s := by
  by_contra! h
  simp only [SpecLE, Finset.not_subset, Finset.mem_inter] at h
  obtain ⟨⟨x, ⟨hx, hxs⟩, hxt⟩, y, ⟨hy, hyt⟩, hys⟩ := h
  rcases hP.total hx hy with hxy | hyx
  · exact hxt (ht hxy hyt)
  · exact hys (hs hyx hxs)

/-- On a chain of features lower sets are compared by how many of the features they have. -/
theorem specLE_iff_card_le (hP : IsChain (· ≤ ·) (P : Set F)) (hs : IsLowerSet (s : Set F))
    (ht : IsLowerSet (t : Set F)) : SpecLE P s t ↔ (P ∩ s).card ≤ (P ∩ t).card := by
  refine ⟨SpecLE.card_le, fun h ↦ (specLE_total hP hs ht).elim id fun hts ↦ ?_⟩
  rw [SpecLE, ← Finset.eq_of_subset_of_card_le (Finset.subset_inter Finset.inter_subset_left hts) h]
  exact Finset.inter_subset_right

end SpecLE

/-- The third person, bearing the root alone, is the least specified person on any segments. -/
theorem specLE_third (P : Finset Person.Segment) (q : Person) :
    SpecLE P (Person.Segment.spec .third) (Person.Segment.spec q) :=
  .of_subset fun x hx ↦ by
    rw [show Person.Segment.spec Person.third = {.pi} by decide, Finset.mem_singleton] at hx
    exact hx ▸ Person.Segment.pi_mem_spec q

end Minimalist

namespace Minimalist.CyclicAgree

open Person.Segment
open Clause (Scenario)

variable (P : Finset Person.Segment) (s : Scenario Person) (p q : Person) {x : Person.Segment}

/-! ### The residue and the two kinds of context -/

/-- A context, the scenario of the external over the internal argument, is inverse when the
internal argument is at least as specified as the external one relative to the probe, so that it
leaves no residue the external argument could check. -/
def IsInverse : Prop := SpecLE P (spec s.high) (spec s.low)

/-- A context is direct when it is not inverse: the external argument bears some segment of the
residue the internal argument leaves. -/
def IsDirect : Prop := ¬ IsInverse P s

instance : DecidablePred (IsInverse P) := fun _ ↦ inferInstanceAs (Decidable (SpecLE P _ _))

instance : DecidablePred (IsDirect P) := fun _ ↦ inferInstanceAs (Decidable (¬ _))

variable {P s}

@[simp] theorem not_isDirect : ¬ IsDirect P s ↔ IsInverse P s := not_not

theorem isDirect_iff : IsDirect P s ↔ ∃ x ∈ P, x ∉ spec s.low ∧ x ∈ spec s.high := by
  simp only [IsDirect, IsInverse, specLE_iff, not_forall]
  exact ⟨fun ⟨x, hx, hh, hl⟩ ↦ ⟨x, hx, hl, hh⟩, fun ⟨x, hx, hl, hh⟩ ↦ ⟨x, hx, hh, hl⟩⟩

variable (P) in
theorem isInverse_self : IsInverse P ⟨p, p⟩ := .refl P _

/-- A probe with more segments has more direct contexts. -/
theorem IsDirect.mono {Q : Finset Person.Segment} (h : P ⊆ Q) (hd : IsDirect P s) :
    IsDirect Q s :=
  fun hi ↦ hd (hi.anti h)

/-- An internal argument bearing every segment of the probe leaves no residue. -/
theorem isInverse_of_subset (h : P ⊆ spec s.low) : IsInverse P s :=
  Finset.inter_subset_left.trans h

variable (s) in
/-- The flat probe `[uπ]` makes every context inverse, since every internal argument bears `π`. -/
theorem isInverse_Iic_bot : IsInverse (Finset.Iic ⊥) s :=
  isInverse_of_subset fun x hx ↦ by
    rw [Finset.mem_Iic, le_bot_iff] at hx
    exact hx ▸ pi_mem_spec s.low

end Minimalist.CyclicAgree
