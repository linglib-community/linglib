/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Locality.Transfer

/-!
# Anti-locality

Anti-locality bars movement that is too short. Abels's version bars the complement of a head
from moving to a specifier of the head's phrase; Erlewine's bars a specifier from moving unless
it crosses a maximal projection other than the one it leaves, a projection being crossed when it
dominates the phrase that moves but not its landing site. With the PIC, Abels's version leaves the
complement of a phase head no way out, so that a phase head cannot be stranded.

## Main definitions

* `Minimalist.crossed`: the maximal projections a link of a chain crosses.
* `Minimalist.SpecToSpec`, `Minimalist.CompToSpec`: links too short in Erlewine's and in Abels's
  sense.

## Main results

* `Minimalist.compToSpec_or_mem_sealed`: a link that moves the complement of a phase head is
  Comp-to-Spec or leaves the positions the PIC seals.

## Implementation notes

* A link pairs the phrase that lands with the position of the lower copy (`Minimalist.links`); the
  phrase that moves is the projection of the lower copy.
* Erlewine restricts his version to Ā-movement. The definitions apply to any link, and an analysis
  picks the links it constrains.

## References

* [abels-2003]
* [erlewine-2016]
-/

@[expose] public section

namespace Minimalist

open Core.Order RoseTree

variable (hd : HeadFunction) (t : LinearizedSyntacticObject)

/-- A pronounced head occupies the position. -/
def IsHeadPosition (p : TreePath) : Prop := ∃ x ∈ tokenList t.val, x.1 = p

instance (p : TreePath) : Decidable (IsHeadPosition t p) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The maximal projections a link crosses, those dominating the phrase that moves but not its
landing site ([erlewine-2016]). -/
def crossed (x : TreePath × TreePath) : Finset TreePath :=
  ((projectionAt hd t x.2).toList.inits.map TreePath.mk).toFinset.filter fun Y ↦
    Y ∈ maximalProjections hd t ∧ x.1.parent < Y ∧ Y < projectionAt hd t x.2

/-- A link moves a specifier, a phrase whose sister is no head, across no maximal projection but
the one it leaves, which [erlewine-2016]'s Spec-to-Spec anti-locality bans. -/
def SpecToSpec (x : TreePath × TreePath) : Prop :=
  projectionAt hd t x.2 ≠ ⊥ ∧ ¬ IsHeadPosition t (complement (projectionAt hd t x.2)) ∧
    (crossed hd t x).card ≤ 1

instance (x : TreePath × TreePath) : Decidable (SpecToSpec hd t x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A link moves the complement of a head to a specifier of the head's phrase, which
[abels-2003]'s anti-locality bans. -/
def CompToSpec (x : TreePath × TreePath) : Prop :=
  IsHeadPosition t (complement (projectionAt hd t x.2)) ∧
    projectionAt hd t (complement (projectionAt hd t x.2)) ≤ x.1.parent

instance (x : TreePath × TreePath) : Decidable (CompToSpec hd t x) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {hd t}

/-- A link that moves the complement of a phase head, landing outside it, moves it to a
specifier of the head's phrase or leaves the complement after the phase is complete: with the
PIC, Abels's anti-locality leaves the complement of a phase head no way out. -/
theorem compToSpec_or_mem_sealed {tok : LexicalItem.Token} {x : TreePath × TreePath}
    {h : TreePath} (hh : h ∈ t.val.validPaths) (h0 : h ≠ ⊥) (hhead : IsHeadPosition t h)
    (hx : x ∈ links hd t tok) (hr : projectionAt hd t x.2 = complement h)
    (hin : ¬ complement h ≤ x.1.parent) :
    CompToSpec hd t x ∨ x.2 ∈ sealed {h} (complementDomain hd t ∅) (Pic1 hd t) x.1.parent := by
  have hcx : complement h ≤ x.2 := hr ▸ projectionAt_le hd t x.2
  have hlt : x.1.parent < complement h :=
    ((IsLeftLinear.comparable_of_le_common (parent_lt_of_mem_links hx).1.le hcx).resolve_right
      hin).lt_of_ne fun he ↦ hin he.ge
  have hle : x.1.parent ≤ h.parent := by
    simpa [TreePath.pred_eq_parent] using Order.le_pred_of_lt hlt
  have hcomp : CompToSpec hd t x ↔ projectionAt hd t h ≤ x.1.parent := by
    rw [CompToSpec, hr, complement_complement hh h0]
    exact and_iff_right hhead
  rcases IsLeftLinear.comparable_of_le_common (projectionAt_le hd t h)
    (hle.trans (TreePath.parent_le h)) with hph | hph
  · exact .inl (hcomp.2 hph)
  · rcases hph.lt_or_eq with hph | hph
    · refine .inr ⟨h, Finset.mem_singleton_self h, hph, ?_⟩
      simpa [complementDomain, transferHead] using hcx
    · exact .inl (hcomp.2 hph.ge)

end Minimalist
