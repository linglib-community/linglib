/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Verbal.Voice
public import Linglib.Syntax.Voice.Basic

/-!
# The voice a Voice head derives

This file defines the voice that a Voice head derives from the transitive construction. Expletive
Voice leaves the external argument out of participant structure and makes the internal argument
the subject, the anticausative. A thematic head whose variable is implicit makes the internal
argument the subject while keeping the external one implied, the passive. A thematic head whose
specifier receives the external argument keeps it as the subject and leaves the internal argument
where it is realized, so that the active, the antipassive, the reflexive and the reciprocal differ
in the realization of the internal argument, not in the head.

## Main definitions

* `Minimalist.Voice.Head.diathesis`: the voice a head derives, given the position of the internal
  argument.

## Main results

* `Minimalist.Voice.Head.diathesis_of_not_isThematic`: expletive Voice derives the anticausative.
* `Minimalist.Voice.Head.diathesis_of_externalImplicit`: an implicit variable derives the passive.
* `Minimalist.Voice.Head.diathesis_reflexive`: a θ-assigning head over an implicit reflexive object
  derives the reflexive.

## References

* [alexiadou-anagnostopoulou-schaefer-2015]
* [creissels-2024]
* [coon-2019]
-/

@[expose] public section

namespace Minimalist.Voice.Head

open ArgumentFrame (Position)

variable (h : Head)

/-- The voice `h` derives from the transitive construction with the internal argument at `p`,
`none` when it is absent. Expletive Voice derives the anticausative, a thematic head with an
implicit variable the passive, and a θ-assigning head keeps the external argument as subject with
the internal argument at `p`, as in the stems of [coon-2019]. -/
def diathesis (p : Option Position) : _root_.Voice :=
  match h.thematic with
  | none => .anticausative
  | some _ =>
    if h.implicit then .passive
    else .of .np ⟨some .nominal, p.toList⟩ [some .external, p.map fun _ ↦ .complement 0]

variable {h} (p : Option Position)

theorem diathesis_of_not_isThematic (hh : ¬ h.IsThematic) :
    h.diathesis p = _root_.Voice.anticausative := by
  simp_all [diathesis, IsThematic]

theorem diathesis_of_externalImplicit (ht : h.IsThematic) (hi : h.ExternalImplicit) :
    h.diathesis p = _root_.Voice.passive := by
  obtain ⟨i, hi'⟩ := Option.isSome_iff_exists.1 ht
  simp_all [diathesis, ExternalImplicit]

theorem diathesis_of_assignsTheta (hh : h.AssignsTheta) :
    h.diathesis p =
      .of .np ⟨some .nominal, p.toList⟩ [some .external, p.map fun _ ↦ .complement 0] := by
  obtain ⟨ht, hi⟩ := hh
  obtain ⟨i, hi'⟩ := Option.isSome_iff_exists.1 ht
  simp_all [diathesis, ExternalImplicit]

/-- A θ-assigning head derives the active with a nominal object. -/
theorem diathesis_nominal (hh : h.AssignsTheta) :
    h.diathesis (some .nominal) = _root_.Voice.active := by
  rw [diathesis_of_assignsTheta _ hh]; decide

/-- A θ-assigning head derives the antipassive with its object at `q`. -/
theorem diathesis_antipassive (hh : h.AssignsTheta) (q : Position) :
    h.diathesis (some q) = _root_.Voice.antipassive q := by
  rw [diathesis_of_assignsTheta _ hh]; rfl

/-- A θ-assigning head derives the reflexive with an implicit object understood as its
subject. -/
theorem diathesis_reflexive (hh : h.AssignsTheta) :
    h.diathesis (some (.implicit (some .reflexive))) = _root_.Voice.reflexive := by
  rw [diathesis_of_assignsTheta _ hh]; decide

/-- A θ-assigning head derives the reciprocal with an implicit object understood as its
subject's members. -/
theorem diathesis_reciprocal (hh : h.AssignsTheta) :
    h.diathesis (some (.implicit (some .reciprocal))) = _root_.Voice.reciprocal := by
  rw [diathesis_of_assignsTheta _ hh]; decide

end Minimalist.Voice.Head
