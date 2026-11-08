/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# The Givenness Hierarchy

A cognitive status is a condition on the addressee's knowledge and attention state with respect to
a referent, which a referring form signals. The Givenness Hierarchy ranks six of them, from *in
focus* down to *type identifiable*. The statuses are nested, each entailing every lower one, so a
referent's status is the highest it has, and it has status $t$ exactly when its status lies in
`Set.Ici t`.

## Implementation notes

A two-valued criterion read off the hierarchy is a cut `Set.Ici t`, and by
`IsUpperSet.eq_empty_or_Ici` the monotone ones are no others; a consumer states the cut it means
as `t ≤ s`. Discourse status (`DiscourseStatus`) is no such cut, since a status is not the means by
which a referent attains it. The scale of referring forms, rather than referents, is
`Discourse.AccessibilityLevel`.

## References

* [gundel-hedberg-zacharski-1993]
-/

@[expose] public section

/-- A cognitive status is a tier of the Givenness Hierarchy of [gundel-hedberg-zacharski-1993], a
condition on a referent that a referring form signals. A referent with a status has every lower
one. -/
inductive CognitiveStatus where
  /-- The referent is at the current center of attention, as zero and unstressed pronouns
  require. -/
  | inFocus
  /-- The referent is represented in current short-term memory (*that*, *this*, *this N*). -/
  | activated
  /-- The addressee already has a representation of the referent in memory, long-term or
  short-term, and so can uniquely identify it (*that N*). -/
  | familiar
  /-- The addressee can identify the speaker's intended referent from the nominal alone
  (*the N*). -/
  | uniquelyIdentifiable
  /-- The speaker intends to refer to a particular object (indefinite *this N*). -/
  | referential
  /-- The addressee can access a representation of the type of object described (*a N*). -/
  | typeIdentifiable
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace CognitiveStatus

/-- The rank of a status, higher for the more restrictive. -/
def rank : CognitiveStatus → ℕ
  | .inFocus              => 5
  | .activated            => 4
  | .familiar             => 3
  | .uniquelyIdentifiable => 2
  | .referential          => 1
  | .typeIdentifiable     => 0

/-- Each status entails every lower one, so the statuses form the chain
`typeIdentifiable < ⋯ < inFocus`. -/
instance : LinearOrder CognitiveStatus := LinearOrder.lift' rank (by decide)

end CognitiveStatus
