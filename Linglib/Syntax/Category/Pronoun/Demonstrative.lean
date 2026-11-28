/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Discourse.SpeechAct.Role
public import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Demonstrative pronouns

A demonstrative pronoun is a pronoun with deictic content: the participant sets of the referents in
whose vicinity it locates its referent. Harbour finds that the deixis of objects, spaces and paths
attests the five partitions of person and, in the descriptions he has read, no others, so the
content is a class of one of them, as a person value's `Person.participantSets` is. English *this*
covers the sets containing the speaker and *that* the others; Catalan *aquest* covers every set with
a participant and *aquell* the empty one; Latin *hic*, *iste* and *ille* separate the speaker's, the
addressee's and the others'; and French *celui*, which enters no deictic opposition without a
locative, covers every set. German *der*, *die* and *das*, traditionally called demonstrative
pronouns, encode no deixis on Patel-Grosz and Grosz's analysis and are `PersonalPronoun`s here.

## References

* [harbour-2016]
* [terenghi-2023]
* [patel-grosz-grosz-2017]
-/

@[expose] public section

/-- A demonstrative pronoun is a `Pronoun` with its deictic content, the participant sets of the
referents in whose vicinity it locates its referent. -/
@[ext]
structure DemonstrativePronoun extends Pronoun where
  /-- The participant sets of the referents in whose vicinity the form locates its referent. -/
  deixis : Finset (Finset SpeechAct.Role)

instance : DecidableEq DemonstrativePronoun :=
  fun _ _ ↦ decidable_of_iff _ DemonstrativePronoun.ext_iff.symm
