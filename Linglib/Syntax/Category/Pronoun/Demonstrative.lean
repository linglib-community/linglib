/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Feature.Person.Valued
public import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Demonstrative pronouns

A demonstrative pronoun is a pronoun with deictic content: the person feature value of the
referents in whose vicinity it locates its referent. English *this* is [+speaker] and *that*
[−speaker]; Catalan *aquest* is [+participant] and *aquell* [−participant]; Latin *hic*, *iste*
and *ille* are [+speaker], [+addressee] and [−participant]; and French *celui*, which enters no
deictic opposition without a locative, has no deictic content. A degree of distance, as the
medial term of a distance-oriented system has, is not recorded. German *der*, *die* and *das*, traditionally called demonstrative
pronouns, encode no deixis on Patel-Grosz and Grosz's analysis and are `PersonalPronoun`s here.

## References

* [harbour-2016]
* [terenghi-2023]
* [patel-grosz-grosz-2017]
-/

@[expose] public section

/-- A demonstrative pronoun is a `Pronoun` with its deictic content, the person feature value of
the referents in whose vicinity it locates its referent. -/
@[ext]
structure DemonstrativePronoun extends Pronoun where
  /-- The deictic content, none for a form that enters no deictic contrast. -/
  deixis : Option Person.ValuedFeature

instance : DecidableEq DemonstrativePronoun :=
  fun _ _ ↦ decidable_of_iff _ DemonstrativePronoun.ext_iff.symm
