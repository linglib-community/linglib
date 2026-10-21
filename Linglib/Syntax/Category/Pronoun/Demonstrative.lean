module

public import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Demonstrative pronouns

A demonstrative pronoun is a pronoun with deictic content: the participant sets of the referents in
whose vicinity it locates its referent. Harbour finds that the deixis of objects and spaces attests
the five partitions of person and, as far as he has found, no others, so the content is a cell of
one of them, as a person value's `Person.participantSets` is. English *this* covers the sets
containing the speaker and *that* the others. Catalan *aquest* covers every set with a participant
and *aquell* the empty one. Latin *hic*, *iste*, *ille* separate the speaker's, the addressee's and
the others' spaces, and French *ce*, which makes no deictic contrast, covers every set. What makes a
form a demonstrative is this content and not its traditional label: Patel-Grosz and Grosz argue that
German *der*, *die*, *das*, traditionally called demonstrative pronouns, are personal pronouns built
on the strong article that encode no deixis, so they are `PersonalPronoun`s here
(`Studies/PatelGroszGrosz2017.lean`), whereas Harbour treats stressed *der* as a demonstrative
without a deictic contrast.

## Main definitions

* `DemonstrativePronoun`: a pronoun with its deictic content.
* `DemonstrativePronoun.toWord`: its token, of UD pronoun type `Dem`.

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
  deixis : Finset (Finset Discourse.Role)

instance : DecidableEq DemonstrativePronoun :=
  fun _ _ ↦ decidable_of_iff _ DemonstrativePronoun.ext_iff.symm

/-- A demonstrative's token is of UD pronoun type `Dem`. -/
def DemonstrativePronoun.toWord (d : DemonstrativePronoun) : Morphology.Word :=
  d.toPronoun.toWord (some .Dem)
