module

public import Linglib.Syntax.Category.Verb.Tense

/-!
# Temporal connectives

This file defines the lexical entry of a temporal connective, a subordinator or preposition
that locates the time of its host clause relative to the time of its complement: *before*,
*after*, *as soon as*, *when*, *whenever*, *while*, *as long as*, *until* and *since*. An entry
records the relation the word lexicalizes, one for each connective Heinämäki gives an account of,
and the tense its complement takes where the word fixes one, as Japanese *mae* 'before' takes a
non-past complement under a past. Whether an *until* word is a punctual rather than a durative
*until*, Karttunen's two *until*s, is contested, since Iatridou and Zeijlstra derive both uses
from one *until*, so a study that draws the line classifies the words itself.

An entry carries no truth conditions. What *before* means is contested, from the quantificational
relations of Anscombe to the reference points of Heinämäki, the branching-time analysis of Beaver
and Condoravdi and the scalar one of Rett, so a study assigns denotations to the relations it
treats; a fragment says only which relation a word lexicalizes.

## Main declarations

* `Tense.Connective`: the lexical entry, with its `relation` and `tense`.
* `Tense.Connective.Relation`: the nine relations a connective can lexicalize.

## References

* [heinamaki-1974]
* [karttunen-1974]
* [iatridou-zeijlstra-2021]
* [anscombe-1964]
* [beaver-condoravdi-2003]
* [rett-2020a]
-/

@[expose] public section

namespace Tense

/-- The temporal relations a connective can lexicalize, the connectives of [heinamaki-1974]. -/
inductive Connective.Relation where
  /-- The host begins, or an accomplishment ends, before the complement begins. -/
  | before
  /-- Some part of the host follows the complement. -/
  | after
  /-- The host begins immediately after the complement. -/
  | asSoonAs
  /-- The host and the complement overlap or, when neither takes time, the host follows. -/
  | when_
  /-- The host holds at every time when the complement does. -/
  | whenever
  /-- The host and a complement that takes time overlap. -/
  | while_
  /-- The host holds throughout a complement that takes time. -/
  | asLongAs
  /-- The host holds up to the complement. -/
  | until_
  /-- The host holds, or has held, in the period from the complement to the present. -/
  | since
  deriving DecidableEq, Repr

/-- A temporal connective is a subordinator or preposition relating the time of its host clause to
that of its complement. -/
structure Connective where
  /-- The surface form. -/
  form : String
  /-- The relation the connective lexicalizes. -/
  relation : Connective.Relation
  /-- The grammatical tense of the complement, where the connective fixes one. -/
  tense : Option Tense := none

end Tense
