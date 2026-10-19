module

public import Linglib.Semantics.Mood.Defs
public import Linglib.Syntax.Category.Verb.Tense

/-!
# Temporal connectives

This file defines the lexical entry of a temporal connective, a subordinator or preposition
that locates the time of its host clause relative to the time of its complement: *before*,
*after*, *when*, *while*, *until*, *since*, *by* and *whenever*. An entry records the relation
the word lexicalizes, drawn from Heinämäki's inventory, and the grammatical mood and tense its
complement takes where the language or the word fixes one, as Japanese *mae* 'before' takes a
non-past complement under a past. Whether an *until* word is a punctual rather than a durative
*until*, Karttunen's two *until*s, is contested, since Iatridou and Zeijlstra derive both uses
from one *until*, so a study that draws the line classifies the words itself.

An entry carries no truth conditions. What *before* means is contested, from the quantificational
relations of Anscombe and Heinämäki to the branching-time analysis of Beaver and Condoravdi and
the scalar one of Rett, so a study assigns denotations to the relations it treats and derives
veridicality and polarity licensing from them; a fragment says only which relation a word
lexicalizes.

## Main declarations

* `Tense.Connective`: the lexical entry, with its `relation`, `mood` and `tense`.
* `Tense.Connective.Relation`: the eight relations a connective can lexicalize.

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

/-- The temporal relations a connective can lexicalize, [heinamaki-1974]'s inventory, are that the
host precedes or follows the complement, the two coincide or the host lies within the complement,
the host persists to or from the complement time, the host is done by it, or the host recurs with
the complement. -/
inductive Connective.Relation where
  | before
  | after
  | when_
  | while_
  | until_
  | since
  | by_
  | whenever
  deriving DecidableEq, Repr

/-- A temporal connective is a subordinator or preposition relating the time of its host clause to
that of its complement. -/
structure Connective where
  /-- The surface form. -/
  form : String
  /-- The relation the connective lexicalizes. -/
  relation : Connective.Relation
  /-- The grammatical mood of the complement, where the language marks one. -/
  mood : Option Mood.Grammatical := none
  /-- The grammatical tense of the complement, where the connective fixes one. -/
  tense : Option Tense := none

end Tense
