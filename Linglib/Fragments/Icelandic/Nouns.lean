/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Word.Tree
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Icelandic nouns

Icelandic has three genders, the masculine, the feminine and the neuter, and the gender of a noun is
only indirectly related to the sex of its referents: most nouns for women are feminine, but *skáld*
'poet' is neuter whoever the poet, as Thráinsson's overview of the nominal inflection notes. The
gendered nouns are those of Adamson and Anagnostopoulou's Icelandic examples and of the
coordinations Corbett resolves, each with its grammatical gender and the gender of its referents
where they have one.

The deverbal nouns are each segmented into their morphs: an optional prefixed preposition,
the root, an optional overt verbalizer, and a nominalizing suffix. The nominalizers are many
(*-un*, *-ing*, *-sla*, *-stur*, *-n*, *-ð*, and others); the verbalizers *-k* (the *-ka* of
*seinka* 'delay') and *-er* (the *-era* of loanword verbs) appear before the nominalizer, while
the final *-a* of the verb is absent from the noun. Some prepositions that a verb takes as a
separate word are prefixed to its noun: *gera við* 'repair', *við-ger-ð*.

## Main definitions

* `Icelandic.Nouns.Deverbal`: a deverbal noun, segmented.
* `Icelandic.Nouns.Deverbal.tree`, `Icelandic.Nouns.Deverbal.morphs`: its word-formation tree and
  its morphs in linear order.
* `Icelandic.Nouns.deverbals`: the entries.

## Implementation notes

Morphs are given in their surface forms, as segmented by Wood: the roots of *söfn-un*,
*vönt-un*, *við-vör-un* and *um-önn-un* show the regular u-umlaut of *safna*, *vanta*, *vara*
and *annast*.

## References

* [adamson-anagnostopoulou-2025]
* [corbett-1991]
* [thrainsson-2007]
* [wood-2023]
-/

@[expose] public section

namespace Icelandic.Nouns

open Morphology (Morph)

/-! ### Gendered nouns -/

/-- *maður* 'man', masculine. -/
def madur : GenderedNoun _root_.Gender.Label :=
  { form := "maður", gloss := "man", gender := .masculine, naturalGender := some .masculine }

/-- *kona* 'woman', feminine. -/
def kona : GenderedNoun _root_.Gender.Label :=
  { form := "kona", gloss := "woman", gender := .feminine, naturalGender := some .feminine }

/-- *Jón*, a man's name, masculine. -/
def jon : GenderedNoun _root_.Gender.Label :=
  { form := "Jón", gloss := "Jón", gender := .masculine, naturalGender := some .masculine }

/-- *skáld* 'poet', neuter whatever the sex of the poet. -/
def skald : GenderedNoun _root_.Gender.Label :=
  { form := "skáld", gloss := "poet", gender := .neuter }

/-- *frægð* 'fame', feminine. -/
def fraegd : GenderedNoun _root_.Gender.Label :=
  { form := "frægð", gloss := "fame", gender := .feminine }

/-- *frami* 'success', masculine. -/
def frami : GenderedNoun _root_.Gender.Label :=
  { form := "frami", gloss := "success", gender := .masculine }

/-- *skeið* 'spoon', feminine. -/
def skeid : GenderedNoun _root_.Gender.Label :=
  { form := "skeið", gloss := "spoon", gender := .feminine }

/-- *stóll* 'chair', masculine. -/
def stoll : GenderedNoun _root_.Gender.Label :=
  { form := "stóll", gloss := "chair", gender := .masculine }

/-- *epli* 'apple', neuter. -/
def epli : GenderedNoun _root_.Gender.Label :=
  { form := "epli", gloss := "apple", gender := .neuter }

/-- *drengur* 'boy', masculine. -/
def drengur : GenderedNoun _root_.Gender.Label :=
  { form := "drengur", gloss := "boy", gender := .masculine, naturalGender := some .masculine }

/-- *telpa* 'girl', feminine. -/
def telpa : GenderedNoun _root_.Gender.Label :=
  { form := "telpa", gloss := "girl", gender := .feminine, naturalGender := some .feminine }

/-- *ær* 'ewe', feminine, the *á* of [corbett-1991]'s ch. 9 (57) its accusative. -/
def aer : GenderedNoun _root_.Gender.Label :=
  { form := "ær", gloss := "ewe", gender := .feminine, naturalGender := some .feminine }

/-- *lamb* 'lamb', neuter. -/
def lamb : GenderedNoun _root_.Gender.Label :=
  { form := "lamb", gloss := "lamb", gender := .neuter }

/-! ### Deverbal nouns -/

/-- A deverbal noun, segmented. -/
structure Deverbal where
  /-- A preposition prefixed to the noun. -/
  preposition : Option String := none
  /-- The root. -/
  root : String
  /-- An overt verbalizer between the root and the nominalizer. -/
  verbalizer : Option String := none
  /-- The nominalizing suffix. -/
  nominalizer : String
  deriving DecidableEq, Repr

/-- The word-formation tree of a nominal: the verbalizer and the nominalizer suffixed to the
root, and the preposition prefixed to the noun. -/
def Deverbal.tree (w : Deverbal) : Morphology.Word.Tree Morph :=
  .attachMorphs (.root w.root)
    ((w.verbalizer.map .suff).toList ++ .suff w.nominalizer :: (w.preposition.map .pref).toList)

/-- The morphs of a nominal in linear order. -/
def Deverbal.morphs (w : Deverbal) : List Morph := w.tree.toList

/-- *opn-un* 'opening', from *opna* 'open' ([wood-2023], (2.94)). -/
def opnun : Deverbal := { root := "opn", nominalizer := "un" }

/-- *söfn-un* 'collection', from *safna* 'collect' ([wood-2023], (2.28)). -/
def sofnun : Deverbal := { root := "söfn", nominalizer := "un" }

/-- *vönt-un* 'need', from *vanta* 'need' ([wood-2023], (3.39)). -/
def vontun : Deverbal := { root := "vönt", nominalizer := "un" }

/-- *misheyr-n* 'mishearing', from *misheyrast* 'mishear' ([wood-2023], (3.41)). -/
def misheyrn : Deverbal := { root := "misheyr", nominalizer := "n" }

/-- *sein-k-un* 'delay', from *seinka* 'delay' ([wood-2023], (2.3)). -/
def seinkun : Deverbal := { root := "sein", verbalizer := some "k", nominalizer := "un" }

/-- *not-k-un* 'use', from *nota* 'use', which has no verbalizer ([wood-2023], (5.37)). -/
def notkun : Deverbal := { root := "not", verbalizer := some "k", nominalizer := "un" }

/-- *analýs-er-ing* 'analysis', from *analýsera* 'analyze' ([wood-2023], (2.7)). -/
def analysering : Deverbal := { root := "analýs", verbalizer := some "er", nominalizer := "ing" }

/-- *prent-un* 'printing', from *prenta* 'print' ([wood-2023], (6.48)). -/
def prentun : Deverbal := { root := "prent", nominalizer := "un" }

/-- *þvo-ttur* 'washing, laundry', from *þvo* 'wash' ([wood-2023], (6.26), (6.27)). -/
def pvottur : Deverbal := { root := "þvo", nominalizer := "ttur" }

/-- *við-vör-un* 'warning', from *vara við* 'warn' ([wood-2023], (4.12a)). -/
def vidvorun : Deverbal := { preposition := some "við", root := "vör", nominalizer := "un" }

/-- *að-dá-un* 'admiration', from *dást að* 'admire', whose preposition cannot be prefixed to
the verb ([wood-2023], (4.48)). -/
def addaun : Deverbal := { preposition := some "að", root := "dá", nominalizer := "un" }

/-- *við-ger-ð* 'repair', from *gera við* 'repair' ([wood-2023], (4.42)). -/
def vidgerd : Deverbal := { preposition := some "við", root := "ger", nominalizer := "ð" }

/-- *um-önn-un* 'care', from *annast um* 'take care of' ([wood-2023], (4.49)). -/
def umonnun : Deverbal := { preposition := some "um", root := "önn", nominalizer := "un" }

/-- The deverbal nouns of the fragment. -/
def deverbals : List Deverbal :=
  [opnun, sofnun, vontun, misheyrn, seinkun, notkun, analysering, prentun, pvottur, vidvorun,
    addaun, vidgerd, umonnun]

end Icelandic.Nouns
