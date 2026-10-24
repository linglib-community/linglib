module

public import Linglib.Fragments.Dutch.Determiners
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Dutch nouns

This file records the Dutch noun as a lexical entry. An entry is the root `GenderedNoun` over
the two genders of `Dutch.Gender`, which a numeral counts directly or not at all, with its plural
and diminutive where the entry records them; names are the root `ProperName`. The definite article
a noun takes, `Noun.definiteArticle`, is read off its gender through
`Dutch.Determiners.singular`. Bare plurals and bare mass nouns are arguments and bare singular
count nouns are not. The entries are the nouns of Le Bruyn and de Swart's scrambling data and
the nouns with which Broekhuis and Corver's grammar shows the attributive ending of the
adjective.

## References

* [H. Broekhuis and N. Corver, *Syntax of Dutch, Volume V: Nouns and Noun Phrases 2: Prenominal
  Elements, Pronouns and Syntactic Uses of Noun Phrases* (2026)][broekhuis-corver-2026b]
* [H. Broekhuis and N. Corver, *Syntax of Dutch, Volume VI: Adjectives and Adjective Phrases*
  (2026)][broekhuis-corver-2026d]
* [B. Le Bruyn and H. de Swart, *Exceptional wide scope of bare nominals*
  (2022)][le-bruyn-de-swart-2022]
-/

@[expose] public section

namespace Dutch.Nouns

/-- A Dutch noun is the root gendered entry, which a numeral counts directly or not at all, with
its plural and diminutive where recorded. -/
structure Noun extends GenderedNoun Gender.Value, ClassifiedNoun Empty where
  counters := {none}
  /-- The plural. -/
  plural : Option String := none
  /-- The diminutive. -/
  diminutive : Option String := none
  deriving DecidableEq

/-- A noun takes the definite article *het* in the singular when it is neuter and *de* when it
is of common gender. -/
def Noun.definiteArticle (n : Noun) : String := Determiners.singular n.gender .definite

/-! ### Count nouns -/

/-- *boek* 'book', neuter. -/
def boek : Noun :=
  { form := "boek", gloss := "book", gender := .neuter, plural := "boeken", diminutive := "boekje" }

/-- *mens* 'human', of common gender, for a human of either sex. -/
def mens : Noun := { form := "mens", gloss := "human", gender := .common, plural := "mensen" }

/-- *geest* 'ghost', of common gender. -/
def geest : Noun := { form := "geest", gloss := "ghost", gender := .common, plural := "geesten" }

/-- *student* 'student', of common gender, for a student of either sex. -/
def student : Noun :=
  { form := "student", gloss := "student", gender := .common, plural := "studenten" }

/-- *hond* 'dog', of common gender. -/
def hond : Noun :=
  { form := "hond", gloss := "dog", gender := .common, plural := "honden", diminutive := "hondje" }

/-- *kat* 'cat', of common gender. -/
def kat : Noun :=
  { form := "kat", gloss := "cat", gender := .common, plural := "katten", diminutive := "katje" }

/-- *film* 'film', of common gender. -/
def film : Noun :=
  { form := "film", gloss := "film", gender := .common, plural := "films", diminutive := "filmpje" }

/-- *stoel* 'chair', of common gender, *de oude stoel* 'the old chair'. -/
def stoel : Noun := { form := "stoel", gloss := "chair", gender := .common, plural := "stoelen" }

/-- *paard* 'horse', neuter, *het oude paard* 'the old horse'. -/
def paard : Noun := { form := "paard", gloss := "horse", gender := .neuter, plural := "paarden" }

/-- *jas* 'coat', of common gender, *een oranje jas* 'an orange coat'. -/
def jas : Noun := { form := "jas", gloss := "coat", gender := .common, plural := "jassen" }

/-- *ring* 'ring', of common gender, *de gouden ring* 'the golden ring'. -/
def ring : Noun := { form := "ring", gloss := "ring", gender := .common, plural := "ringen" }

/-! ### Mass nouns -/

/-- *water* 'water', neuter. -/
def water : Noun := { form := "water", gloss := "water", gender := .neuter, counters := ∅ }

/-- *goud* 'gold', neuter. -/
def goud : Noun := { form := "goud", gloss := "gold", gender := .neuter, counters := ∅ }

/-- *meel* 'flour', neuter. -/
def meel : Noun := { form := "meel", gloss := "flour", gender := .neuter, counters := ∅ }

/-- *rijst* 'rice', of common gender, *de lekkere rijst* 'the tasty rice'. -/
def rijst : Noun := { form := "rijst", gloss := "rice", gender := .common, counters := ∅ }

/-- *bier* 'beer', neuter, *het lekkere bier* 'the tasty beer' but *lekker bier*. -/
def bier : Noun := { form := "bier", gloss := "beer", gender := .neuter, counters := ∅ }

/-! ### Proper names -/

/-- A personal name, restricted to a sex. -/
def name (form : String) (sex : Sex) : ProperName := { form, gloss := form, sex := some sex }

/-- *Helen*. -/
def helen : ProperName := name "Helen" .female

/-- *Jan*. -/
def jan : ProperName := name "Jan" .male

/-- *Piet*. -/
def piet : ProperName := name "Piet" .male

/-- *Marie*. -/
def marie : ProperName := name "Marie" .female

end Dutch.Nouns
