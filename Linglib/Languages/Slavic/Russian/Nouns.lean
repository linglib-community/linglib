module

public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Languages.Slavic.Russian.Gender

/-!
# Russian nouns

The Russian common noun as a lexical entry is the root `GenderedNoun` over the three genders with
the ways a numeral counts it. A numeral counts a count noun directly, *tri batona* 'three
loaves', and counts a mass noun only through a measure noun, *tri batona xleba* 'three loaves of
bread', so a mass noun has no counter. Russian has no classifiers and no articles
(`Russian.Determiners.inventory`).

## References

* [chierchia-1998]
-/

@[expose] public section

namespace Russian.Nouns

/-- A Russian common noun is the root gendered entry, which a numeral counts directly or not at
all. -/
structure Noun extends GenderedNoun Gender.Value, ClassifiedNoun Empty where
  counters := {none}
  deriving DecidableEq

/-! ### Count nouns -/

/-- *mal'čik* 'boy'. -/
def mal'čik : Noun :=
  { form := "mal'čik", gloss := "boy", gender := .masc, referentGender := some .male }

/-- *devočka* 'girl'. -/
def devočka : Noun :=
  { form := "devočka", gloss := "girl", gender := .fem, referentGender := some .female }

/-- *sobaka* 'dog'. -/
def sobaka : Noun := { form := "sobaka", gloss := "dog", gender := .fem }

/-- *dinozavr* 'dinosaur'. -/
def dinozavr : Noun := { form := "dinozavr", gloss := "dinosaur", gender := .masc }

/-- *baton* 'loaf'. -/
def baton : Noun := { form := "baton", gloss := "loaf", gender := .masc }

/-! ### Mass nouns -/

/-- *xleb* 'bread'. -/
def xleb : Noun := { form := "xleb", gloss := "bread", gender := .masc, counters := ∅ }

/-- *syr* 'cheese'. -/
def syr : Noun := { form := "syr", gloss := "cheese", gender := .masc, counters := ∅ }

/-- The common nouns. -/
def nouns : List Noun := [mal'čik, devočka, sobaka, dinozavr, baton, xleb, syr]

end Russian.Nouns
