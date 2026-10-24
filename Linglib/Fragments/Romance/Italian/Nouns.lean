module

public import Linglib.Syntax.Category.Noun.Basic

/-!
# Italian nouns

The Italian noun as a lexical entry is the root `GenderedNoun` over the masculine and feminine
genders, which a numeral counts directly or not at all, with its plural; names are the root
`ProperName`. Italian nouns need a determiner (`Italian.Determiners.inventory`) to be arguments, as
Chierchia observes; the definite plural denotes a kind and the bare plural, where licensed, a
property (`Studies/Guerrini2026.lean`). The plurals in *-a* that change gender are
`Italian.NumberGender`.

## References

* [chierchia-1998]
-/

@[expose] public section

namespace Italian.Nouns


/-- An Italian noun is the root gendered entry, which a numeral counts directly or not at all,
with its plural. -/
structure Noun extends GenderedNoun Gender.Label, ClassifiedNoun Empty where
  counters := {none}
  /-- The plural. -/
  plural : Option String := none
  deriving DecidableEq

/-! ### Count nouns -/

def libro : Noun := { form := "libro", gloss := "book", gender := .masculine, plural := "libri" }
def ragazzo : Noun :=
  { form := "ragazzo", gloss := "boy", gender := .masculine, naturalGender := some .masculine,
    plural := "ragazzi" }
def uomo : Noun :=
  { form := "uomo", gloss := "man", gender := .masculine, naturalGender := some .masculine,
    plural := "uomini" }
def gatto : Noun := { form := "gatto", gloss := "cat", gender := .masculine, plural := "gatti" }
def cane : Noun := { form := "cane", gloss := "dog", gender := .masculine, plural := "cani" }
def tavolo : Noun :=
  { form := "tavolo", gloss := "table", gender := .masculine, plural := "tavoli" }
def ragazza : Noun :=
  { form := "ragazza", gloss := "girl", gender := .feminine, naturalGender := some .feminine,
    plural := "ragazze" }
def donna : Noun :=
  { form := "donna", gloss := "woman", gender := .feminine, naturalGender := some .feminine,
    plural := "donne" }
def casa : Noun := { form := "casa", gloss := "house", gender := .feminine, plural := "case" }

/-! ### Mass nouns -/

def acqua : Noun := { form := "acqua", gloss := "water", gender := .feminine, counters := ∅ }
def vino : Noun := { form := "vino", gloss := "wine", gender := .masculine, counters := ∅ }
def pane : Noun := { form := "pane", gloss := "bread", gender := .masculine, counters := ∅ }
def latte : Noun := { form := "latte", gloss := "milk", gender := .masculine, counters := ∅ }

/-! ### Proper names -/

/-- A personal name with its natural gender. -/
def name (form : String) (gender : Gender.Label) : ProperName :=
  { form, gloss := form, gender := some gender }

def paolo : ProperName := name "Paolo" .masculine
def maria : ProperName := name "Maria" .feminine

end Italian.Nouns
