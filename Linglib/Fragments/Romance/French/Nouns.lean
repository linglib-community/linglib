module

public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Fragments.Romance.French.Gender

/-!
# French nouns

The French noun as a lexical entry is the root `GenderedNoun` over the masculine and feminine
genders, which a numeral counts directly or not at all, with its plural; names are the root
`ProperName`. A French noun needs a determiner (`French.Determiners.inventory`) to be an argument,
so no bare nominal is one, as Chierchia observes.

## References

* [chierchia-1998]
-/

@[expose] public section

namespace French.Nouns


/-- A French noun is the root gendered entry, which a numeral counts directly or not at all,
with its plural. -/
structure Noun extends GenderedNoun Gender.Value, ClassifiedNoun Empty where
  counters := {none}
  /-- The plural. -/
  plural : Option String := none
  deriving DecidableEq

/-! ### Count nouns -/

def chien : Noun := { form := "chien", gloss := "dog", gender := .masculine, plural := "chiens" }
def chat : Noun := { form := "chat", gloss := "cat", gender := .masculine, plural := "chats" }
def livre : Noun := { form := "livre", gloss := "book", gender := .masculine, plural := "livres" }
def homme : Noun :=
  { form := "homme", gloss := "man", gender := .masculine, referentGender := some .male,
    plural := "hommes" }
def garcon : Noun :=
  { form := "garçon", gloss := "boy", gender := .masculine, referentGender := some .male,
    plural := "garçons" }
def professeur : Noun :=
  { form := "professeur", gloss := "teacher", gender := .masculine, plural := "professeurs" }
def etudiant : Noun :=
  { form := "étudiant", gloss := "student", gender := .masculine, referentGender := some .male,
    plural := "étudiants" }
def avocat : Noun :=
  { form := "avocat", gloss := "lawyer", gender := .masculine, plural := "avocats" }
def cheval : Noun :=
  { form := "cheval", gloss := "horse", gender := .masculine, plural := "chevaux" }
def fille : Noun :=
  { form := "fille", gloss := "girl", gender := .feminine, referentGender := some .female,
    plural := "filles" }
def femme : Noun :=
  { form := "femme", gloss := "woman", gender := .feminine, referentGender := some .female,
    plural := "femmes" }
def table : Noun := { form := "table", gloss := "table", gender := .feminine, plural := "tables" }
def pomme : Noun := { form := "pomme", gloss := "apple", gender := .feminine, plural := "pommes" }
def fleur : Noun := { form := "fleur", gloss := "flower", gender := .feminine, plural := "fleurs" }

/-! ### Mass nouns -/

def eau : Noun := { form := "eau", gloss := "water", gender := .feminine, counters := ∅ }
def vin : Noun := { form := "vin", gloss := "wine", gender := .masculine, counters := ∅ }
def pain : Noun := { form := "pain", gloss := "bread", gender := .masculine, counters := ∅ }
def lait : Noun := { form := "lait", gloss := "milk", gender := .masculine, counters := ∅ }

/-- The common nouns. -/
def nouns : List Noun :=
  [chien, chat, livre, homme, garcon, professeur, etudiant, avocat, cheval, fille, femme, table,
    pomme, fleur, eau, vin, pain, lait]

/-! ### Proper names -/

/-- A personal name, restricted to a gender. -/
def name (form : String) (g : ReferentGender) : ProperName :=
  { form, gloss := form, referentGender := some g }

def jean : ProperName := name "Jean" .male
def marie : ProperName := name "Marie" .female
def pierre : ProperName := name "Pierre" .male

end French.Nouns
