module

public import Linglib.Fragments.Romance.Spanish.Gender

/-!
# Spanish binominal nouns

Spanish binominals join a first noun to a second by *de*, and fall into three types by the class
of the first noun. A group noun heads a pseudo-partitive, *un grupo de estudiantes* 'a group of
students'; a quantity noun heads a quantificational binominal, *un montón de estudiantes* 'a lot
of students'; and an expressive noun heads a qualitative binominal, in which it evaluates the
referent of the second noun, *una mierda de departamento* 'a shit of an apartment'. Group and
quantity nouns also have a descriptive reading in which they head the phrase, as *una pila de
libros* is 'a pile of books' beside 'a lot of books'. *Bocha* and *pila* are the Rioplatense
quantity nouns. The classification is Saab's.

## Main definitions

* `Spanish.Binominals.BinominalType`: the three types.
* `Spanish.Binominals.BinominalNoun`: a noun with its gender and the type of binominal it heads.

## References

* [saab-2026]
-/

@[expose] public section

namespace Spanish.Binominals

/-- The types of binominal, by the class of the first noun. -/
inductive BinominalType where
  /-- A group noun and the set it groups. -/
  | pseudoPartitive
  /-- A quantity noun and what it quantifies. -/
  | quantificational
  /-- An expressive noun and what it evaluates. -/
  | qualitative
  deriving DecidableEq, Repr

/-- A noun with its gender and the type of binominal it heads. -/
structure BinominalNoun extends GenderedNoun Spanish.Gender.Value where
  /-- The type of binominal the noun heads. -/
  binominalType : BinominalType

/-- *grupo* 'group'. -/
def grupo : BinominalNoun :=
  { form := "grupo", gloss := "group", gender := .masc, binominalType := .pseudoPartitive }

/-- *parte* 'part'. -/
def parte : BinominalNoun :=
  { form := "parte", gloss := "part", gender := .fem, binominalType := .pseudoPartitive }

/-- *mayoría* 'most'. -/
def mayoría : BinominalNoun :=
  { form := "mayoría", gloss := "most", gender := .fem, binominalType := .pseudoPartitive }

/-- *montón* 'lot'. -/
def montón : BinominalNoun :=
  { form := "montón", gloss := "lot", gender := .masc, binominalType := .quantificational }

/-- *pila* 'pile', Rioplatense. -/
def pila : BinominalNoun :=
  { form := "pila", gloss := "pile", gender := .fem, binominalType := .quantificational }

/-- *bocha* 'ball', Rioplatense. -/
def bocha : BinominalNoun :=
  { form := "bocha", gloss := "ball", gender := .fem, binominalType := .quantificational }

/-- *mierda* 'shit'. -/
def mierda : BinominalNoun :=
  { form := "mierda", gloss := "shit", gender := .fem, binominalType := .qualitative }

/-- The binominal nouns. -/
def allNouns : List BinominalNoun := [grupo, parte, mayoría, montón, pila, bocha, mierda]

/-- The entry with a given form. -/
def lookup (form : String) : Option BinominalNoun := allNouns.find? (·.form == form)

end Spanish.Binominals
