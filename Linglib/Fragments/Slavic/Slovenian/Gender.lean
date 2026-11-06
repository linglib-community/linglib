module

public import Linglib.Syntax.Category.Noun.Basic

/-!
# Slovene noun gender

Slovene has three genders, masculine, feminine and neuter, distinguished in the singular, the
dual and the plural of agreeing predicates. This file gives the genders and the nouns of
Corbett's examples of resolved agreement after Lenček: the names *Tonček*, *Igor*, *Marina*,
*Marta* and *Marjanca*, *brat* 'brother', *dekletce* 'little girl', a neuter denoting a female,
and the inanimates *streha* 'roof', *gnezdo* 'nest', *drevo* 'tree' and *okno* 'window'.

## References

* [corbett-1991]
-/

@[expose] public section

namespace Slovenian.Gender

/-- The three genders. -/
inductive Value where
  | masculine
  | feminine
  | neuter
  deriving DecidableEq, Repr, Fintype

/-- Male humans are masculine and female humans feminine. -/
def Value.ofReferentGender : ReferentGender → Value
  | .male => .masculine
  | .female => .feminine

/-- *Tonček*, a man's name. -/
def toncek : GenderedNoun Value :=
  { form := "Tonček", gloss := "Tonček", gender := .masculine, referentGender := some .male }

/-- *Igor*, a man's name. -/
def igor : GenderedNoun Value :=
  { form := "Igor", gloss := "Igor", gender := .masculine, referentGender := some .male }

/-- *Marina*, a woman's name. -/
def marina : GenderedNoun Value :=
  { form := "Marina", gloss := "Marina", gender := .feminine, referentGender := some .female }

/-- *Marta*, a woman's name. -/
def marta : GenderedNoun Value :=
  { form := "Marta", gloss := "Marta", gender := .feminine, referentGender := some .female }

/-- *Marjanca*, a woman's name. -/
def marjanca : GenderedNoun Value :=
  { form := "Marjanca", gloss := "Marjanca", gender := .feminine,
    referentGender := some .female }

/-- *brat* 'brother'. -/
def brat : GenderedNoun Value :=
  { form := "brat", gloss := "brother", gender := .masculine, referentGender := some .male }

/-- *dekletce* 'little girl', a neuter denoting a female. -/
def dekletce : GenderedNoun Value :=
  { form := "dekletce", gloss := "little girl", gender := .neuter,
    referentGender := some .female }

/-- *streha* 'roof'. -/
def streha : GenderedNoun Value := { form := "streha", gloss := "roof", gender := .feminine }

/-- *gnezdo* 'nest'. -/
def gnezdo : GenderedNoun Value := { form := "gnezdo", gloss := "nest", gender := .neuter }

/-- *drevo* 'tree'. -/
def drevo : GenderedNoun Value := { form := "drevo", gloss := "tree", gender := .neuter }

/-- *okno* 'window'. -/
def okno : GenderedNoun Value := { form := "okno", gloss := "window", gender := .neuter }

/-- The nouns of the file. -/
def allNouns : List (GenderedNoun Value) :=
  [toncek, igor, marina, marta, marjanca, brat, dekletce, streha, gnezdo, drevo, okno]

end Slovenian.Gender
