module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Tamil noun gender

Tamil assigns nouns to three genders by their meaning alone: the masculine for gods and male
humans, the feminine for goddesses and female humans, and the neuter for the rest, so that the
masculine and the feminine together are the rational gender of the traditional grammars and
the neuter the non-rational. Corbett gives the system as his first strict semantic assignment
system, with the sun and the moon masculine as names of gods. The genders show on the finite
verb: in the singular three forms, the masculine *-aan*, the feminine *-aaL* and the neuter
*-atu*, and in the plural two, the rational *-aanka* for masculines and feminines alike and the
neuter *-atunka*, which many speakers replace by the singular *-atu*. Corbett's data are from
Asher's grammar of colloquial Tamil; the nouns are those of his assignment table and of the
coordinations his resolution rules cover, the matter of `Studies/Corbett1991.lean`.

## Main definitions

* `Tamil.Gender.Value`: the three genders.
* `Tamil.Gender.Noun`, `Tamil.Gender.allNouns`: a noun with its gender and rationality, and the
  entries.
* `Tamil.Gender.SgConcord`, `Tamil.Gender.PlConcord`: the verb's singular and plural agreement
  forms.

## References

* [corbett-1991]
-/

@[expose] public section

namespace Tamil.Gender

/-! ### Genders -/

/-- The three controller genders. -/
inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-! ### Nouns -/

/-- A Tamil noun with the agreement it takes and the two semantic facts the gender tracks,
whether the referent is rational, a human or a deity, and the gender it restricts its referents
to where it does. -/
structure Noun extends GenderedNoun Value where
  /-- Whether the referent is rational, a human or a deity. -/
  rational : Bool
  deriving DecidableEq, Repr

/-- *aaN* 'man', masculine. -/
def aaN : Noun :=
  { form := "aaN", gloss := "man", gender := .masc, referentGender := some .male,
    rational := true }

/-- *CivaN* 'Shiva', masculine. -/
def civaN : Noun :=
  { form := "CivaN", gloss := "Shiva", gender := .masc, referentGender := some .male,
    rational := true }

/-- *peN* 'woman', feminine. -/
def peN : Noun :=
  { form := "peN", gloss := "woman", gender := .fem, referentGender := some .female,
    rational := true }

/-- *kaali* 'Kali', feminine. -/
def kaali : Noun :=
  { form := "kaali", gloss := "Kali", gender := .fem, referentGender := some .female,
    rational := true }

/-- *maram* 'tree', neuter. -/
def maram : Noun := { form := "maram", gloss := "tree", gender := .neut, rational := false }

/-- *viiTu* 'house', neuter. -/
def viiTu : Noun := { form := "viiTu", gloss := "house", gender := .neut, rational := false }

/-- *cuuriyan* 'sun', masculine as the name of a god. -/
def cuuriyan : Noun :=
  { form := "cuuriyan", gloss := "sun", gender := .masc, referentGender := some .male,
    rational := true }

/-- *cantiran* 'moon', masculine as the name of a god. -/
def cantiran : Noun :=
  { form := "cantiran", gloss := "moon", gender := .masc, referentGender := some .male,
    rational := true }

/-- *raaman* 'Raman', masculine. -/
def raaman : Noun :=
  { form := "raaman", gloss := "Raman", gender := .masc, referentGender := some .male,
    rational := true }

/-- *murukan* 'Murugan', masculine. -/
def murukan : Noun :=
  { form := "murukan", gloss := "Murugan", gender := .masc, referentGender := some .male,
    rational := true }

/-- *akkaa* 'elder sister', feminine. -/
def akkaa : Noun :=
  { form := "akkaa", gloss := "elder sister", gender := .fem, referentGender := some .female,
    rational := true }

/-- *tankacci* 'younger sister', feminine. -/
def tankacci : Noun :=
  { form := "tankacci", gloss := "younger sister", gender := .fem,
    referentGender := some .female, rational := true }

/-- *annan* 'elder brother', masculine. -/
def annan : Noun :=
  { form := "annan", gloss := "elder brother", gender := .masc, referentGender := some .male,
    rational := true }

/-- *naay* 'dog', neuter. -/
def naay : Noun := { form := "naay", gloss := "dog", gender := .neut, rational := false }

/-- *puune* 'cat', neuter. -/
def puune : Noun := { form := "puune", gloss := "cat", gender := .neut, rational := false }

/-- The nouns of Corbett's assignment table, his masculine heavenly bodies, and his
coordinations. -/
def allNouns : List Noun :=
  [aaN, civaN, peN, kaali, maram, viiTu, cuuriyan, cantiran, raaman, murukan, akkaa, tankacci,
    annan, naay, puune]

/-! ### Verb agreement -/

/-- The third person singular agreement of the verb, *-aan* masculine, *-aaL* feminine and
*-atu* neuter. -/
inductive SgConcord where
  | aan
  | aaL
  | atu
  deriving DecidableEq, Repr, Fintype

/-- The third person plural agreement of the verb, the rational *-aanka* and the neuter
*-atunka*. -/
inductive PlConcord where
  | rational
  | neuter
  deriving DecidableEq, Repr, Fintype

/-- The singular agreement form of each gender. -/
def Value.sgConcord : Value → SgConcord
  | .masc => .aan
  | .fem => .aaL
  | .neut => .atu

/-- The plural agreement form of each gender, one for the two rational genders. -/
def Value.plConcord : Value → PlConcord
  | .masc | .fem => .rational
  | .neut => .neuter

end Tamil.Gender
