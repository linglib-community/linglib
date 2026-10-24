module

public import Linglib.Syntax.Category.Noun.Basic

/-!
# Modern Greek nouns by gender

The nouns of Adamson and Anagnostopoulou's Greek examples, each with its grammatical gender and the
sex it restricts its referents to where it does. The gender of *andras* 'man' and *gineka* 'woman'
is natural, the one their referents' sex is assigned. *Koritsi* 'girl' is neuter though its
referents are female,
and *megalofiia* 'genius' and *thima* 'victim' are feminine and neuter whoever they refer to. The
inanimates are of all three genders.

## References

* [adamson-anagnostopoulou-2025]
-/

@[expose] public section

namespace Greek.StandardModern.Gender

/-- The three genders. -/
inductive Value where
  | masculine
  | feminine
  | neuter
  deriving DecidableEq, Repr, Fintype

/-- Male humans are masculine and female humans feminine. -/
def Value.ofSex : Sex → Value
  | .male => .masculine
  | .female => .feminine

/-- *andras* 'man'. -/
def andras : GenderedNoun Value :=
  { form := "andras", gloss := "man", gender := .masculine, sex := some .male }

/-- *gineka* 'woman'. -/
def gineka : GenderedNoun Value :=
  { form := "gineka", gloss := "woman", gender := .feminine, sex := some .female }

/-- *Petros*. -/
def petros : GenderedNoun Value :=
  { form := "Petros", gloss := "Petros", gender := .masculine, sex := some .male }

/-- *Kostas*. -/
def kostas : GenderedNoun Value :=
  { form := "Kostas", gloss := "Kostas", gender := .masculine, sex := some .male }

/-- *Giorgos*. -/
def giorgos : GenderedNoun Value :=
  { form := "Giorgos", gloss := "Giorgos", gender := .masculine,
    sex := some .male }

/-- *Maria*. -/
def maria : GenderedNoun Value :=
  { form := "Maria", gloss := "Maria", gender := .feminine, sex := some .female }

/-- *Giota*. -/
def giota : GenderedNoun Value :=
  { form := "Giota", gloss := "Giota", gender := .feminine, sex := some .female }

/-- *kleftis* 'thief'. -/
def kleftis : GenderedNoun Value :=
  { form := "kleftis", gloss := "thief", gender := .masculine, sex := some .male }

/-- *filos* 'friend'. -/
def filos : GenderedNoun Value :=
  { form := "filos", gloss := "friend", gender := .masculine, sex := some .male }

/-- *adherfi* 'sister'. -/
def adherfi : GenderedNoun Value :=
  { form := "adherfi", gloss := "sister", gender := .feminine, sex := some .female }

/-- *mitera* 'mother'. -/
def mitera : GenderedNoun Value :=
  { form := "mitera", gloss := "mother", gender := .feminine, sex := some .female }

/-- *koritsi* 'girl', neuter though its referents are female. -/
def koritsi : GenderedNoun Value :=
  { form := "koritsi", gloss := "girl", gender := .neuter, sex := some .female }

/-- *megalofiia* 'genius', feminine whoever the genius. -/
def megalofiia : GenderedNoun Value :=
  { form := "megalofiia", gloss := "genius", gender := .feminine }

/-- *thima* 'victim', neuter whoever the victim. -/
def thima : GenderedNoun Value := { form := "thima", gloss := "victim", gender := .neuter }

/-- *pinakas* 'blackboard, painting'. -/
def pinakas : GenderedNoun Value :=
  { form := "pinakas", gloss := "blackboard, painting", gender := .masculine }

/-- *karekla* 'chair'. -/
def karekla : GenderedNoun Value :=
  { form := "karekla", gloss := "chair", gender := .feminine }

/-- *piruni* 'fork'. -/
def piruni : GenderedNoun Value := { form := "piruni", gloss := "fork", gender := .neuter }

/-- *kutali* 'spoon'. -/
def kutali : GenderedNoun Value := { form := "kutali", gloss := "spoon", gender := .neuter }

/-- *fusta* 'skirt'. -/
def fusta : GenderedNoun Value := { form := "fusta", gloss := "skirt", gender := .feminine }

/-- *bluza* 'T-shirt'. -/
def bluza : GenderedNoun Value :=
  { form := "bluza", gloss := "T-shirt", gender := .feminine }

/-- *anaptiras* 'lighter'. -/
def anaptiras : GenderedNoun Value :=
  { form := "anaptiras", gloss := "lighter", gender := .masculine }

/-- *fakos* 'torch'. -/
def fakos : GenderedNoun Value :=
  { form := "fakos", gloss := "torch", gender := .masculine }

/-- *scholio* 'school'. -/
def scholio : GenderedNoun Value :=
  { form := "scholio", gloss := "school", gender := .neuter }

/-- *ekklisia* 'church'. -/
def ekklisia : GenderedNoun Value :=
  { form := "ekklisia", gloss := "church", gender := .feminine }

/-- *balkoni* 'balcony'. -/
def balkoni : GenderedNoun Value :=
  { form := "balkoni", gloss := "balcony", gender := .neuter }

/-- *dhiadhromos* 'corridor'. -/
def dhiadhromos : GenderedNoun Value :=
  { form := "dhiadhromos", gloss := "corridor", gender := .masculine }

/-- *daxtilidi* 'ring'. -/
def daxtilidi : GenderedNoun Value :=
  { form := "daxtilidi", gloss := "ring", gender := .neuter }

/-- *ombrela* 'umbrella'. -/
def ombrela : GenderedNoun Value :=
  { form := "ombrela", gloss := "umbrella", gender := .feminine }

/-- *fotografia* 'picture'. -/
def fotografia : GenderedNoun Value :=
  { form := "fotografia", gloss := "picture", gender := .feminine }

/-- *pukamiso* 'shirt'. -/
def pukamiso : GenderedNoun Value :=
  { form := "pukamiso", gloss := "shirt", gender := .neuter }

end Greek.StandardModern.Gender
