module

public import Linglib.Syntax.Category.Noun.Basic

/-!
# Modern Greek nouns by gender

The nouns of Adamson and Anagnostopoulou's Greek examples, each with its grammatical gender and the
gender of its referents where they have one. The gender of *andras* 'man' and *gineka* 'woman' is
natural, the gender of their referents. *Koritsi* 'girl' is neuter though its referents are female,
and *megalofiia* 'genius' and *thima* 'victim' are feminine and neuter whoever they refer to. The
inanimates are of all three genders.

## References

* [adamson-anagnostopoulou-2025]
-/

@[expose] public section

namespace Greek.StandardModern.Gender

/-- *andras* 'man'. -/
def andras : GenderedNoun _root_.Gender.Label :=
  { form := "andras", gloss := "man", gender := .masculine, naturalGender := some .masculine }

/-- *gineka* 'woman'. -/
def gineka : GenderedNoun _root_.Gender.Label :=
  { form := "gineka", gloss := "woman", gender := .feminine, naturalGender := some .feminine }

/-- *Petros*. -/
def petros : GenderedNoun _root_.Gender.Label :=
  { form := "Petros", gloss := "Petros", gender := .masculine, naturalGender := some .masculine }

/-- *Kostas*. -/
def kostas : GenderedNoun _root_.Gender.Label :=
  { form := "Kostas", gloss := "Kostas", gender := .masculine, naturalGender := some .masculine }

/-- *Giorgos*. -/
def giorgos : GenderedNoun _root_.Gender.Label :=
  { form := "Giorgos", gloss := "Giorgos", gender := .masculine,
    naturalGender := some .masculine }

/-- *Maria*. -/
def maria : GenderedNoun _root_.Gender.Label :=
  { form := "Maria", gloss := "Maria", gender := .feminine, naturalGender := some .feminine }

/-- *Giota*. -/
def giota : GenderedNoun _root_.Gender.Label :=
  { form := "Giota", gloss := "Giota", gender := .feminine, naturalGender := some .feminine }

/-- *kleftis* 'thief'. -/
def kleftis : GenderedNoun _root_.Gender.Label :=
  { form := "kleftis", gloss := "thief", gender := .masculine, naturalGender := some .masculine }

/-- *filos* 'friend'. -/
def filos : GenderedNoun _root_.Gender.Label :=
  { form := "filos", gloss := "friend", gender := .masculine, naturalGender := some .masculine }

/-- *adherfi* 'sister'. -/
def adherfi : GenderedNoun _root_.Gender.Label :=
  { form := "adherfi", gloss := "sister", gender := .feminine, naturalGender := some .feminine }

/-- *mitera* 'mother'. -/
def mitera : GenderedNoun _root_.Gender.Label :=
  { form := "mitera", gloss := "mother", gender := .feminine, naturalGender := some .feminine }

/-- *koritsi* 'girl', neuter though its referents are female. -/
def koritsi : GenderedNoun _root_.Gender.Label :=
  { form := "koritsi", gloss := "girl", gender := .neuter, naturalGender := some .feminine }

/-- *megalofiia* 'genius', feminine whoever the genius. -/
def megalofiia : GenderedNoun _root_.Gender.Label :=
  { form := "megalofiia", gloss := "genius", gender := .feminine }

/-- *thima* 'victim', neuter whoever the victim. -/
def thima : GenderedNoun _root_.Gender.Label :=
  { form := "thima", gloss := "victim", gender := .neuter }

/-- *pinakas* 'blackboard, painting'. -/
def pinakas : GenderedNoun _root_.Gender.Label :=
  { form := "pinakas", gloss := "blackboard, painting", gender := .masculine }

/-- *karekla* 'chair'. -/
def karekla : GenderedNoun _root_.Gender.Label :=
  { form := "karekla", gloss := "chair", gender := .feminine }

/-- *piruni* 'fork'. -/
def piruni : GenderedNoun _root_.Gender.Label :=
  { form := "piruni", gloss := "fork", gender := .neuter }

/-- *kutali* 'spoon'. -/
def kutali : GenderedNoun _root_.Gender.Label :=
  { form := "kutali", gloss := "spoon", gender := .neuter }

/-- *fusta* 'skirt'. -/
def fusta : GenderedNoun _root_.Gender.Label :=
  { form := "fusta", gloss := "skirt", gender := .feminine }

/-- *bluza* 'T-shirt'. -/
def bluza : GenderedNoun _root_.Gender.Label :=
  { form := "bluza", gloss := "T-shirt", gender := .feminine }

/-- *anaptiras* 'lighter'. -/
def anaptiras : GenderedNoun _root_.Gender.Label :=
  { form := "anaptiras", gloss := "lighter", gender := .masculine }

/-- *fakos* 'torch'. -/
def fakos : GenderedNoun _root_.Gender.Label :=
  { form := "fakos", gloss := "torch", gender := .masculine }

/-- *scholio* 'school'. -/
def scholio : GenderedNoun _root_.Gender.Label :=
  { form := "scholio", gloss := "school", gender := .neuter }

/-- *ekklisia* 'church'. -/
def ekklisia : GenderedNoun _root_.Gender.Label :=
  { form := "ekklisia", gloss := "church", gender := .feminine }

/-- *balkoni* 'balcony'. -/
def balkoni : GenderedNoun _root_.Gender.Label :=
  { form := "balkoni", gloss := "balcony", gender := .neuter }

/-- *dhiadhromos* 'corridor'. -/
def dhiadhromos : GenderedNoun _root_.Gender.Label :=
  { form := "dhiadhromos", gloss := "corridor", gender := .masculine }

/-- *daxtilidi* 'ring'. -/
def daxtilidi : GenderedNoun _root_.Gender.Label :=
  { form := "daxtilidi", gloss := "ring", gender := .neuter }

/-- *ombrela* 'umbrella'. -/
def ombrela : GenderedNoun _root_.Gender.Label :=
  { form := "ombrela", gloss := "umbrella", gender := .feminine }

/-- *fotografia* 'picture'. -/
def fotografia : GenderedNoun _root_.Gender.Label :=
  { form := "fotografia", gloss := "picture", gender := .feminine }

/-- *pukamiso* 'shirt'. -/
def pukamiso : GenderedNoun _root_.Gender.Label :=
  { form := "pukamiso", gloss := "shirt", gender := .neuter }

end Greek.StandardModern.Gender
