module

public import Linglib.Syntax.Category.Noun.Basic

/-!
# Bosnian/Croatian/Serbian nouns by gender

This file gives the nouns of Adamson and Anagnostopoulou's Bosnian/Croatian/Serbian examples, each
with its grammatical gender and the gender of its referents where they have one: the conjuncts of
their examples of resolved agreement, *muškarac i žena* 'the man and the woman', *znanje i
intuicija* 'knowledge and intuition' and *selo i brdo* 'village and hill' ((68)–(70)), and the nouns
of their Table 1, *žena*, *čovek*, *mleko*, *knjiga* and *pesak*. Their analysis of the neuter as a
mass gender is in `Studies/AdamsonAnagnostopoulou2025.lean`.

## References

* [adamson-anagnostopoulou-2025]
-/

@[expose] public section

namespace Serbian.Gender

/-- *muškarac* 'man'. -/
def muskarac : GenderedNoun _root_.Gender.Label :=
  { form := "muškarac", gloss := "man", gender := .masculine, naturalGender := some .masculine }

/-- *žena* 'woman'. -/
def zena : GenderedNoun _root_.Gender.Label :=
  { form := "žena", gloss := "woman", gender := .feminine, naturalGender := some .feminine }

/-- *čovek* 'person, man'. -/
def covek : GenderedNoun _root_.Gender.Label :=
  { form := "čovek", gloss := "person, man", gender := .masculine,
    naturalGender := some .masculine }

/-- *znanje* 'knowledge'. -/
def znanje : GenderedNoun _root_.Gender.Label :=
  { form := "znanje", gloss := "knowledge", gender := .neuter }

/-- *intuicija* 'intuition'. -/
def intuicija : GenderedNoun _root_.Gender.Label :=
  { form := "intuicija", gloss := "intuition", gender := .feminine }

/-- *selo* 'village'. -/
def selo : GenderedNoun _root_.Gender.Label :=
  { form := "selo", gloss := "village", gender := .neuter }

/-- *brdo* 'hill'. -/
def brdo : GenderedNoun _root_.Gender.Label :=
  { form := "brdo", gloss := "hill", gender := .neuter }

/-- *knjiga* 'book'. -/
def knjiga : GenderedNoun _root_.Gender.Label :=
  { form := "knjiga", gloss := "book", gender := .feminine }

/-- *pesak* 'sand'. -/
def pesak : GenderedNoun _root_.Gender.Label :=
  { form := "pesak", gloss := "sand", gender := .masculine }

/-- *mleko* 'milk'. -/
def mleko : GenderedNoun _root_.Gender.Label :=
  { form := "mleko", gloss := "milk", gender := .neuter }

end Serbian.Gender
