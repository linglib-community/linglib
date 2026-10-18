module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Coastal Marind gender

This file records the four genders of Coastal Marind (Anim, South New Guinea), the forms of
words that agree with them, and nouns whose form varies with gender, after Olsson.

Gender I holds men, gender II women and animals, and genders III and IV inanimates. Only genders
I and II distinguish number, and their plural takes the agreement of gender IV. Demonstratives,
a few adjectives and some postpositions agree by a gender vowel. A few nouns vary their stem
vowel with gender in the same way; *nanVh* 'face' takes the gender of the one whose face it is.

## Implementation notes

* Number is a value of the singular-plural system, and matters only for genders I and II.
* Demonstratives are segmented into their gender vowel and the stem, as in *e-pe*.

## References

* [olsson-2021]
* [corbett-1998]
-/

@[expose] public section

namespace CoastalMarind

/-- The four genders. -/
inductive Gender where
  /-- Men. -/
  | gI
  /-- Women and animals. -/
  | gII
  /-- Inanimates. -/
  | gIII
  /-- Inanimates. -/
  | gIV
  deriving DecidableEq, Repr, Fintype

/-- Coastal Marind distinguishes the singular and the plural. -/
abbrev numberSystem : Number.System := .singularPlural

/-- The distal demonstrative, by gender and number. -/
def demonstrative (g : Gender) (n : numberSystem.values) : String :=
  match g, n.1 with
  | .gI, .singular | .gIII, _ => "e-pe"
  | .gII, .singular => "u-pe"
  | _, _ => "i-pe"

/-- The similative postposition *hV* 'like', which is *hu* for gender II in the singular and *hi*
otherwise. -/
def similative (g : Gender) (n : numberSystem.values) : String :=
  match g, n.1 with
  | .gII, .singular => "hu"
  | _, _ => "hi"

/-- The adjective *ak-k* 'light (in weight)', by gender and number. -/
def light (g : Gender) (n : numberSystem.values) : String :=
  match g, n.1 with
  | .gI, .singular => "akek"
  | .gII, .singular => "akuk"
  | .gIII, _ => "akak"
  | _, _ => "akik"

/-- The noun *nanVh* 'face', by the gender and number of the one whose face it is. -/
def face (g : Gender) (n : numberSystem.values) : String :=
  match g, n.1 with
  | .gII, .singular => "nanuh"
  | _, _ => "nanih"

/-- A noun with its gender. -/
abbrev Noun := GenderedNoun Gender

/-! ### Nouns with overt gender -/

/-- *anem* 'man'. -/
def anem : Noun := ⟨⟨"anem", "man"⟩, .gI, some .masculine⟩

/-- *anum* 'woman'. -/
def anum : Noun := ⟨⟨"anum", "woman"⟩, .gII, some .feminine⟩

/-- *namek* 'clanmate', of a man. -/
def namek : Noun := ⟨⟨"namek", "clanmate"⟩, .gI, some .masculine⟩

/-- *namuk* 'clanmate', of a woman. -/
def namuk : Noun := ⟨⟨"namuk", "clanmate"⟩, .gII, some .feminine⟩

/-- *wananggib* 'son'. -/
def wananggib : Noun := ⟨⟨"wananggib", "son"⟩, .gI, some .masculine⟩

/-- *wananggub* 'daughter'. -/
def wananggub : Noun := ⟨⟨"wananggub", "daughter"⟩, .gII, some .feminine⟩

/-- *eɣal* 'a certain man'. -/
def «eɣal» : Noun := ⟨⟨"eɣal", "a certain man"⟩, .gI, some .masculine⟩

/-- *eɣul* 'a certain woman'. -/
def «eɣul» : Noun := ⟨⟨"eɣul", "a certain woman"⟩, .gII, some .feminine⟩

end CoastalMarind
