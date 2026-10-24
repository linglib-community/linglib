module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Coastal Marind gender

This file records the four genders of Coastal Marind (Anim, South New Guinea), the forms of
words that agree with them, and nouns whose form varies with gender, after Olsson.

Gender I holds male humans, gender II female humans and all animals, and genders III and IV
divide the inanimates. Demonstratives, a few adjectives and some postpositions agree by a
stem-final gender vowel, *e*, *u*, *a*, *i* for genders I–IV, with syncretisms particular to
each target. Only genders I and II distinguish number, and on every form recorded here their
plural is the singular form of gender IV (`Gender.pluralGender`); the full demonstrative
paradigm still separates the four genders (`faithful_demonstrative`). A few nouns vary their
stem vowel with gender in the same way, and *nanVh* 'face' takes the gender of the one whose
face it is, Olsson's inherited gender.

## Implementation notes

* Number is a value of the singular-plural system, and matters only for genders I and II.
* Demonstratives are segmented into their gender vowel and the stem, as in *e-pe*.
* Only forms alternating by the gender vowel are recorded. The suppletive adjective 'small',
  the one target that distinguishes number in genders III and IV, and the number-suppletive
  verb stems group gender IV with the animate plurals too; neither is recorded.

## References

* [olsson-2021]
* [corbett-1998]
-/

@[expose] public section

namespace CoastalMarind

/-- The four genders ([olsson-2021] §5.1). -/
inductive Gender where
  /-- Male humans. -/
  | gI
  /-- Female humans and all animals. -/
  | gII
  /-- Most inanimates, and the default: ideophones and adverbial demonstratives take its
  forms. -/
  | gIII
  /-- The remaining inanimates, whose agreements are the animate plurals'. -/
  | gIV
  deriving DecidableEq, Repr, Fintype

/-- Coastal Marind distinguishes the singular and the plural. -/
def numberSystem : Number.System := { values := {.singular, .plural} }

/-- The distal demonstrative *Vpe*, by gender and number ([olsson-2021] Table 4.2). -/
def demonstrative (g : Gender) : numberSystem.values → String :=
  numberSystem.elim (match g with | .gI | .gIII => "e-pe" | .gII => "u-pe" | .gIV => "i-pe")
    (match g with | .gIII => "e-pe" | .gI | .gII | .gIV => "i-pe")

/-- The similative postposition *hV* 'like', which is *hu* for gender II in the singular and *hi*
otherwise ([olsson-2021] §3.3). -/
def similative (g : Gender) : numberSystem.values → String :=
  numberSystem.elim (match g with | .gII => "hu" | .gI | .gIII | .gIV => "hi") "hi"

/-- The adjective *ak-k* 'light (in weight)', by gender and number ([olsson-2021] Table 3.3). -/
def light (g : Gender) : numberSystem.values → String :=
  numberSystem.elim
    (match g with | .gI => "akek" | .gII => "akuk" | .gIII => "akak" | .gIV => "akik")
    (match g with | .gIII => "akak" | .gI | .gII | .gIV => "akik")

/-- The noun *nanVh* 'face', by the gender and number of the one whose face it is: the one
noun with overt alternation among the three that take their referent's gender, Olsson's
inherited gender ([olsson-2021] §5.2.3). -/
def face (g : Gender) : numberSystem.values → String :=
  numberSystem.elim (match g with | .gII => "nanuh" | .gI | .gIII | .gIV => "nanih") "nanih"

/-! ### Agreement patterns -/

/-- The distal demonstrative alone separates the four genders, I and III sharing *e-pe* only in
the singular and I, II and IV sharing *i-pe* only in the plural ([olsson-2021] §5.1). -/
theorem faithful_demonstrative : Gender.Faithful demonstrative := by decide

/-- The gender whose singular form a gender's plural takes: gender IV, except that gender III
does not distinguish number. Every recorded form realizes the plural of genders I and II as the
singular of gender IV, the plural–gender IV affinity that [olsson-2021] §5.3.2 extends to
number-suppletive verb stems. -/
def Gender.pluralGender : Gender → Gender
  | .gIII => .gIII
  | _ => .gIV

theorem demonstrative_plural (g : Gender) :
    demonstrative g (numberSystem.value .plural) =
      demonstrative g.pluralGender (numberSystem.value .singular) := by cases g <;> rfl

theorem similative_plural (g : Gender) :
    similative g (numberSystem.value .plural) =
      similative g.pluralGender (numberSystem.value .singular) := by cases g <;> rfl

theorem light_plural (g : Gender) :
    light g (numberSystem.value .plural) =
      light g.pluralGender (numberSystem.value .singular) := by cases g <;> rfl

theorem face_plural (g : Gender) :
    face g (numberSystem.value .plural) =
      face g.pluralGender (numberSystem.value .singular) := by cases g <;> rfl

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
