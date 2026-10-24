module

public import Linglib.Syntax.Category.Noun.Basic

/-!
# German gender

This file defines the three German genders and the suffixes that fix the gender of a noun.
German has three controller genders, the masculine, the feminine and the neuter. The determiners
and the adjectives distinguish them in the singular and not in the plural, and
`German.Determiners` records that evidence. A noun's gender follows its meaning for many nouns
denoting persons and animals, and its ending for many others. Of the endings Durrell tabulates,
*-heit* ~ *-keit*, *-schaft* and *-ung* make a noun feminine and the diminutives *-chen* and
*-lein* make it neuter, and for these five he gives no exception. The diminutives do so whatever
the sex of the referent: *Mädchen* 'girl' and *Fräulein* 'young lady' are neuter, like *Bübchen*
'little boy'. Determiners and adjectives agree with that gender, relative pronouns almost always
do, and personal pronouns often follow the sex of the referent instead, especially in speech.

## Main definitions

* `German.Gender.Value`: the three genders.
* `German.Gender.Suffix`, `German.Gender.Suffix.gender`: the suffixes that fix the gender of the
  nouns they end, and the gender each fixes.
* `German.Gender.Suffix.noun`: a noun ending in such a suffix, whose gender is the suffix's.
* `German.GenderNumber`: the gender and number a noun phrase agrees in.

## References

* [durrell-2011]
-/

@[expose] public section

namespace German.Gender

/-- German has three controller genders. -/
inductive Value where
  | masc
  | fem
  | neut
  deriving DecidableEq, Repr, Fintype

/-- Each German gender bears the comparative label of the same name. -/
def Value.toLabel : Value → Gender.Label
  | .masc => .masculine
  | .fem => .feminine
  | .neut => .neuter

/-- The suffixes that fix the gender of every noun they end. -/
inductive Suffix where
  | heit
  | keit
  | schaft
  | ung
  | chen
  | lein
  deriving DecidableEq, Repr, Fintype

/-- `s.form` is the written form of the suffix `s`. -/
def Suffix.form : Suffix → String
  | .heit => "-heit"
  | .keit => "-keit"
  | .schaft => "-schaft"
  | .ung => "-ung"
  | .chen => "-chen"
  | .lein => "-lein"

/-- The suffixes *-heit* ~ *-keit*, *-schaft* and *-ung* fix the feminine, and the diminutives
*-chen* and *-lein* the neuter. -/
def Suffix.gender : Suffix → Value
  | .heit | .keit | .schaft | .ung => .fem
  | .chen | .lein => .neut

/-- `s.noun form gloss` is the noun `form` 'gloss' ending in the suffix `s`, and its gender is the
one `s` fixes. -/
def Suffix.noun (s : Suffix) (form gloss : String) (naturalGender : Option Gender.Label := none) :
    GenderedNoun Value :=
  { form, gloss, gender := s.gender, naturalGender }

theorem Suffix.isNaturalGender_noun_iff (s : Suffix) (form gloss : String) (g : Gender.Label) :
    (s.noun form gloss g).IsNaturalGender Value.toLabel ↔ g = s.gender.toLabel := by
  simp [noun, GenderedNoun.IsNaturalGender]

/-! ### Nouns -/

/-- *Krankheit* 'illness' is a noun in *-heit*. -/
def krankheit : GenderedNoun Value := Suffix.heit.noun "Krankheit" "illness"

/-- *Herrschaft* 'rule' is a noun in *-schaft*. -/
def herrschaft : GenderedNoun Value := Suffix.schaft.noun "Herrschaft" "rule"

/-- *Bedeutung* 'meaning' is a noun in *-ung*. -/
def bedeutung : GenderedNoun Value := Suffix.ung.noun "Bedeutung" "meaning"

/-- *Büchlein* 'little book' is a noun in *-lein*. -/
def buechlein : GenderedNoun Value := Suffix.lein.noun "Büchlein" "little book"

/-- *Mädchen* 'girl' is neuter, though its referents are female. -/
def maedchen : GenderedNoun Value := Suffix.chen.noun "Mädchen" "girl" (some .feminine)

/-- *Fräulein* 'young lady' is neuter, though its referents are female. -/
def fraeulein : GenderedNoun Value := Suffix.lein.noun "Fräulein" "young lady" (some .feminine)

/-- *Bübchen* 'little boy' is neuter, though its referents are male. -/
def buebchen : GenderedNoun Value := Suffix.chen.noun "Bübchen" "little boy" (some .masculine)

theorem not_isNaturalGender_diminutive :
    ¬ maedchen.IsNaturalGender Value.toLabel ∧ ¬ fraeulein.IsNaturalGender Value.toLabel ∧
      ¬ buebchen.IsNaturalGender Value.toLabel := by
  decide

end German.Gender

namespace German

/-- The agreement value of a German noun phrase, a gender in the singular and only a number in the
plural, where the genders fall together. -/
inductive GenderNumber where
  | sg (g : Gender.Value)
  | pl
  deriving DecidableEq, Repr, Fintype

end German
