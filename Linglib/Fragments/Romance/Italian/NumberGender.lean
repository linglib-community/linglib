module

public import Linglib.Syntax.Category.Noun.Basic

/-!
# Italian plurals in *-a*

The Standard Italian nouns whose plural ends in unstressed *-a* and is feminine although the
singular is masculine, after Maiden and Robustelli's list as given in [adamson-2024], beside
regular plurals in *-i* and *-e* that keep the singular's gender.

## References

* [adamson-2024]
-/

@[expose] public section

namespace Italian.NumberGender

/-- The plural class by ending: the irregular *-a* plural or the regular *-i* / *-e* one. -/
inductive PluralClass where
  | aPlural
  | regular
  deriving DecidableEq, Repr, Fintype

/-- A noun with its singular form and gender, its plural form and gender, and its plural
class. -/
structure Noun extends GenderedNoun Gender where
  /-- The plural form. -/
  formPl : String
  /-- The gender of the plural. -/
  plGender : Gender
  /-- The plural class. -/
  pluralClass : PluralClass
  deriving DecidableEq, Repr

/-- The *-a* plurals. -/
def aPlurals : List Noun :=
  [⟨⟨⟨"braccio", "arm"⟩, .masculine, none⟩, "braccia", .feminine, .aPlural⟩,
    ⟨⟨⟨"budello", "intestine"⟩, .masculine, none⟩, "budella", .feminine, .aPlural⟩,
    ⟨⟨⟨"cervello", "brain"⟩, .masculine, none⟩, "cervella", .feminine, .aPlural⟩,
    ⟨⟨⟨"ciglio", "eyelash"⟩, .masculine, none⟩, "ciglia", .feminine, .aPlural⟩,
    ⟨⟨⟨"corno", "horn"⟩, .masculine, none⟩, "corna", .feminine, .aPlural⟩,
    ⟨⟨⟨"dito", "finger"⟩, .masculine, none⟩, "dita", .feminine, .aPlural⟩,
    ⟨⟨⟨"fondamento", "foundation"⟩, .masculine, none⟩, "fondamenta", .feminine, .aPlural⟩,
    ⟨⟨⟨"ginocchio", "knee"⟩, .masculine, none⟩, "ginocchia", .feminine, .aPlural⟩,
    ⟨⟨⟨"grido", "shout"⟩, .masculine, none⟩, "grida", .feminine, .aPlural⟩,
    ⟨⟨⟨"labbro", "lip"⟩, .masculine, none⟩, "labbra", .feminine, .aPlural⟩,
    ⟨⟨⟨"lenzuolo", "sheet"⟩, .masculine, none⟩, "lenzuola", .feminine, .aPlural⟩,
    ⟨⟨⟨"membro", "limb"⟩, .masculine, none⟩, "membra", .feminine, .aPlural⟩,
    ⟨⟨⟨"miglio", "mile"⟩, .masculine, none⟩, "miglia", .feminine, .aPlural⟩,
    ⟨⟨⟨"muro", "wall"⟩, .masculine, none⟩, "mura", .feminine, .aPlural⟩,
    ⟨⟨⟨"osso", "bone"⟩, .masculine, none⟩, "ossa", .feminine, .aPlural⟩,
    ⟨⟨⟨"paio", "pair"⟩, .masculine, none⟩, "paia", .feminine, .aPlural⟩,
    ⟨⟨⟨"riso", "laugh"⟩, .masculine, none⟩, "risa", .feminine, .aPlural⟩,
    ⟨⟨⟨"sopracciglio", "eyebrow"⟩, .masculine, none⟩, "sopracciglia", .feminine, .aPlural⟩,
    ⟨⟨⟨"strido", "shriek"⟩, .masculine, none⟩, "strida", .feminine, .aPlural⟩,
    ⟨⟨⟨"uovo", "egg"⟩, .masculine, none⟩, "uova", .feminine, .aPlural⟩,
    ⟨⟨⟨"urlo", "howl"⟩, .masculine, none⟩, "urla", .feminine, .aPlural⟩]

/-- Regular plurals. -/
def regulars : List Noun :=
  [⟨⟨⟨"libro", "book"⟩, .masculine, none⟩, "libri", .masculine, .regular⟩,
    ⟨⟨⟨"ragazzo", "boy"⟩, .masculine, some .male⟩, "ragazzi", .masculine, .regular⟩,
    ⟨⟨⟨"casa", "house"⟩, .feminine, none⟩, "case", .feminine, .regular⟩,
    ⟨⟨⟨"ragazza", "girl"⟩, .feminine, some .female⟩, "ragazze", .feminine, .regular⟩]

end Italian.NumberGender
