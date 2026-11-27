module

public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Languages.Romance.Italian.Gender

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
structure Noun extends GenderedNoun Gender.Value where
  /-- The plural form. -/
  formPl : String
  /-- The gender of the plural. -/
  plGender : Gender.Value
  /-- The plural class. -/
  pluralClass : PluralClass
  deriving DecidableEq, Repr

/-- The *-a* plurals. -/
def aPlurals : List Noun :=
  [⟨⟨⟨"braccio", "arm", none⟩, .masculine⟩, "braccia", .feminine, .aPlural⟩,
    ⟨⟨⟨"budello", "intestine", none⟩, .masculine⟩, "budella", .feminine, .aPlural⟩,
    ⟨⟨⟨"cervello", "brain", none⟩, .masculine⟩, "cervella", .feminine, .aPlural⟩,
    ⟨⟨⟨"ciglio", "eyelash", none⟩, .masculine⟩, "ciglia", .feminine, .aPlural⟩,
    ⟨⟨⟨"corno", "horn", none⟩, .masculine⟩, "corna", .feminine, .aPlural⟩,
    ⟨⟨⟨"dito", "finger", none⟩, .masculine⟩, "dita", .feminine, .aPlural⟩,
    ⟨⟨⟨"fondamento", "foundation", none⟩, .masculine⟩, "fondamenta", .feminine, .aPlural⟩,
    ⟨⟨⟨"ginocchio", "knee", none⟩, .masculine⟩, "ginocchia", .feminine, .aPlural⟩,
    ⟨⟨⟨"grido", "shout", none⟩, .masculine⟩, "grida", .feminine, .aPlural⟩,
    ⟨⟨⟨"labbro", "lip", none⟩, .masculine⟩, "labbra", .feminine, .aPlural⟩,
    ⟨⟨⟨"lenzuolo", "sheet", none⟩, .masculine⟩, "lenzuola", .feminine, .aPlural⟩,
    ⟨⟨⟨"membro", "limb", none⟩, .masculine⟩, "membra", .feminine, .aPlural⟩,
    ⟨⟨⟨"miglio", "mile", none⟩, .masculine⟩, "miglia", .feminine, .aPlural⟩,
    ⟨⟨⟨"muro", "wall", none⟩, .masculine⟩, "mura", .feminine, .aPlural⟩,
    ⟨⟨⟨"osso", "bone", none⟩, .masculine⟩, "ossa", .feminine, .aPlural⟩,
    ⟨⟨⟨"paio", "pair", none⟩, .masculine⟩, "paia", .feminine, .aPlural⟩,
    ⟨⟨⟨"riso", "laugh", none⟩, .masculine⟩, "risa", .feminine, .aPlural⟩,
    ⟨⟨⟨"sopracciglio", "eyebrow", none⟩, .masculine⟩, "sopracciglia", .feminine, .aPlural⟩,
    ⟨⟨⟨"strido", "shriek", none⟩, .masculine⟩, "strida", .feminine, .aPlural⟩,
    ⟨⟨⟨"uovo", "egg", none⟩, .masculine⟩, "uova", .feminine, .aPlural⟩,
    ⟨⟨⟨"urlo", "howl", none⟩, .masculine⟩, "urla", .feminine, .aPlural⟩]

/-- Regular plurals. -/
def regulars : List Noun :=
  [⟨⟨⟨"libro", "book", none⟩, .masculine⟩, "libri", .masculine, .regular⟩,
    ⟨⟨⟨"ragazzo", "boy", some .male⟩, .masculine⟩, "ragazzi", .masculine, .regular⟩,
    ⟨⟨⟨"casa", "house", none⟩, .feminine⟩, "case", .feminine, .regular⟩,
    ⟨⟨⟨"ragazza", "girl", some .female⟩, .feminine⟩, "ragazze", .feminine, .regular⟩]

end Italian.NumberGender
