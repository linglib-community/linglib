module

public import Linglib.Data.Wordlist.Schema

/-!
# `UchiharaMendozaRuiz2021`: word forms

Auto-generated from `Linglib/Data/Wordlist/UchiharaMendozaRuiz2021.json` by
`scripts/gen_wordlist.py`. Do not edit by hand; edit the JSON and re-run the generator. Declarations
live in `namespace UchiharaMendozaRuiz2021.Wordlist`.
-/

@[expose] public section

namespace UchiharaMendozaRuiz2021.Wordlist

open CLDF.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.white : Lexeme :=
  { id := "white", languageId := "alco1235", parameterId := "white" }

def Lexemes.animal : Lexeme :=
  { id := "animal", languageId := "alco1235", parameterId := "animal" }

def Lexemes.water : Lexeme :=
  { id := "water", languageId := "alco1235", parameterId := "water" }

def Lexemes.hammock : Lexeme :=
  { id := "hammock", languageId := "alco1235", parameterId := "hammock" }

def Lexemes.school : Lexeme :=
  { id := "school", languageId := "alco1235", parameterId := "school" }

def Lexemes.buzzard : Lexeme :=
  { id := "buzzard", languageId := "alco1235", parameterId := "buzzard" }

def Lexemes.police : Lexeme :=
  { id := "police", languageId := "alco1235", parameterId := "police" }

def Lexemes.hug : Lexeme :=
  { id := "hug", languageId := "alco1235", parameterId := "hug" }

def Lexemes.hugged : Lexeme :=
  { id := "hugged", languageId := "alco1235", parameterId := "hugged" }

def Lexemes.sold : Lexeme :=
  { id := "sold", languageId := "alco1235", parameterId := "sold" }

def ja3a3 : Form Cell :=
  { id := "uchiharamendozaruiz2021_ja3a3"
    lexeme := Lexemes.white
    cell := {}
    form := "ja3a3"
    segments := ["j", "a3", "a3"]
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(15)"⟩
    ] }

def ki3ti4 : Form Cell :=
  { id := "uchiharamendozaruiz2021_ki3ti4"
    lexeme := Lexemes.animal
    cell := {}
    form := "ki3ti4"
    segments := ["k", "i3", "t", "i4"]
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(16)"⟩
    ] }

def ti1kwi14i2 : Form Cell :=
  { id := "uchiharamendozaruiz2021_ti1kwi14i2"
    lexeme := Lexemes.water
    cell := {}
    form := "ti1kwi14i2"
    segments := ["t", "i1", "kw", "i14", "i2"]
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(17)"⟩
    ] }

def ma4ka2 : Form Cell :=
  { id := "uchiharamendozaruiz2021_ma4ka2"
    lexeme := Lexemes.hammock
    cell := {}
    form := "ma4ka2"
    segments := ["m", "a4", "k", "a2"]
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(42a)"⟩
    ] }

def skwe4la2 : Form Cell :=
  { id := "uchiharamendozaruiz2021_skwe4la2"
    lexeme := Lexemes.school
    cell := {}
    form := "skwe4la2"
    segments := ["s", "kw", "e4", "l", "a2"]
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(42d)"⟩
    ] }

def pe3lo3 : Form Cell :=
  { id := "uchiharamendozaruiz2021_pe3lo3"
    lexeme := Lexemes.buzzard
    cell := {}
    form := "pe3lo3"
    segments := ["p", "e3", "l", "o3"]
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(43a)"⟩
    ] }

def po3li3si4a2 : Form Cell :=
  { id := "uchiharamendozaruiz2021_po3li3si4a2"
    lexeme := Lexemes.police
    cell := {}
    form := "po3li3si4a2"
    segments := ["p", "o3", "l", "i3", "s", "i4", "a2"]
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(44a)"⟩
    ] }

def nu3mi3 : Form Cell :=
  { id := "uchiharamendozaruiz2021_nu3mi3"
    lexeme := Lexemes.hug
    cell := {}
    form := "nu3mi3"
    segments := ["n", "u3", "m", "i3"]
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(64)"⟩
    ] }

def nu2mi3 : Form Cell :=
  { id := "uchiharamendozaruiz2021_nu2mi3"
    lexeme := Lexemes.hugged
    cell := {}
    form := "nu2mi3"
    segments := ["n", "u2", "m", "i3"]
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(64)"⟩
    ] }

def ni1shi14ko3 : Form Cell :=
  { id := "uchiharamendozaruiz2021_ni1shi14ko3"
    lexeme := Lexemes.sold
    cell := {}
    form := "ni1shi14ko3"
    segments := ["n", "i1", "sh", "i14", "k", "o3"]
    source := [
      ⟨"uchihara-mendozaruiz-2021", "(5)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.white, Lexemes.animal, Lexemes.water, Lexemes.hammock,
  Lexemes.school, Lexemes.buzzard, Lexemes.police, Lexemes.hug, Lexemes.hugged, Lexemes.sold]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [ja3a3, ki3ti4, ti1kwi14i2, ma4ka2, skwe4la2, pe3lo3, po3li3si4a2,
  nu3mi3, nu2mi3, ni1shi14ko3]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "uchiharamendozaruiz2021_nu3mi3_nu2mi3", form := nu3mi3, target := nu2mi3,
    relation := "perfective", source := [
      ⟨"uchihara-mendozaruiz-2021", "(64)"⟩
    ] }]

end UchiharaMendozaRuiz2021.Wordlist
