module

public import Linglib.Data.Wordlist.Schema

/-!
# `Booij2019`: word forms

Auto-generated from `Linglib/Data/Wordlist/Booij2019.json` by `scripts/gen_wordlist.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Booij2019.Wordlist`.
-/

@[expose] public section

namespace Booij2019.Wordlist

open CLDF.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.baker : Lexeme :=
  { id := "baker", languageId := "nort3139", parameterId := "baker" }

def Lexemes.servant : Lexeme :=
  { id := "servant", languageId := "nort3139", parameterId := "servant" }

def Lexemes.doorkeeper : Lexeme :=
  { id := "doorkeeper", languageId := "nort3139", parameterId := "doorkeeper" }

def Lexemes.fish_seller : Lexeme :=
  { id := "fish_seller", languageId := "nort3139", parameterId := "fish_seller" }

def Lexemes.guest : Lexeme :=
  { id := "guest", languageId := "java1254", parameterId := "guest" }

def Lexemes.to_visit : Lexeme :=
  { id := "to_visit", languageId := "java1254", parameterId := "to_visit" }

def Lexemes.rain : Lexeme :=
  { id := "rain", languageId := "java1254", parameterId := "rain" }

def Lexemes.to_play_in_the_rain : Lexeme :=
  { id := "to_play_in_the_rain", languageId := "java1254", parameterId := "to_play_in_the_rain" }

def Lexemes.fire : Lexeme :=
  { id := "fire", languageId := "java1254", parameterId := "fire" }

def Lexemes.to_warm_oneself_by_the_fire : Lexeme :=
  { id := "to_warm_oneself_by_the_fire", languageId := "java1254",
    parameterId := "to_warm_oneself_by_the_fire" }

def Lexemes.big : Lexeme :=
  { id := "big", languageId := "egyp1253", parameterId := "big" }

def Lexemes.bigger : Lexeme :=
  { id := "bigger", languageId := "egyp1253", parameterId := "bigger" }

def Lexemes.fat : Lexeme :=
  { id := "fat", languageId := "egyp1253", parameterId := "fat" }

def Lexemes.fatter : Lexeme :=
  { id := "fatter", languageId := "egyp1253", parameterId := "fatter" }

def xabbaaz : Form Cell :=
  { id := "booij2019_xabbaaz"
    lexeme := Lexemes.baker
    cell := {}
    form := "xabbaaz"
    segments := ["x", "a", "b", "b", "aa", "z"]
    source := [
      ⟨"booij-2019", "(1)"⟩
    ] }

def xaddaam : Form Cell :=
  { id := "booij2019_xaddaam"
    lexeme := Lexemes.servant
    cell := {}
    form := "xaddaam"
    segments := ["x", "a", "d", "d", "aa", "m"]
    source := [
      ⟨"booij-2019", "(1)"⟩
    ] }

def bawwaab : Form Cell :=
  { id := "booij2019_bawwaab"
    lexeme := Lexemes.doorkeeper
    cell := {}
    form := "bawwaab"
    segments := ["b", "a", "w", "w", "aa", "b"]
    source := [
      ⟨"booij-2019", "(1)"⟩
    ] }

def sammaak : Form Cell :=
  { id := "booij2019_sammaak"
    lexeme := Lexemes.fish_seller
    cell := {}
    form := "sammaak"
    segments := ["s", "a", "m", "m", "aa", "k"]
    source := [
      ⟨"booij-2019", "(1)"⟩
    ] }

def tamu : Form Cell :=
  { id := "booij2019_tamu"
    lexeme := Lexemes.guest
    cell := {}
    form := "tamu"
    segments := ["t", "amu"]
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] }

def tetamu : Form Cell :=
  { id := "booij2019_tetamu"
    lexeme := Lexemes.to_visit
    cell := {}
    form := "tətamu"
    segments := ["t", "ə", "t", "amu"]
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] }

def jawah : Form Cell :=
  { id := "booij2019_jawah"
    lexeme := Lexemes.rain
    cell := {}
    form := "jawah"
    segments := ["j", "awah"]
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] }

def jejawah : Form Cell :=
  { id := "booij2019_jejawah"
    lexeme := Lexemes.to_play_in_the_rain
    cell := {}
    form := "jəjawah"
    segments := ["j", "ə", "j", "awah"]
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] }

def geni : Form Cell :=
  { id := "booij2019_geni"
    lexeme := Lexemes.fire
    cell := {}
    form := "gəni"
    segments := ["g", "əni"]
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] }

def gegeni : Form Cell :=
  { id := "booij2019_gegeni"
    lexeme := Lexemes.to_warm_oneself_by_the_fire
    cell := {}
    form := "gəgəni"
    segments := ["g", "ə", "g", "əni"]
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] }

def kibiir : Form Cell :=
  { id := "booij2019_kibiir"
    lexeme := Lexemes.big
    cell := {}
    form := "kibiir"
    segments := ["k", "i", "b", "ii", "r"]
    source := [
      ⟨"booij-2019", "(15)"⟩
    ] }

def akbar : Form Cell :=
  { id := "booij2019_akbar"
    lexeme := Lexemes.bigger
    cell := {}
    form := "akbar"
    segments := ["a", "k", "b", "a", "r"]
    source := [
      ⟨"booij-2019", "(15)"⟩
    ] }

def tixiin : Form Cell :=
  { id := "booij2019_tixiin"
    lexeme := Lexemes.fat
    cell := {}
    form := "tixiin"
    segments := ["t", "i", "x", "ii", "n"]
    source := [
      ⟨"booij-2019", "(15)"⟩
    ] }

def atxan : Form Cell :=
  { id := "booij2019_atxan"
    lexeme := Lexemes.fatter
    cell := {}
    form := "atxan"
    segments := ["a", "t", "x", "a", "n"]
    source := [
      ⟨"booij-2019", "(15)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.baker, Lexemes.servant, Lexemes.doorkeeper,
  Lexemes.fish_seller, Lexemes.guest, Lexemes.to_visit, Lexemes.rain, Lexemes.to_play_in_the_rain,
  Lexemes.fire, Lexemes.to_warm_oneself_by_the_fire, Lexemes.big, Lexemes.bigger, Lexemes.fat,
  Lexemes.fatter]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [xabbaaz, xaddaam, bawwaab, sammaak, tamu, tetamu, jawah, jejawah,
  geni, gegeni, kibiir, akbar, tixiin, atxan]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "booij2019_tamu_tetamu", form := tamu, target := tetamu, relation := "reduplication",
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] },
  { id := "booij2019_jawah_jejawah", form := jawah, target := jejawah, relation := "reduplication",
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] },
  { id := "booij2019_geni_gegeni", form := geni, target := gegeni, relation := "reduplication",
    source := [
      ⟨"booij-2019", "(12)"⟩
    ] },
  { id := "booij2019_kibiir_akbar", form := kibiir, target := akbar, relation := "comparative",
    source := [
      ⟨"booij-2019", "(15)"⟩
    ] },
  { id := "booij2019_tixiin_atxan", form := tixiin, target := atxan, relation := "comparative",
    source := [
      ⟨"booij-2019", "(15)"⟩
    ] }]

end Booij2019.Wordlist
