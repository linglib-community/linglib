module

public import Linglib.Data.Wordlist.Schema

/-!
# `Audring2019`: word forms

Auto-generated from `Linglib/Data/Wordlist/Audring2019.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Audring2019.Wordlist`.
-/

@[expose] public section

namespace Audring2019.Wordlist

open Data.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.like_a_boy : Lexeme :=
  { id := "like_a_boy", languageId := "stan1293", parameterId := "like_a_boy" }

def Lexemes.like_a_fool : Lexeme :=
  { id := "like_a_fool", languageId := "stan1293", parameterId := "like_a_fool" }

def Lexemes.like_a_child : Lexeme :=
  { id := "like_a_child", languageId := "stan1293", parameterId := "like_a_child" }

def Lexemes.like_trump : Lexeme :=
  { id := "like_trump", languageId := "stan1293", parameterId := "like_trump" }

def Lexemes.careful : Lexeme :=
  { id := "careful", languageId := "stan1293", parameterId := "careful" }

def Lexemes.careless : Lexeme :=
  { id := "careless", languageId := "stan1293", parameterId := "careless" }

def Lexemes.clueless : Lexeme :=
  { id := "clueless", languageId := "stan1293", parameterId := "clueless" }

def boyish : Form Cell :=
  { id := "audring2019_boyish"
    lexeme := Lexemes.like_a_boy
    cell := {}
    form := "boyish"
    segments := ["boy", "ish"]
    source := [
      ⟨"audring-2019", "(8)"⟩
    ] }

def foolish : Form Cell :=
  { id := "audring2019_foolish"
    lexeme := Lexemes.like_a_fool
    cell := {}
    form := "foolish"
    segments := ["fool", "ish"]
    source := [
      ⟨"audring-2019", "(8)"⟩
    ] }

def childish : Form Cell :=
  { id := "audring2019_childish"
    lexeme := Lexemes.like_a_child
    cell := {}
    form := "childish"
    segments := ["child", "ish"]
    source := [
      ⟨"audring-2019", "(8)"⟩
    ] }

def trumpish : Form Cell :=
  { id := "audring2019_trumpish"
    lexeme := Lexemes.like_trump
    cell := {}
    form := "Trumpish"
    segments := ["Trump", "ish"]
    source := [
      ⟨"audring-2019", "4.1"⟩
    ] }

def careful : Form Cell :=
  { id := "audring2019_careful"
    lexeme := Lexemes.careful
    cell := {}
    form := "careful"
    segments := ["care", "ful"]
    source := [
      ⟨"audring-2019", "5"⟩
    ] }

def careless : Form Cell :=
  { id := "audring2019_careless"
    lexeme := Lexemes.careless
    cell := {}
    form := "careless"
    segments := ["care", "less"]
    source := [
      ⟨"audring-2019", "5"⟩
    ] }

def clueless : Form Cell :=
  { id := "audring2019_clueless"
    lexeme := Lexemes.clueless
    cell := {}
    form := "clueless"
    segments := ["clue", "less"]
    source := [
      ⟨"audring-2019", "4.2.2"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.like_a_boy, Lexemes.like_a_fool, Lexemes.like_a_child,
  Lexemes.like_trump, Lexemes.careful, Lexemes.careless, Lexemes.clueless]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [boyish, foolish, childish, trumpish, careful, careless, clueless]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "audring2019_boyish_foolish", form := boyish, target := foolish, relation := "same_affix",
    source := [
      ⟨"audring-2019", "(8)"⟩
    ] },
  { id := "audring2019_boyish_childish", form := boyish, target := childish,
    relation := "same_affix", source := [
      ⟨"audring-2019", "(8)"⟩
    ] },
  { id := "audring2019_foolish_childish", form := foolish, target := childish,
    relation := "same_affix", source := [
      ⟨"audring-2019", "(8)"⟩
    ] },
  { id := "audring2019_careful_careless", form := careful, target := careless,
    relation := "second_order_schema", source := [
      ⟨"audring-2019", "(14)"⟩
    ] }]

end Audring2019.Wordlist
