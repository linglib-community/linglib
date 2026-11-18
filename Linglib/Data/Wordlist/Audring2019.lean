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

open CLDF.Wordlist

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

def Lexemes.childless : Lexeme :=
  { id := "childless", languageId := "stan1293", parameterId := "childless" }

def Lexemes.helpful : Lexeme :=
  { id := "helpful", languageId := "stan1293", parameterId := "helpful" }

def Lexemes.helpless : Lexeme :=
  { id := "helpless", languageId := "stan1293", parameterId := "helpless" }

def boyish : Form Cell :=
  { id := "audring2019_boyish"
    lexeme := Lexemes.like_a_boy
    cell := {}
    form := "boyish"
    morphs := ["boy", "ish"]
    source := [
      ⟨"audring-2019", "(8)"⟩
    ] }

def foolish : Form Cell :=
  { id := "audring2019_foolish"
    lexeme := Lexemes.like_a_fool
    cell := {}
    form := "foolish"
    morphs := ["fool", "ish"]
    source := [
      ⟨"audring-2019", "(8)"⟩
    ] }

def childish : Form Cell :=
  { id := "audring2019_childish"
    lexeme := Lexemes.like_a_child
    cell := {}
    form := "childish"
    morphs := ["child", "ish"]
    source := [
      ⟨"audring-2019", "(8)"⟩
    ] }

def trumpish : Form Cell :=
  { id := "audring2019_trumpish"
    lexeme := Lexemes.like_trump
    cell := {}
    form := "Trumpish"
    morphs := ["Trump", "ish"]
    source := [
      ⟨"audring-2019", "4.1"⟩
    ] }

def careful : Form Cell :=
  { id := "audring2019_careful"
    lexeme := Lexemes.careful
    cell := {}
    form := "careful"
    morphs := ["care", "ful"]
    source := [
      ⟨"audring-2019", "5"⟩
    ] }

def careless : Form Cell :=
  { id := "audring2019_careless"
    lexeme := Lexemes.careless
    cell := {}
    form := "careless"
    morphs := ["care", "less"]
    source := [
      ⟨"audring-2019", "5"⟩
    ] }

def clueless : Form Cell :=
  { id := "audring2019_clueless"
    lexeme := Lexemes.clueless
    cell := {}
    form := "clueless"
    morphs := ["clue", "less"]
    source := [
      ⟨"audring-2019", "4.2.2"⟩
    ] }

def childless : Form Cell :=
  { id := "audring2019_childless"
    lexeme := Lexemes.childless
    cell := {}
    form := "childless"
    morphs := ["child", "less"]
    source := [
      ⟨"audring-2019", "(10)"⟩
    ] }

def helpful : Form Cell :=
  { id := "audring2019_helpful"
    lexeme := Lexemes.helpful
    cell := {}
    form := "helpful"
    morphs := ["help", "ful"]
    source := [
      ⟨"audring-2019", "(12)"⟩
    ] }

def helpless : Form Cell :=
  { id := "audring2019_helpless"
    lexeme := Lexemes.helpless
    cell := {}
    form := "helpless"
    morphs := ["help", "less"]
    source := [
      ⟨"audring-2019", "(12)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.like_a_boy, Lexemes.like_a_fool, Lexemes.like_a_child,
  Lexemes.like_trump, Lexemes.careful, Lexemes.careless, Lexemes.clueless, Lexemes.childless,
  Lexemes.helpful, Lexemes.helpless]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [boyish, foolish, childish, trumpish, careful, careless, clueless,
  childless, helpful, helpless]

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
      ⟨"audring-2019", "5"⟩
    ] },
  { id := "audring2019_childish_childless", form := childish, target := childless,
    relation := "same_stem", source := [
      ⟨"audring-2019", "(10)"⟩
    ] },
  { id := "audring2019_helpful_helpless", form := helpful, target := helpless,
    relation := "second_order_schema", source := [
      ⟨"audring-2019", "(12)"⟩
    ] }]

end Audring2019.Wordlist
