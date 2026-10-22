module

public import Linglib.Data.Wordlist.Schema

/-!
# `Booij2010`: word forms

Auto-generated from `Linglib/Data/Wordlist/Booij2010.json` by `scripts/gen_wordlist.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Booij2010.Wordlist`.
-/

@[expose] public section

namespace Booij2010.Wordlist

open Data.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.carlessness : Lexeme :=
  { id := "carlessness", languageId := "stan1293", parameterId := "carlessness" }

def Lexemes.baldness : Lexeme :=
  { id := "baldness", languageId := "stan1293", parameterId := "baldness" }

def Lexemes.bigness : Lexeme :=
  { id := "bigness", languageId := "stan1293", parameterId := "bigness" }

def Lexemes.blackness : Lexeme :=
  { id := "blackness", languageId := "stan1293", parameterId := "blackness" }

def Lexemes.britishness : Lexeme :=
  { id := "britishness", languageId := "stan1293", parameterId := "britishness" }

def Lexemes.awareness : Lexeme :=
  { id := "awareness", languageId := "stan1293", parameterId := "awareness" }

def Lexemes.readable : Lexeme :=
  { id := "readable", languageId := "dutc1256", parameterId := "readable" }

def Lexemes.workable : Lexeme :=
  { id := "workable", languageId := "dutc1256", parameterId := "workable" }

def Lexemes.unsuppressable : Lexeme :=
  { id := "unsuppressable", languageId := "dutc1256", parameterId := "unsuppressable" }

def carlessness : Form Cell :=
  { id := "booij2010_carlessness"
    lexeme := Lexemes.carlessness
    cell := {}
    form := "carlessness"
    segments := ["carless", "ness"]
    source := [
      ⟨"booij-2010-compass", ""⟩
    ] }

def baldness : Form Cell :=
  { id := "booij2010_baldness"
    lexeme := Lexemes.baldness
    cell := {}
    form := "baldness"
    segments := ["bald", "ness"]
    source := [
      ⟨"booij-2010-compass", "(1)"⟩
    ] }

def bigness : Form Cell :=
  { id := "booij2010_bigness"
    lexeme := Lexemes.bigness
    cell := {}
    form := "bigness"
    segments := ["big", "ness"]
    source := [
      ⟨"booij-2010-compass", "(1)"⟩
    ] }

def blackness : Form Cell :=
  { id := "booij2010_blackness"
    lexeme := Lexemes.blackness
    cell := {}
    form := "blackness"
    segments := ["black", "ness"]
    source := [
      ⟨"booij-2010-compass", "(1)"⟩
    ] }

def britishness : Form Cell :=
  { id := "booij2010_britishness"
    lexeme := Lexemes.britishness
    cell := {}
    form := "Britishness"
    segments := ["British", "ness"]
    source := [
      ⟨"booij-2010-compass", "(1)"⟩
    ] }

def awareness : Form Cell :=
  { id := "booij2010_awareness"
    lexeme := Lexemes.awareness
    cell := {}
    form := "awareness"
    segments := ["aware", "ness"]
    source := [
      ⟨"booij-2010-compass", "(2)"⟩
    ] }

def leesbaar : Form Cell :=
  { id := "booij2010_leesbaar"
    lexeme := Lexemes.readable
    cell := {}
    form := "leesbaar"
    segments := ["lees", "baar"]
    source := [
      ⟨"booij-2010-compass", ""⟩
    ] }

def werkbaar : Form Cell :=
  { id := "booij2010_werkbaar"
    lexeme := Lexemes.workable
    cell := {}
    form := "werkbaar"
    segments := ["werk", "baar"]
    source := [
      ⟨"booij-2010-compass", ""⟩
    ] }

def onbedwingbaar : Form Cell :=
  { id := "booij2010_onbedwingbaar"
    lexeme := Lexemes.unsuppressable
    cell := {}
    form := "onbedwingbaar"
    segments := ["on", "bedwing", "baar"]
    source := [
      ⟨"booij-2010-compass", "(15)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.carlessness, Lexemes.baldness, Lexemes.bigness,
  Lexemes.blackness, Lexemes.britishness, Lexemes.awareness, Lexemes.readable, Lexemes.workable,
  Lexemes.unsuppressable]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [carlessness, baldness, bigness, blackness, britishness, awareness,
  leesbaar, werkbaar, onbedwingbaar]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

end Booij2010.Wordlist
