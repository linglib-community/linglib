module

public import Linglib.Data.Wordlist.Schema

/-!
# `Bybee1995`: word forms

Auto-generated from `Linglib/Data/Wordlist/Bybee1995.json` by `scripts/gen_wordlist.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Bybee1995.Wordlist`.
-/

@[expose] public section

namespace Bybee1995.Wordlist

open CLDF.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.string_past : Lexeme :=
  { id := "string_past", languageId := "stan1293", parameterId := "string_past" }

def Lexemes.sting_past : Lexeme :=
  { id := "sting_past", languageId := "stan1293", parameterId := "sting_past" }

def Lexemes.fling_past : Lexeme :=
  { id := "fling_past", languageId := "stan1293", parameterId := "fling_past" }

def Lexemes.hang_past : Lexeme :=
  { id := "hang_past", languageId := "stan1293", parameterId := "hang_past" }

def Lexemes.strike : Lexeme :=
  { id := "strike", languageId := "stan1293", parameterId := "strike" }

def Lexemes.strike_past : Lexeme :=
  { id := "strike_past", languageId := "stan1293", parameterId := "strike_past" }

def Lexemes.sneak : Lexeme :=
  { id := "sneak", languageId := "stan1293", parameterId := "sneak" }

def Lexemes.sneak_past : Lexeme :=
  { id := "sneak_past", languageId := "stan1293", parameterId := "sneak_past" }

def Lexemes.drag : Lexeme :=
  { id := "drag", languageId := "stan1293", parameterId := "drag" }

def Lexemes.drag_past : Lexeme :=
  { id := "drag_past", languageId := "stan1293", parameterId := "drag_past" }

def Lexemes.string : Lexeme :=
  { id := "string", languageId := "stan1293", parameterId := "string" }

def strung : Form Cell :=
  { id := "bybee1995_strung"
    lexeme := Lexemes.string_past
    cell := {}
    form := "strung"
    segments := ["s", "t", "r", "ʌ", "ŋ"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def stung : Form Cell :=
  { id := "bybee1995_stung"
    lexeme := Lexemes.sting_past
    cell := {}
    form := "stung"
    segments := ["s", "t", "ʌ", "ŋ"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def flung : Form Cell :=
  { id := "bybee1995_flung"
    lexeme := Lexemes.fling_past
    cell := {}
    form := "flung"
    segments := ["f", "l", "ʌ", "ŋ"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def hung : Form Cell :=
  { id := "bybee1995_hung"
    lexeme := Lexemes.hang_past
    cell := {}
    form := "hung"
    segments := ["h", "ʌ", "ŋ"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def strike : Form Cell :=
  { id := "bybee1995_strike"
    lexeme := Lexemes.strike
    cell := {}
    form := "strike"
    segments := ["s", "t", "r", "aɪ", "k"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def struck : Form Cell :=
  { id := "bybee1995_struck"
    lexeme := Lexemes.strike_past
    cell := {}
    form := "struck"
    segments := ["s", "t", "r", "ʌ", "k"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def sneak : Form Cell :=
  { id := "bybee1995_sneak"
    lexeme := Lexemes.sneak
    cell := {}
    form := "sneak"
    segments := ["s", "n", "i", "k"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def snuck : Form Cell :=
  { id := "bybee1995_snuck"
    lexeme := Lexemes.sneak_past
    cell := {}
    form := "snuck"
    segments := ["s", "n", "ʌ", "k"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def drag : Form Cell :=
  { id := "bybee1995_drag"
    lexeme := Lexemes.drag
    cell := {}
    form := "drag"
    segments := ["d", "r", "æ", "g"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def drug : Form Cell :=
  { id := "bybee1995_drug"
    lexeme := Lexemes.drag_past
    cell := {}
    form := "drug"
    segments := ["d", "r", "ʌ", "g"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

def string : Form Cell :=
  { id := "bybee1995_string"
    lexeme := Lexemes.string
    cell := {}
    form := "string"
    segments := ["s", "t", "r", "ɪ", "ŋ"]
    source := [
      ⟨"bybee-1995", "2"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.string_past, Lexemes.sting_past, Lexemes.fling_past,
  Lexemes.hang_past, Lexemes.strike, Lexemes.strike_past, Lexemes.sneak, Lexemes.sneak_past,
  Lexemes.drag, Lexemes.drag_past, Lexemes.string]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [strung, stung, flung, hung, strike, struck, sneak, snuck, drag, drug,
  string]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "bybee1995_string_strung", form := string, target := strung, relation := "past",
    source := [
      ⟨"bybee-1995", "2"⟩
    ] },
  { id := "bybee1995_strike_struck", form := strike, target := struck, relation := "past",
    source := [
      ⟨"bybee-1995", "2"⟩
    ] },
  { id := "bybee1995_sneak_snuck", form := sneak, target := snuck, relation := "past", source := [
      ⟨"bybee-1995", "2"⟩
    ] },
  { id := "bybee1995_drag_drug", form := drag, target := drug, relation := "past", source := [
      ⟨"bybee-1995", "2"⟩
    ] }]

end Bybee1995.Wordlist
