module

public import Linglib.Data.Forms.Schema

/-!
# `Brodkin2026`: word forms

Auto-generated from `Linglib/Data/Forms/Brodkin2026.json` by `scripts/gen_forms.py`. Do not edit by
hand; edit the JSON and re-run the generator. Declarations live in `namespace Brodkin2026.Forms`.
-/

@[expose] public section

namespace Brodkin2026.Forms

open Data.Forms

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.this_in_hand : Lexeme :=
  { id := "this_in_hand", languageId := "mand1442", parameterId := "this_in_hand" }

def Lexemes.this : Lexeme :=
  { id := "this", languageId := "mand1442", parameterId := "this" }

def Lexemes.that : Lexeme :=
  { id := "that", languageId := "mand1442", parameterId := "that" }

def Lexemes.neg : Lexeme :=
  { id := "neg", languageId := "mand1442", parameterId := "neg" }

def Lexemes.what : Lexeme :=
  { id := "what", languageId := "mand1442", parameterId := "what" }

def Lexemes.which : Lexeme :=
  { id := "which", languageId := "mand1442", parameterId := "which" }

def Lexemes.who : Lexeme :=
  { id := "who", languageId := "mand1442", parameterId := "who" }

def this_in_hand_short : Form Cell :=
  { id := "brodkin2026_this_in_hand_short"
    lexeme := Lexemes.this_in_hand
    cell := {}
    form := "ndi"
    segments := ["n", "d", "i"]
    source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] }

def this_in_hand_long : Form Cell :=
  { id := "brodkin2026_this_in_hand_long"
    lexeme := Lexemes.this_in_hand
    cell := {}
    form := "indi"
    segments := ["i", "n", "d", "i"]
    source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] }

def this_short : Form Cell :=
  { id := "brodkin2026_this_short"
    lexeme := Lexemes.this
    cell := {}
    form := "de"
    segments := ["d", "e"]
    source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] }

def this_long : Form Cell :=
  { id := "brodkin2026_this_long"
    lexeme := Lexemes.this
    cell := {}
    form := "diʔe"
    segments := ["d", "i", "ʔ", "e"]
    source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] }

def that_short : Form Cell :=
  { id := "brodkin2026_that_short"
    lexeme := Lexemes.that
    cell := {}
    form := "do"
    segments := ["d", "o"]
    source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] }

def that_long : Form Cell :=
  { id := "brodkin2026_that_long"
    lexeme := Lexemes.that
    cell := {}
    form := "diʔo"
    segments := ["d", "i", "ʔ", "o"]
    source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] }

def neg_short : Form Cell :=
  { id := "brodkin2026_neg_short"
    lexeme := Lexemes.neg
    cell := {}
    form := "ndaŋ"
    segments := ["n", "d", "a", "ŋ"]
    source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] }

def neg_long : Form Cell :=
  { id := "brodkin2026_neg_long"
    lexeme := Lexemes.neg
    cell := {}
    form := "andiaŋ"
    segments := ["a", "n", "d", "i", "a", "ŋ"]
    source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] }

def what_short : Form Cell :=
  { id := "brodkin2026_what_short"
    lexeme := Lexemes.what
    cell := {}
    form := "a"
    segments := ["a"]
    source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] }

def what_long : Form Cell :=
  { id := "brodkin2026_what_long"
    lexeme := Lexemes.what
    cell := {}
    form := "apa"
    segments := ["a", "p", "a"]
    source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] }

def which_short : Form Cell :=
  { id := "brodkin2026_which_short"
    lexeme := Lexemes.which
    cell := {}
    form := "na"
    segments := ["n", "a"]
    source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] }

def which_long : Form Cell :=
  { id := "brodkin2026_which_long"
    lexeme := Lexemes.which
    cell := {}
    form := "inna"
    segments := ["i", "n", "n", "a"]
    source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] }

def who_short : Form Cell :=
  { id := "brodkin2026_who_short"
    lexeme := Lexemes.who
    cell := {}
    form := "ne"
    segments := ["n", "e"]
    source := [
      ⟨"brodkin-2026", "(42a)"⟩
    ] }

def who_long : Form Cell :=
  { id := "brodkin2026_who_long"
    lexeme := Lexemes.who
    cell := {}
    form := "inne"
    segments := ["i", "n", "n", "e"]
    source := [
      ⟨"brodkin-2026", "(42b)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.this_in_hand, Lexemes.this, Lexemes.that, Lexemes.neg,
  Lexemes.what, Lexemes.which, Lexemes.who]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [this_in_hand_short, this_in_hand_long, this_short, this_long,
  that_short, that_long, neg_short, neg_long, what_short, what_long, which_short, which_long,
  who_short, who_long]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "brodkin2026_this_in_hand", form := this_in_hand_short, target := this_in_hand_long,
    relation := "top-down suppletion", source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] },
  { id := "brodkin2026_this", form := this_short, target := this_long,
    relation := "top-down suppletion", source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] },
  { id := "brodkin2026_that", form := that_short, target := that_long,
    relation := "top-down suppletion", source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] },
  { id := "brodkin2026_neg", form := neg_short, target := neg_long,
    relation := "top-down suppletion", source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] },
  { id := "brodkin2026_what", form := what_short, target := what_long,
    relation := "top-down suppletion", source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] },
  { id := "brodkin2026_which", form := which_short, target := which_long,
    relation := "top-down suppletion", source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] },
  { id := "brodkin2026_who", form := who_short, target := who_long,
    relation := "top-down suppletion", source := [
      ⟨"brodkin-2026", "(44)"⟩
    ] }]

end Brodkin2026.Forms
