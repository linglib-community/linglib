module

public import Linglib.Data.Wordlist.Schema

/-!
# `ArregiPietraszko2021`: word forms

Auto-generated from `Linglib/Data/Wordlist/ArregiPietraszko2021.json` by `scripts/gen_wordlist.py`.
Do not edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
ArregiPietraszko2021.Wordlist`.
-/

@[expose] public section

namespace ArregiPietraszko2021.Wordlist

open CLDF.Wordlist

/-- The values of `Verb` the source distinguishes. -/
inductive Verb where
  /-- Dummy do, `dummy` in the source. -/
  | dummy
  /-- An auxiliary, `auxiliary` in the source. -/
  | auxiliary
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.rel_cl1 : Lexeme :=
  { id := "rel_cl1", languageId := "nort2795", parameterId := "rel_cl1" }

def Lexemes.rel_cl9 : Lexeme :=
  { id := "rel_cl9", languageId := "nort2795", parameterId := "rel_cl9" }

def Lexemes.rel_cl7 : Lexeme :=
  { id := "rel_cl7", languageId := "nort2795", parameterId := "rel_cl7" }

def Lexemes.rel_cl11 : Lexeme :=
  { id := "rel_cl11", languageId := "nort2795", parameterId := "rel_cl11" }

def Lexemes.do_3sg_neg : Lexeme :=
  { id := "do_3sg_neg", languageId := "stan1293", parameterId := "do_3sg_neg" }

def Lexemes.have_pst_neg : Lexeme :=
  { id := "have_pst_neg", languageId := "stan1293", parameterId := "have_pst_neg" }

def f_19_cl1 : Form Cell :=
  { id := "arregipietraszko2021_19_cl1"
    lexeme := Lexemes.rel_cl1
    cell := {}
    form := "o"
    segments := ["o"]
    source := [
      ⟨"arregi-pietraszko-2021", "(19)"⟩
    ] }

def f_19_cl9 : Form Cell :=
  { id := "arregipietraszko2021_19_cl9"
    lexeme := Lexemes.rel_cl9
    cell := {}
    form := "e"
    segments := ["e"]
    source := [
      ⟨"arregi-pietraszko-2021", "(19)"⟩
    ] }

def f_19_cl7 : Form Cell :=
  { id := "arregipietraszko2021_19_cl7"
    lexeme := Lexemes.rel_cl7
    cell := {}
    form := "esi"
    segments := ["e", "s", "i"]
    source := [
      ⟨"arregi-pietraszko-2021", "(19)"⟩
    ] }

def f_19_cl11 : Form Cell :=
  { id := "arregipietraszko2021_19_cl11"
    lexeme := Lexemes.rel_cl11
    cell := {}
    form := "olu"
    segments := ["o", "l", "u"]
    source := [
      ⟨"arregi-pietraszko-2021", "(19)"⟩
    ] }

def doesnt : Form Cell :=
  { id := "arregipietraszko2021_doesnt"
    lexeme := Lexemes.do_3sg_neg
    cell := {}
    form := "doesn't"
    segments := ["doe", "s", "n't"]
    source := [
      ⟨"arregi-pietraszko-2021", "p. 264"⟩
    ] }

def hadnt : Form Cell :=
  { id := "arregipietraszko2021_hadnt"
    lexeme := Lexemes.have_pst_neg
    cell := {}
    form := "hadn't"
    segments := ["ha", "d", "n't"]
    source := [
      ⟨"arregi-pietraszko-2021", "p. 264"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Lnk` column. -/
  lnk : Option String := none
  /-- The `D` column. -/
  d : Option String := none
  /-- The `T` column. -/
  t : Option String := none
  /-- The `Verb` column. -/
  verb : Option Verb := none
  deriving DecidableEq, Repr

def f_19_cl1.analysis : Analysis :=
  { form := f_19_cl1,
    lnk := some "a",
    d := some "u",
    t := some "u" }

def f_19_cl9.analysis : Analysis :=
  { form := f_19_cl9,
    lnk := some "a",
    d := some "i",
    t := some "i" }

def f_19_cl7.analysis : Analysis :=
  { form := f_19_cl7,
    lnk := some "a",
    d := some "i",
    t := some "si" }

def f_19_cl11.analysis : Analysis :=
  { form := f_19_cl11,
    lnk := some "a",
    d := some "u",
    t := some "lu" }

def doesnt.analysis : Analysis :=
  { form := doesnt,
    verb := some Verb.dummy }

def hadnt.analysis : Analysis :=
  { form := hadnt,
    verb := some Verb.auxiliary }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.rel_cl1, Lexemes.rel_cl9, Lexemes.rel_cl7, Lexemes.rel_cl11,
  Lexemes.do_3sg_neg, Lexemes.have_pst_neg]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [f_19_cl1, f_19_cl9, f_19_cl7, f_19_cl11, doesnt, hadnt]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every analysis of the data. -/
def analyses : List Analysis := [f_19_cl1.analysis, f_19_cl9.analysis, f_19_cl7.analysis,
  f_19_cl11.analysis, doesnt.analysis, hadnt.analysis]

end ArregiPietraszko2021.Wordlist
