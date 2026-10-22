module

public import Linglib.Data.Wordlist.Schema

/-!
# `Yolyan2025`: word forms

Auto-generated from `Linglib/Data/Wordlist/Yolyan2025.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Yolyan2025.Wordlist`.
-/

@[expose] public section

namespace Yolyan2025.Wordlist

open Data.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.they_will_arrive : Lexeme :=
  { id := "they_will_arrive", languageId := "bemb1257", parameterId := "they_will_arrive" }

def Lexemes.they_will_introduce_him_her : Lexeme :=
  { id := "they_will_introduce_him_her", languageId := "bemb1257",
    parameterId := "they_will_introduce_him_her" }

def Lexemes.they_will_hate : Lexeme :=
  { id := "they_will_hate", languageId := "bemb1257", parameterId := "they_will_hate" }

def Lexemes.they_will_introduce_them : Lexeme :=
  { id := "they_will_introduce_them", languageId := "bemb1257",
    parameterId := "they_will_introduce_them" }

def Lexemes.to_pierce : Lexeme :=
  { id := "to_pierce", languageId := "bemb1257", parameterId := "to_pierce" }

def f_2_11a_1 : Form Cell :=
  { id := "yolyan2025_2_11a_1"
    lexeme := Lexemes.they_will_arrive
    cell := {}
    form := "bá-ká-fík-á"
    segments := ["b", "á", "+", "k", "á", "+", "f", "í", "k", "+", "á"]
    source := [
      ⟨"yolyan-2025", "Example 2.11 (a)"⟩
    ] }

def f_2_11a_2 : Form Cell :=
  { id := "yolyan2025_2_11a_2"
    lexeme := Lexemes.they_will_introduce_him_her
    cell := {}
    form := "bá-ká-mú-lóndólól-á"
    segments := ["b", "á", "+", "k", "á", "+", "m", "ú", "+", "l", "ó", "n", "d", "ó", "l", "ó",
      "l", "+", "á"]
    source := [
      ⟨"yolyan-2025", "Example 2.11 (a)"⟩
    ] }

def f_2_11b_1 : Form Cell :=
  { id := "yolyan2025_2_11b_1"
    lexeme := Lexemes.they_will_hate
    cell := {}
    form := "bá-ká-pát-à kó"
    segments := ["b", "á", "+", "k", "á", "+", "p", "á", "t", "+", "à", "_", "k", "ó"]
    source := [
      ⟨"yolyan-2025", "Example 2.11 (b)"⟩
    ] }

def f_2_11b_2 : Form Cell :=
  { id := "yolyan2025_2_11b_2"
    lexeme := Lexemes.they_will_introduce_them
    cell := {}
    form := "bá-ká-ló-òndòlòl-à kó"
    segments := ["b", "á", "+", "k", "á", "+", "l", "ó", "+", "ò", "n", "d", "ò", "l", "ò", "l",
      "+", "à", "_", "k", "ó"]
    source := [
      ⟨"yolyan-2025", "Example 2.11 (b)"⟩
    ] }

def f_2_11c : Form Cell :=
  { id := "yolyan2025_2_11c"
    lexeme := Lexemes.to_pierce
    cell := {}
    form := "ù-kù-tùl-à"
    segments := ["ù", "+", "k", "ù", "+", "t", "ù", "l", "+", "à"]
    source := [
      ⟨"yolyan-2025", "Example 2.11 (c)"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Underlying` column. -/
  underlying : String
  deriving DecidableEq, Repr

def f_2_11a_1.analysis : Analysis :=
  { form := f_2_11a_1,
    underlying := "/bá-ka-fik-a/" }

def f_2_11a_2.analysis : Analysis :=
  { form := f_2_11a_2,
    underlying := "/bá-ka-mu-londolol-a/" }

def f_2_11b_1.analysis : Analysis :=
  { form := f_2_11b_1,
    underlying := "/bá-ka-pat-a kó/" }

def f_2_11b_2.analysis : Analysis :=
  { form := f_2_11b_2,
    underlying := "/bá-ka-londolol-a kó/" }

def f_2_11c.analysis : Analysis :=
  { form := f_2_11c,
    underlying := "/u-ku-tul-a/" }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.they_will_arrive, Lexemes.they_will_introduce_him_her,
  Lexemes.they_will_hate, Lexemes.they_will_introduce_them, Lexemes.to_pierce]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [f_2_11a_1, f_2_11a_2, f_2_11b_1, f_2_11b_2, f_2_11c]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every analysis of the data. -/
def analyses : List Analysis := [f_2_11a_1.analysis, f_2_11a_2.analysis, f_2_11b_1.analysis,
  f_2_11b_2.analysis, f_2_11c.analysis]

end Yolyan2025.Wordlist
