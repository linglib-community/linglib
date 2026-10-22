module

public import Linglib.Data.Wordlist.Schema

/-!
# `Svenonius2004`: word forms

Auto-generated from `Linglib/Data/Wordlist/Svenonius2004.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
Svenonius2004.Wordlist`.
-/

@[expose] public section

namespace Svenonius2004.Wordlist

open CLDF.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

/-- The infinitive cell, `VerbForm=Inf`. -/
def inf : Cell := { verbForm := ↑UD.VerbForm.Inf }

/-- The 1sg.prs cell, `Tense=Pres|Number=Sing|Person=1`. -/
def prs_1sg : Cell :=
  { tense := ↑UD.Tense.Pres, number := ↑UD.Number.Sing, person := ↑UD.Person.first }

/-- The past cell, `Tense=Past`. -/
def pst : Cell := { tense := ↑UD.Tense.Past }

/-- The pst.pl cell, `Tense=Past|Number=Plur`. -/
def pst_pl : Cell := { tense := ↑UD.Tense.Past, number := ↑UD.Number.Plur }

def Lexemes.zabrosil_throw_into : Lexeme :=
  { id := "zabrosil_throw_into", languageId := "russ1263", parameterId := "throw_into",
    pos := ↑UD.UPOS.VERB }

def Lexemes.zabrosil_give_up : Lexeme :=
  { id := "zabrosil_give_up", languageId := "russ1263", parameterId := "give_up",
    pos := ↑UD.UPOS.VERB }

def Lexemes.zabrosal_begin_to_throw : Lexeme :=
  { id := "zabrosal_begin_to_throw", languageId := "russ1263", parameterId := "begin_to_throw",
    pos := ↑UD.UPOS.VERB }

def Lexemes.povybrasyvatj : Lexeme :=
  { id := "povybrasyvatj", languageId := "russ1263", parameterId := "throw_out_one_by_one",
    pos := ↑UD.UPOS.VERB }

def Lexemes.powchodzili : Lexeme :=
  { id := "powchodzili", languageId := "poli1260", parameterId := "walk_in_one_by_one",
    pos := ↑UD.UPOS.VERB }

def Lexemes.ponarazkaza : Lexeme :=
  { id := "ponarazkaza", languageId := "bulg1262", parameterId := "tell_a_little_of_many",
    pos := ↑UD.UPOS.VERB }

def Lexemes.izponaprerazkaza : Lexeme :=
  { id := "izponaprerazkaza", languageId := "bulg1262",
    parameterId := "renarrate_completely_one_by_one_of_many", pos := ↑UD.UPOS.VERB }

def Lexemes.zakuritj : Lexeme :=
  { id := "zakuritj", languageId := "russ1263", parameterId := "start_smoking",
    pos := ↑UD.UPOS.VERB }

def Lexemes.pocitatj : Lexeme :=
  { id := "pocitatj", languageId := "russ1263", parameterId := "read_for_a_little_while",
    pos := ↑UD.UPOS.VERB }

def f_1a : Form Cell :=
  { id := "svenonius2004_1a"
    lexeme := Lexemes.zabrosil_throw_into
    cell := pst
    form := "zabrosil"
    morphs := ["za", "brosil"]
    source := [
      ⟨"svenonius-2004", "(1a)"⟩
    ] }

def f_1b : Form Cell :=
  { id := "svenonius2004_1b"
    lexeme := Lexemes.zabrosil_give_up
    cell := pst
    form := "zabrosil"
    morphs := ["za", "brosil"]
    source := [
      ⟨"svenonius-2004", "(1b)"⟩
    ] }

def f_1c : Form Cell :=
  { id := "svenonius2004_1c"
    lexeme := Lexemes.zabrosal_begin_to_throw
    cell := pst
    form := "zabrosal"
    morphs := ["za", "brosal"]
    source := [
      ⟨"svenonius-2004", "(1c)"⟩
    ] }

def f_4a : Form Cell :=
  { id := "svenonius2004_4a"
    lexeme := Lexemes.povybrasyvatj
    cell := inf
    form := "povybrasyvatj"
    morphs := ["po", "vy", "brasyvatj"]
    source := [
      ⟨"svenonius-2004", "(4a)"⟩
    ] }

def f_4b : Form Cell :=
  { id := "svenonius2004_4b"
    lexeme := Lexemes.povybrasyvatj
    cell := inf
    form := "vypobrasyvatj"
    morphs := ["vy", "po", "brasyvatj"]
    judgment := .ungrammatical
    source := [
      ⟨"svenonius-2004", "(4b)"⟩
    ] }

def f_4c : Form Cell :=
  { id := "svenonius2004_4c"
    lexeme := Lexemes.powchodzili
    cell := pst_pl
    form := "powchodzili"
    morphs := ["po", "w", "chodzili"]
    source := [
      ⟨"svenonius-2004", "(4c)"⟩
    ] }

def f_4d : Form Cell :=
  { id := "svenonius2004_4d"
    lexeme := Lexemes.powchodzili
    cell := pst_pl
    form := "wpochodzili"
    morphs := ["w", "po", "chodzili"]
    judgment := .ungrammatical
    source := [
      ⟨"svenonius-2004", "(4d)"⟩
    ] }

def f_3a : Form Cell :=
  { id := "svenonius2004_3a"
    lexeme := Lexemes.ponarazkaza
    cell := prs_1sg
    form := "ponarazkaža"
    morphs := ["po", "na", "razkaža"]
    source := [
      ⟨"istratkova-2004", "Table 1"⟩,
      ⟨"svenonius-2004", "(3a)"⟩
    ] }

def f_3e : Form Cell :=
  { id := "svenonius2004_3e"
    lexeme := Lexemes.izponaprerazkaza
    cell := prs_1sg
    form := "izponaprerazkaža"
    morphs := ["iz", "po", "na", "pre", "razkaža"]
    source := [
      ⟨"istratkova-2004", "Table 1"⟩,
      ⟨"svenonius-2004", "(3e)"⟩
    ] }

def f_58za : Form Cell :=
  { id := "svenonius2004_58za"
    lexeme := Lexemes.zakuritj
    cell := inf
    form := "zakuritj"
    morphs := ["za", "kuritj"]
    source := [
      ⟨"svenonius-2004", "§4.1 (58) discussion"⟩
    ] }

def f_58za_alt : Form Cell :=
  { id := "svenonius2004_58za_alt"
    lexeme := Lexemes.zakuritj
    cell := inf
    form := "zakurivatj"
    morphs := ["za", "kurivatj"]
    judgment := .ungrammatical
    source := [
      ⟨"svenonius-2004", "§4.1 (58) discussion"⟩
    ] }

def f_58po : Form Cell :=
  { id := "svenonius2004_58po"
    lexeme := Lexemes.pocitatj
    cell := inf
    form := "počitatj"
    morphs := ["po", "čitatj"]
    source := [
      ⟨"svenonius-2004", "§4.1 (58) discussion"⟩
    ] }

def f_58po_alt : Form Cell :=
  { id := "svenonius2004_58po_alt"
    lexeme := Lexemes.pocitatj
    cell := inf
    form := "počityvatj"
    morphs := ["po", "čityvatj"]
    source := [
      ⟨"svenonius-2004", "§4.1 (58) discussion"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.zabrosil_throw_into, Lexemes.zabrosil_give_up,
  Lexemes.zabrosal_begin_to_throw, Lexemes.povybrasyvatj, Lexemes.powchodzili, Lexemes.ponarazkaza,
  Lexemes.izponaprerazkaza, Lexemes.zakuritj, Lexemes.pocitatj]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [f_1a, f_1b, f_1c, f_4a, f_4c, f_3a, f_3e, f_58za, f_58po, f_58po_alt]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := [f_4b, f_4d, f_58za_alt]

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := [
  { id := "svenonius2004_r_58za_alt_imperfective", form := f_58za, target := f_58za_alt,
    relation := "imperfective", source := [
      ⟨"svenonius-2004", "§4.1 (58) discussion"⟩
    ] },
  { id := "svenonius2004_r_58po_alt_imperfective", form := f_58po, target := f_58po_alt,
    relation := "imperfective", source := [
      ⟨"svenonius-2004", "§4.1 (58) discussion"⟩
    ] }]

end Svenonius2004.Wordlist
