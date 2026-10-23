module

public import Linglib.Data.Wordlist.Schema

/-!
# `AfkirZellou2025`: word forms

Auto-generated from `Linglib/Data/Wordlist/AfkirZellou2025.json` by `scripts/gen_wordlist.py`. Do
not edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
AfkirZellou2025.Wordlist`.
-/

@[expose] public section

namespace AfkirZellou2025.Wordlist

open CLDF.Wordlist

/-- The values of `Stem` the source distinguishes. -/
inductive Stem where
  /-- The simple stem, `simple` in the source. -/
  | simple
  /-- The intensive stem, `intensive` in the source. -/
  | intensive
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features and the features UD
lacks. -/
structure Cell extends UD.MorphFeatures where
  /-- The `Stem` feature. -/
  stem : Flat Stem := ⊥
  deriving DecidableEq, Repr

/-- The simple imperative cell, `Mood=Imp|Stem=simple`. -/
def imp : Cell := { mood := ↑UD.Mood.Imp, stem := ↑Stem.simple }

/-- The intensive imperative cell, `Mood=Imp|Stem=intensive`. -/
def imp_intens : Cell := { mood := ↑UD.Mood.Imp, stem := ↑Stem.intensive }

def Lexemes.pull_out : Lexeme :=
  { id := "pull_out", languageId := "tari1263", parameterId := "pull_out", pos := ↑UD.UPOS.VERB }

def Lexemes.work : Lexeme :=
  { id := "work", languageId := "tari1263", parameterId := "work", pos := ↑UD.UPOS.VERB }

def Lexemes.suck_up : Lexeme :=
  { id := "suck_up", languageId := "tari1263", parameterId := "suck_up", pos := ↑UD.UPOS.VERB }

def Lexemes.pick : Lexeme :=
  { id := "pick", languageId := "tari1263", parameterId := "pick", pos := ↑UD.UPOS.VERB }

def Lexemes.understand : Lexeme :=
  { id := "understand", languageId := "tari1263", parameterId := "understand",
    pos := ↑UD.UPOS.VERB }

def Lexemes.move_back : Lexeme :=
  { id := "move_back", languageId := "tari1263", parameterId := "move_back", pos := ↑UD.UPOS.VERB }

def Lexemes.bend_down : Lexeme :=
  { id := "bend_down", languageId := "tari1263", parameterId := "bend_down", pos := ↑UD.UPOS.VERB }

def pull_out_imp : Form Cell :=
  { id := "afkirzellou2025_pull_out_imp"
    lexeme := Lexemes.pull_out
    cell := imp
    form := "ʒβəð"
    segments := ["ʒ", "β", "ə", "ð"]
    source := [
      ⟨"afkir-zellou-2025", "p. 9"⟩
    ] }

def pull_out_imp_intens : Form Cell :=
  { id := "afkirzellou2025_pull_out_imp_intens"
    lexeme := Lexemes.pull_out
    cell := imp_intens
    form := "ʒəb:əð"
    segments := ["ʒ", "ə", "b:", "ə", "ð"]
    source := [
      ⟨"afkir-zellou-2025", "p. 9"⟩
    ] }

def work_imp : Form Cell :=
  { id := "afkirzellou2025_work_imp"
    lexeme := Lexemes.work
    cell := imp
    form := "χðəm"
    segments := ["χ", "ð", "ə", "m"]
    source := [
      ⟨"afkir-zellou-2025", "p. 9"⟩
    ] }

def work_imp_intens : Form Cell :=
  { id := "afkirzellou2025_work_imp_intens"
    lexeme := Lexemes.work
    cell := imp_intens
    form := "χəd:əm"
    segments := ["χ", "ə", "d:", "ə", "m"]
    source := [
      ⟨"afkir-zellou-2025", "p. 9"⟩
    ] }

def suck_up_imp : Form Cell :=
  { id := "afkirzellou2025_suck_up_imp"
    lexeme := Lexemes.suck_up
    cell := imp
    form := "skəf"
    segments := ["s", "k", "ə", "f"]
    source := [
      ⟨"afkir-zellou-2025", "p. 9"⟩
    ] }

def suck_up_imp_intens : Form Cell :=
  { id := "afkirzellou2025_suck_up_imp_intens"
    lexeme := Lexemes.suck_up
    cell := imp_intens
    form := "sək:əf"
    segments := ["s", "ə", "k:", "ə", "f"]
    source := [
      ⟨"afkir-zellou-2025", "p. 9"⟩
    ] }

def pick_imp : Form Cell :=
  { id := "afkirzellou2025_pick_imp"
    lexeme := Lexemes.pick
    cell := imp
    form := "nqəβ"
    segments := ["n", "q", "ə", "β"]
    source := [
      ⟨"afkir-zellou-2025", "p. 9"⟩
    ] }

def pick_imp_intens : Form Cell :=
  { id := "afkirzellou2025_pick_imp_intens"
    lexeme := Lexemes.pick
    cell := imp_intens
    form := "nəq:əβ"
    segments := ["n", "ə", "q:", "ə", "β"]
    source := [
      ⟨"afkir-zellou-2025", "p. 9"⟩
    ] }

def understand_imp_intens : Form Cell :=
  { id := "afkirzellou2025_understand_imp_intens"
    lexeme := Lexemes.understand
    cell := imp_intens
    form := "fəh:əm"
    segments := ["f", "ə", "h:", "ə", "m"]
    source := [
      ⟨"afkir-zellou-2025", "(1)"⟩
    ] }

def move_back_imp_intens : Form Cell :=
  { id := "afkirzellou2025_move_back_imp_intens"
    lexeme := Lexemes.move_back
    cell := imp_intens
    form := "rəħ:əm"
    segments := ["r", "ə", "ħ:", "ə", "m"]
    source := [
      ⟨"afkir-zellou-2025", "(1)"⟩
    ] }

def bend_down_imp : Form Cell :=
  { id := "afkirzellou2025_bend_down_imp"
    lexeme := Lexemes.bend_down
    cell := imp
    form := "χnəs"
    segments := ["χ", "n", "ə", "s"]
    source := [
      ⟨"afkir-zellou-2025", "Table 1"⟩
    ] }

def bend_down_imp_intens : Form Cell :=
  { id := "afkirzellou2025_bend_down_imp_intens"
    lexeme := Lexemes.bend_down
    cell := imp_intens
    form := "ˈχən:s"
    segments := ["χ", "ə", "n:", "s"]
    source := [
      ⟨"afkir-zellou-2025", "Table 1"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.pull_out, Lexemes.work, Lexemes.suck_up, Lexemes.pick,
  Lexemes.understand, Lexemes.move_back, Lexemes.bend_down]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [pull_out_imp, pull_out_imp_intens, work_imp, work_imp_intens,
  suck_up_imp, suck_up_imp_intens, pick_imp, pick_imp_intens, understand_imp_intens,
  move_back_imp_intens, bend_down_imp, bend_down_imp_intens]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

end AfkirZellou2025.Wordlist
