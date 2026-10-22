module

public import Linglib.Data.Wordlist.Schema

/-!
# `HeinzLai2013`: word forms

Auto-generated from `Linglib/Data/Wordlist/HeinzLai2013.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
HeinzLai2013.Wordlist`.
-/

@[expose] public section

namespace HeinzLai2013.Wordlist

open Data.Wordlist

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.rope_gen : Lexeme :=
  { id := "rope_gen", languageId := "nucl1301", parameterId := "rope_gen" }

def Lexemes.hand_gen : Lexeme :=
  { id := "hand_gen", languageId := "nucl1301", parameterId := "hand_gen" }

def Lexemes.end_gen : Lexeme :=
  { id := "end_gen", languageId := "nucl1301", parameterId := "end_gen" }

def Lexemes.stamp_gen : Lexeme :=
  { id := "stamp_gen", languageId := "nucl1301", parameterId := "stamp_gen" }

def ipin : Form Cell :=
  { id := "heinzlai2013_ipin"
    lexeme := Lexemes.rope_gen
    cell := {}
    form := "ipin"
    segments := ["i", "p", "i", "n"]
    source := [
      ⟨"heinz-lai-2013", "Table 1a"⟩,
      ⟨"heinz-lai-2013", "Table 2a"⟩
    ] }

def elin : Form Cell :=
  { id := "heinzlai2013_elin"
    lexeme := Lexemes.hand_gen
    cell := {}
    form := "elin"
    segments := ["e", "l", "i", "n"]
    source := [
      ⟨"heinz-lai-2013", "Table 1b"⟩,
      ⟨"heinz-lai-2013", "Table 2a"⟩
    ] }

def sonun : Form Cell :=
  { id := "heinzlai2013_sonun"
    lexeme := Lexemes.end_gen
    cell := {}
    form := "sonun"
    segments := ["s", "o", "n", "u", "n"]
    source := [
      ⟨"heinz-lai-2013", "Table 1c"⟩,
      ⟨"heinz-lai-2013", "Table 2a"⟩
    ] }

def pulun : Form Cell :=
  { id := "heinzlai2013_pulun"
    lexeme := Lexemes.stamp_gen
    cell := {}
    form := "pulun"
    segments := ["p", "u", "l", "u", "n"]
    source := [
      ⟨"heinz-lai-2013", "Table 1d"⟩,
      ⟨"heinz-lai-2013", "Table 2a"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Underlying` column. -/
  underlying : String
  deriving DecidableEq, Repr

def ipin.analysis : Analysis :=
  { form := ipin,
    underlying := "/ip-un/" }

def elin.analysis : Analysis :=
  { form := elin,
    underlying := "/el-un/" }

def sonun.analysis : Analysis :=
  { form := sonun,
    underlying := "/son-un/" }

def pulun.analysis : Analysis :=
  { form := pulun,
    underlying := "/pul-un/" }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.rope_gen, Lexemes.hand_gen, Lexemes.end_gen,
  Lexemes.stamp_gen]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [ipin, elin, sonun, pulun]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every analysis of the data. -/
def analyses : List Analysis := [ipin.analysis, elin.analysis, sonun.analysis, pulun.analysis]

end HeinzLai2013.Wordlist
