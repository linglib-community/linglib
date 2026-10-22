module

public import Linglib.Data.Wordlist.Schema

/-!
# `Vago2017`: word forms

Auto-generated from `Linglib/Data/Wordlist/Vago2017.json` by `scripts/gen_wordlist.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace Vago2017.Wordlist`.
-/

@[expose] public section

namespace Vago2017.Wordlist

open Data.Wordlist

/-- The values of `Kind` the source distinguishes. -/
inductive Kind where
  /-- A root, `root` in the source. -/
  | root
  /-- A suffix, `suffix` in the source. -/
  | suffix
  deriving DecidableEq, Repr

/-- The values of `Deleted` the source distinguishes. -/
inductive Deleted where
  /-- Neither vowel, `none` in the source. -/
  | neither
  /-- The first vowel, `first` in the source. -/
  | first
  /-- The second vowel, `second` in the source. -/
  | second
  deriving DecidableEq, Repr

/-- The values of `Hierarchy` the source distinguishes. -/
inductive Hierarchy where
  /-- The regular hierarchy, `regular` in the source. -/
  | regular
  /-- The hierarchy deleting the first vowel, `v1Deletion` in the source. -/
  | v1Deletion
  /-- The hierarchy deleting neither vowel, `noDeletion` in the source. -/
  | noDeletion
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features. -/
abbrev Cell := UD.MorphFeatures

def Lexemes.our_barrel : Lexeme :=
  { id := "our_barrel", languageId := "hung1274", parameterId := "our_barrel" }

def Lexemes.forester : Lexeme :=
  { id := "forester", languageId := "hung1274", parameterId := "forester" }

def Lexemes.in_esperanto : Lexeme :=
  { id := "in_esperanto", languageId := "hung1274", parameterId := "in_esperanto" }

def Lexemes.we_have_to_study : Lexeme :=
  { id := "we_have_to_study", languageId := "hung1274", parameterId := "we_have_to_study" }

def Lexemes.we_would_bring : Lexeme :=
  { id := "we_would_bring", languageId := "hung1274", parameterId := "we_would_bring" }

def Lexemes.on_his_gate : Lexeme :=
  { id := "on_his_gate", languageId := "hung1274", parameterId := "on_his_gate" }

def Lexemes.our_gates : Lexeme :=
  { id := "our_gates", languageId := "hung1274", parameterId := "our_gates" }

def Lexemes.our_detective : Lexeme :=
  { id := "our_detective", languageId := "hung1274", parameterId := "our_detective" }

def hordonk : Form Cell :=
  { id := "vago2017_hordonk"
    lexeme := Lexemes.our_barrel
    cell := {}
    form := "hordónk"
    segments := ["h", "o", "r", "d", "ó", "n", "k"]
    source := [
      ⟨"vago-2017", "Table 1"⟩
    ] }

def erdesz : Form Cell :=
  { id := "vago2017_erdesz"
    lexeme := Lexemes.forester
    cell := {}
    form := "erdész"
    segments := ["e", "r", "d", "é", "sz"]
    source := [
      ⟨"vago-2017", "(7a), Table 2"⟩
    ] }

def eszperantoul : Form Cell :=
  { id := "vago2017_eszperantoul"
    lexeme := Lexemes.in_esperanto
    cell := {}
    form := "eszperantóul"
    segments := ["e", "sz", "p", "e", "r", "a", "n", "t", "ó", "u", "l"]
    source := [
      ⟨"vago-2017", "Table 3"⟩
    ] }

def tanulnunk : Form Cell :=
  { id := "vago2017_tanulnunk"
    lexeme := Lexemes.we_have_to_study
    cell := {}
    form := "tanulnunk"
    segments := ["t", "a", "n", "u", "l", "n", "u", "n", "k"]
    source := [
      ⟨"vago-2017", "(20c), Table 4"⟩
    ] }

def hoznank : Form Cell :=
  { id := "vago2017_hoznank"
    lexeme := Lexemes.we_would_bring
    cell := {}
    form := "hoznánk"
    segments := ["h", "o", "z", "n", "á", "n", "k"]
    source := [
      ⟨"vago-2017", "(17), (21a)"⟩
    ] }

def kapujan : Form Cell :=
  { id := "vago2017_kapujan"
    lexeme := Lexemes.on_his_gate
    cell := {}
    form := "kapuján"
    segments := ["k", "a", "p", "u", "j", "á", "n"]
    source := [
      ⟨"vago-2017", "(18a), (21b)"⟩
    ] }

def kapuink : Form Cell :=
  { id := "vago2017_kapuink"
    lexeme := Lexemes.our_gates
    cell := {}
    form := "kapuink"
    segments := ["k", "a", "p", "u", "i", "n", "k"]
    source := [
      ⟨"vago-2017", "(18b), (23a)"⟩
    ] }

def nyomozonk : Form Cell :=
  { id := "vago2017_nyomozonk"
    lexeme := Lexemes.our_detective
    cell := {}
    form := "nyomozónk"
    segments := ["ny", "o", "m", "o", "z", "ó", "n", "k"]
    source := [
      ⟨"vago-2017", "(19), (23b)"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Left` column. -/
  left : String
  /-- The `LeftKind` column. -/
  leftKind : Kind
  /-- The `Right` column. -/
  right : String
  /-- The `RightKind` column. -/
  rightKind : Kind
  /-- The `Before` column. -/
  before : Option String := none
  /-- The `BeforeKind` column. -/
  beforeKind : Option Kind := none
  /-- The `Deleted` column. -/
  deleted : Deleted
  /-- The `Hierarchy` column. -/
  hierarchy : Hierarchy
  deriving DecidableEq, Repr

def hordonk.analysis : Analysis :=
  { form := hordonk,
    left := "hordó",
    leftKind := Kind.root,
    right := "unk",
    rightKind := Kind.suffix,
    deleted := Deleted.second,
    hierarchy := Hierarchy.regular }

def erdesz.analysis : Analysis :=
  { form := erdesz,
    left := "erdő",
    leftKind := Kind.root,
    right := "ész",
    rightKind := Kind.suffix,
    deleted := Deleted.first,
    hierarchy := Hierarchy.v1Deletion }

def eszperantoul.analysis : Analysis :=
  { form := eszperantoul,
    left := "eszperantó",
    leftKind := Kind.root,
    right := "ul",
    rightKind := Kind.suffix,
    deleted := Deleted.neither,
    hierarchy := Hierarchy.noDeletion }

def tanulnunk.analysis : Analysis :=
  { form := tanulnunk,
    left := "ni",
    leftKind := Kind.suffix,
    right := "unk",
    rightKind := Kind.suffix,
    before := some "tanul",
    beforeKind := some Kind.root,
    deleted := Deleted.first,
    hierarchy := Hierarchy.v1Deletion }

def hoznank.analysis : Analysis :=
  { form := hoznank,
    left := "ná",
    leftKind := Kind.suffix,
    right := "unk",
    rightKind := Kind.suffix,
    before := some "hoz",
    beforeKind := some Kind.root,
    deleted := Deleted.second,
    hierarchy := Hierarchy.regular }

def kapujan.analysis : Analysis :=
  { form := kapujan,
    left := "já",
    leftKind := Kind.suffix,
    right := "on",
    rightKind := Kind.suffix,
    before := some "kapu",
    beforeKind := some Kind.root,
    deleted := Deleted.second,
    hierarchy := Hierarchy.regular }

def kapuink.analysis : Analysis :=
  { form := kapuink,
    left := "i",
    leftKind := Kind.suffix,
    right := "unk",
    rightKind := Kind.suffix,
    before := some "kapu",
    beforeKind := some Kind.root,
    deleted := Deleted.second,
    hierarchy := Hierarchy.regular }

def nyomozonk.analysis : Analysis :=
  { form := nyomozonk,
    left := "ó",
    leftKind := Kind.suffix,
    right := "unk",
    rightKind := Kind.suffix,
    before := some "nyomoz",
    beforeKind := some Kind.root,
    deleted := Deleted.second,
    hierarchy := Hierarchy.regular }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.our_barrel, Lexemes.forester, Lexemes.in_esperanto,
  Lexemes.we_have_to_study, Lexemes.we_would_bring, Lexemes.on_his_gate, Lexemes.our_gates,
  Lexemes.our_detective]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [hordonk, erdesz, eszperantoul, tanulnunk, hoznank, kapujan, kapuink,
  nyomozonk]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every analysis of the data. -/
def analyses : List Analysis := [hordonk.analysis, erdesz.analysis, eszperantoul.analysis,
  tanulnunk.analysis, hoznank.analysis, kapujan.analysis, kapuink.analysis, nyomozonk.analysis]

end Vago2017.Wordlist
