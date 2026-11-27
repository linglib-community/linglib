module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Middleton2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Middleton2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Middleton2026.Examples`.
-/

@[expose] public section

namespace Middleton2026.Examples

def ex_7a : Datum :=
  { id := "middleton2026_7a"
    source := ⟨"kontak-kunkel-1987", "p. 12"⟩
    reportedIn := some ⟨"middleton-2026", "(7a)"⟩
    method := some .description
    language := "nort1550"
    primaryText := "o-sú-mû-ya"
    glossedTokens := [("o-sú-mû-ya", "1S.2S-CERT-see-FUT")]
    glossedWords := [⟨['o', '-', 's', 'ú', '-', 'm', 'û', '-', 'y', 'a'], ['1', 'S', '.', '2', 'S', '-', 'C', 'E', 'R', 'T', '-', 's', 'e', 'e', '-', 'F', 'U', 'T'], [⟨['o'], ['1', 'S', '.', '2', 'S'], none⟩, ⟨['s', 'ú'], ['C', 'E', 'R', 'T'], some '-'⟩, ⟨['m', 'û'], ['s', 'e', 'e'], some '-'⟩, ⟨['y', 'a'], ['F', 'U', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_7b : Datum :=
  { id := "middleton2026_7b"
    source := ⟨"kontak-kunkel-1987", "p. 12"⟩
    reportedIn := some ⟨"middleton-2026", "(7b)"⟩
    method := some .description
    language := "nort1550"
    primaryText := "mopén-sú-mû-ya"
    glossedTokens := [("mopén-sú-mû-ya", "1S.2D-CERT-see-FUT")]
    glossedWords := [⟨['m', 'o', 'p', 'é', 'n', '-', 's', 'ú', '-', 'm', 'û', '-', 'y', 'a'], ['1', 'S', '.', '2', 'D', '-', 'C', 'E', 'R', 'T', '-', 's', 'e', 'e', '-', 'F', 'U', 'T'], [⟨['m', 'o', 'p', 'é', 'n'], ['1', 'S', '.', '2', 'D'], none⟩, ⟨['s', 'ú'], ['C', 'E', 'R', 'T'], some '-'⟩, ⟨['m', 'û'], ['s', 'e', 'e'], some '-'⟩, ⟨['y', 'a'], ['F', 'U', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_7c : Datum :=
  { id := "middleton2026_7c"
    source := ⟨"kontak-kunkel-1987", "p. 12"⟩
    reportedIn := some ⟨"middleton-2026", "(7c)"⟩
    method := some .description
    language := "nort1550"
    primaryText := "mopí-sú-mû-ya"
    glossedTokens := [("mopí-sú-mû-ya", "1S.2I-CERT-see-FUT")]
    glossedWords := [⟨['m', 'o', 'p', 'í', '-', 's', 'ú', '-', 'm', 'û', '-', 'y', 'a'], ['1', 'S', '.', '2', 'I', '-', 'C', 'E', 'R', 'T', '-', 's', 'e', 'e', '-', 'F', 'U', 'T'], [⟨['m', 'o', 'p', 'í'], ['1', 'S', '.', '2', 'I'], none⟩, ⟨['s', 'ú'], ['C', 'E', 'R', 'T'], some '-'⟩, ⟨['m', 'û'], ['s', 'e', 'e'], some '-'⟩, ⟨['y', 'a'], ['F', 'U', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_17b : Datum :=
  { id := "middleton2026_17b"
    source := ⟨"middleton-2026", "(17b)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Su-k gu-∅ ikus-i d-endu-s-n."
    glossedTokens := [("Su-k", "2S-ERG"), ("gu-∅", "1P-ABS"), ("ikus-i", "see-PRF"), ("d-endu-s-n", "L-PAST.1P.ABS-2S.ERG-CPST")]
    glossedWords := [⟨['S', 'u', '-', 'k'], ['2', 'S', '-', 'E', 'R', 'G'], [⟨['S', 'u'], ['2', 'S'], none⟩, ⟨['k'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['g', 'u', '-', '∅'], ['1', 'P', '-', 'A', 'B', 'S'], [⟨['g', 'u'], ['1', 'P'], none⟩, ⟨['∅'], ['A', 'B', 'S'], some '-'⟩]⟩, ⟨['i', 'k', 'u', 's', '-', 'i'], ['s', 'e', 'e', '-', 'P', 'R', 'F'], [⟨['i', 'k', 'u', 's'], ['s', 'e', 'e'], none⟩, ⟨['i'], ['P', 'R', 'F'], some '-'⟩]⟩, ⟨['d', '-', 'e', 'n', 'd', 'u', '-', 's', '-', 'n'], ['L', '-', 'P', 'A', 'S', 'T', '.', '1', 'P', '.', 'A', 'B', 'S', '-', '2', 'S', '.', 'E', 'R', 'G', '-', 'C', 'P', 'S', 'T'], [⟨['d'], ['L'], none⟩, ⟨['e', 'n', 'd', 'u'], ['P', 'A', 'S', 'T', '.', '1', 'P', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['s'], ['2', 'S', '.', 'E', 'R', 'G'], some '-'⟩, ⟨['n'], ['C', 'P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("variety", "ondarru"), ("arguments", "erg2sgAbs1pl")] }

def ex_19b : Datum :=
  { id := "middleton2026_19b"
    source := ⟨"middleton-2026", "(19b)"⟩
    reportedIn := none
    language := "basq1248"
    primaryText := "Gu-k atzo lagun-du u-a-tzu-e-n estasiño-ra."
    glossedTokens := [("Gu-k", "1P-ERG"), ("atzo", "yesterday"), ("lagun-du", "accompany-PRF"), ("u-a-tzu-e-n", "2P.ERG-PAST.3S.ABS-2.DAT-P.DAT-CPST"), ("estasiño-ra", "station-S.ALL")]
    glossedWords := [⟨['G', 'u', '-', 'k'], ['1', 'P', '-', 'E', 'R', 'G'], [⟨['G', 'u'], ['1', 'P'], none⟩, ⟨['k'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['a', 't', 'z', 'o'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['a', 't', 'z', 'o'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['l', 'a', 'g', 'u', 'n', '-', 'd', 'u'], ['a', 'c', 'c', 'o', 'm', 'p', 'a', 'n', 'y', '-', 'P', 'R', 'F'], [⟨['l', 'a', 'g', 'u', 'n'], ['a', 'c', 'c', 'o', 'm', 'p', 'a', 'n', 'y'], none⟩, ⟨['d', 'u'], ['P', 'R', 'F'], some '-'⟩]⟩, ⟨['u', '-', 'a', '-', 't', 'z', 'u', '-', 'e', '-', 'n'], ['2', 'P', '.', 'E', 'R', 'G', '-', 'P', 'A', 'S', 'T', '.', '3', 'S', '.', 'A', 'B', 'S', '-', '2', '.', 'D', 'A', 'T', '-', 'P', '.', 'D', 'A', 'T', '-', 'C', 'P', 'S', 'T'], [⟨['u'], ['2', 'P', '.', 'E', 'R', 'G'], none⟩, ⟨['a'], ['P', 'A', 'S', 'T', '.', '3', 'S', '.', 'A', 'B', 'S'], some '-'⟩, ⟨['t', 'z', 'u'], ['2', '.', 'D', 'A', 'T'], some '-'⟩, ⟨['e'], ['P', '.', 'D', 'A', 'T'], some '-'⟩, ⟨['n'], ['C', 'P', 'S', 'T'], some '-'⟩]⟩, ⟨['e', 's', 't', 'a', 's', 'i', 'ñ', 'o', '-', 'r', 'a'], ['s', 't', 'a', 't', 'i', 'o', 'n', '-', 'S', '.', 'A', 'L', 'L'], [⟨['e', 's', 't', 'a', 's', 'i', 'ñ', 'o'], ['s', 't', 'a', 't', 'i', 'o', 'n'], none⟩, ⟨['r', 'a'], ['S', '.', 'A', 'L', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("variety", "zamudio"), ("arguments", "erg1plDat2pl")] }

def all : List Datum := [ex_7a, ex_7b, ex_7c, ex_17b, ex_19b]

/-- The Biscayan varieties of the examples. -/
inductive Variety where
  /-- ondarru: the variety of Ondarru -/
  | ondarru
  /-- zamudio: the variety of Zamudio -/
  | zamudio
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `variety`. -/
def variety (e : Datum) : Option Variety :=
  e.parse? "variety" [("ondarru", .ondarru), ("zamudio", .zamudio)]

/-- The arguments the auxiliary cross-references. -/
inductive Arguments where
  /-- erg2sgAbs1pl: a second singular ergative and a first plural absolutive argument -/
  | erg2sgAbs1pl
  /-- erg1plDat2pl: a first plural ergative, a second plural dative and a third singular absolutive argument -/
  | erg1plDat2pl
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `arguments`. -/
def arguments (e : Datum) : Option Arguments :=
  e.parse? "arguments" [("erg2sgAbs1pl", .erg2sgAbs1pl), ("erg1plDat2pl", .erg1plDat2pl)]

/-- The Taos sentences of (7) and the Basque auxiliaries the paper stars. -/
inductive Example where
  | ex_7a
  | ex_7b
  | ex_7c
  | ex_17b
  | ex_19b
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_7a, .ex_7b, .ex_7c, .ex_17b, .ex_19b]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_7a => _root_.Middleton2026.Examples.ex_7a
  | .ex_7b => _root_.Middleton2026.Examples.ex_7b
  | .ex_7c => _root_.Middleton2026.Examples.ex_7c
  | .ex_17b => _root_.Middleton2026.Examples.ex_17b
  | .ex_19b => _root_.Middleton2026.Examples.ex_19b

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.Middleton2026.Examples.all := rfl

/-- The value the example records under `variety`. -/
def Example.variety : Example → Option Variety
  | .ex_7a => none
  | .ex_7b => none
  | .ex_7c => none
  | .ex_17b => some .ondarru
  | .ex_19b => some .zamudio

theorem Example.variety_datum :
    ∀ x : Example, _root_.Middleton2026.Examples.variety x.datum = x.variety := by
  decide +kernel

/-- The value the example records under `arguments`. -/
def Example.arguments : Example → Option Arguments
  | .ex_7a => none
  | .ex_7b => none
  | .ex_7c => none
  | .ex_17b => some .erg2sgAbs1pl
  | .ex_19b => some .erg1plDat2pl

theorem Example.arguments_datum :
    ∀ x : Example, _root_.Middleton2026.Examples.arguments x.datum = x.arguments := by
  decide +kernel

end Middleton2026.Examples
