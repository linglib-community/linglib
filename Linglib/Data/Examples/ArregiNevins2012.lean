module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `ArregiNevins2012` — typed example data

Auto-generated from `Linglib/Data/Examples/ArregiNevins2012.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ArregiNevins2012.Examples`.
-/

@[expose] public section

namespace ArregiNevins2012.Examples

def ex_16 : Datum :=
  { id := "arreginevins2012_16"
    source := ⟨"arregi-nevins-2012", "(16)"⟩
    reportedIn := none
    method := some .elicitation
    language := "basq1248"
    primaryText := "Su-k gu-∅ ikus-i s-endu-n."
    glossedTokens := [("Su-k", "you(Sg)-ERG"), ("gu-∅", "us-ABS"), ("ikus-i", "see-PRF"), ("s-endu-n", "CL.E.2.SG-PST.1.PL-CPST")]
    glossedWords := [⟨['S', 'u', '-', 'k'], ['y', 'o', 'u', '(', 'S', 'g', ')', '-', 'E', 'R', 'G'], [⟨['S', 'u'], ['y', 'o', 'u', '(', 'S', 'g', ')'], none⟩, ⟨['k'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['g', 'u', '-', '∅'], ['u', 's', '-', 'A', 'B', 'S'], [⟨['g', 'u'], ['u', 's'], none⟩, ⟨['∅'], ['A', 'B', 'S'], some '-'⟩]⟩, ⟨['i', 'k', 'u', 's', '-', 'i'], ['s', 'e', 'e', '-', 'P', 'R', 'F'], [⟨['i', 'k', 'u', 's'], ['s', 'e', 'e'], none⟩, ⟨['i'], ['P', 'R', 'F'], some '-'⟩]⟩, ⟨['s', '-', 'e', 'n', 'd', 'u', '-', 'n'], ['C', 'L', '.', 'E', '.', '2', '.', 'S', 'G', '-', 'P', 'S', 'T', '.', '1', '.', 'P', 'L', '-', 'C', 'P', 'S', 'T'], [⟨['s'], ['C', 'L', '.', 'E', '.', '2', '.', 'S', 'G'], none⟩, ⟨['e', 'n', 'd', 'u'], ['P', 'S', 'T', '.', '1', '.', 'P', 'L'], some '-'⟩, ⟨['n'], ['C', 'P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("variety", "ondarru"), ("arguments", "erg2sgAbs1pl")] }

def ex_17a : Datum :=
  { id := "arreginevins2012_17a"
    source := ⟨"arregi-nevins-2012", "(17a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "basq1248"
    primaryText := "g-endu-su-n"
    glossedTokens := [("g-endu-su-n", "CL.A.1.PL-PST.1.PL-CL.E.2.SG-CPST")]
    glossedWords := [⟨['g', '-', 'e', 'n', 'd', 'u', '-', 's', 'u', '-', 'n'], ['C', 'L', '.', 'A', '.', '1', '.', 'P', 'L', '-', 'P', 'S', 'T', '.', '1', '.', 'P', 'L', '-', 'C', 'L', '.', 'E', '.', '2', '.', 'S', 'G', '-', 'C', 'P', 'S', 'T'], [⟨['g'], ['C', 'L', '.', 'A', '.', '1', '.', 'P', 'L'], none⟩, ⟨['e', 'n', 'd', 'u'], ['P', 'S', 'T', '.', '1', '.', 'P', 'L'], some '-'⟩, ⟨['s', 'u'], ['C', 'L', '.', 'E', '.', '2', '.', 'S', 'G'], some '-'⟩, ⟨['n'], ['C', 'P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("variety", "ondarru"), ("arguments", "erg2sgAbs1pl")] }

def ex_17b : Datum :=
  { id := "arreginevins2012_17b"
    source := ⟨"arregi-nevins-2012", "(17b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "basq1248"
    primaryText := "eu-su-n"
    glossedTokens := [("eu-su-n", "PST.1.PL-CL.E.2.SG-CPST")]
    glossedWords := [⟨['e', 'u', '-', 's', 'u', '-', 'n'], ['P', 'S', 'T', '.', '1', '.', 'P', 'L', '-', 'C', 'L', '.', 'E', '.', '2', '.', 'S', 'G', '-', 'C', 'P', 'S', 'T'], [⟨['e', 'u'], ['P', 'S', 'T', '.', '1', '.', 'P', 'L'], none⟩, ⟨['s', 'u'], ['C', 'L', '.', 'E', '.', '2', '.', 'S', 'G'], some '-'⟩, ⟨['n'], ['C', 'P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("variety", "ondarru"), ("arguments", "erg2sgAbs1pl")] }

def ex_17c : Datum :=
  { id := "arreginevins2012_17c"
    source := ⟨"arregi-nevins-2012", "(17c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "basq1248"
    primaryText := "s/∅/g/d-eu-su-n"
    glossedTokens := [("s/∅/g/d-eu-su-n", "L-PST.1.PL-CL.E.2.SG-CPST")]
    glossedWords := [⟨['s', '/', '∅', '/', 'g', '/', 'd', '-', 'e', 'u', '-', 's', 'u', '-', 'n'], ['L', '-', 'P', 'S', 'T', '.', '1', '.', 'P', 'L', '-', 'C', 'L', '.', 'E', '.', '2', '.', 'S', 'G', '-', 'C', 'P', 'S', 'T'], [⟨['s', '/', '∅', '/', 'g', '/', 'd'], ['L'], none⟩, ⟨['e', 'u'], ['P', 'S', 'T', '.', '1', '.', 'P', 'L'], some '-'⟩, ⟨['s', 'u'], ['C', 'L', '.', 'E', '.', '2', '.', 'S', 'G'], some '-'⟩, ⟨['n'], ['C', 'P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("variety", "ondarru"), ("arguments", "erg2sgAbs1pl")] }

def ex_20 : Datum :=
  { id := "arreginevins2012_20"
    source := ⟨"arregi-nevins-2012", "(20)"⟩
    reportedIn := none
    method := some .elicitation
    language := "basq1248"
    primaryText := "Gu-k atzo lagun-du y-a-tzu-e-n estasiño-ra."
    glossedTokens := [("Gu-k", "we-ERG"), ("atzo", "yesterday"), ("lagun-du", "accompany-PRF"), ("y-a-tzu-e-n", "L-PST.3.SG-CL.D.2-CL.D.PL-CPST"), ("estasiño-ra", "station-ALL.SG")]
    glossedWords := [⟨['G', 'u', '-', 'k'], ['w', 'e', '-', 'E', 'R', 'G'], [⟨['G', 'u'], ['w', 'e'], none⟩, ⟨['k'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['a', 't', 'z', 'o'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['a', 't', 'z', 'o'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['l', 'a', 'g', 'u', 'n', '-', 'd', 'u'], ['a', 'c', 'c', 'o', 'm', 'p', 'a', 'n', 'y', '-', 'P', 'R', 'F'], [⟨['l', 'a', 'g', 'u', 'n'], ['a', 'c', 'c', 'o', 'm', 'p', 'a', 'n', 'y'], none⟩, ⟨['d', 'u'], ['P', 'R', 'F'], some '-'⟩]⟩, ⟨['y', '-', 'a', '-', 't', 'z', 'u', '-', 'e', '-', 'n'], ['L', '-', 'P', 'S', 'T', '.', '3', '.', 'S', 'G', '-', 'C', 'L', '.', 'D', '.', '2', '-', 'C', 'L', '.', 'D', '.', 'P', 'L', '-', 'C', 'P', 'S', 'T'], [⟨['y'], ['L'], none⟩, ⟨['a'], ['P', 'S', 'T', '.', '3', '.', 'S', 'G'], some '-'⟩, ⟨['t', 'z', 'u'], ['C', 'L', '.', 'D', '.', '2'], some '-'⟩, ⟨['e'], ['C', 'L', '.', 'D', '.', 'P', 'L'], some '-'⟩, ⟨['n'], ['C', 'P', 'S', 'T'], some '-'⟩]⟩, ⟨['e', 's', 't', 'a', 's', 'i', 'ñ', 'o', '-', 'r', 'a'], ['s', 't', 'a', 't', 'i', 'o', 'n', '-', 'A', 'L', 'L', '.', 'S', 'G'], [⟨['e', 's', 't', 'a', 's', 'i', 'ñ', 'o'], ['s', 't', 'a', 't', 'i', 'o', 'n'], none⟩, ⟨['r', 'a'], ['A', 'L', 'L', '.', 'S', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("variety", "zamudio"), ("arguments", "erg1plDat2pl")] }

def all : List Datum := [ex_16, ex_17a, ex_17b, ex_17c, ex_20]

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

/-- The examples of the interaction of Participant Dissimilation with Ergative Metathesis. -/
inductive Example where
  | ex_16
  | ex_17a
  | ex_17b
  | ex_17c
  | ex_20
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_16, .ex_17a, .ex_17b, .ex_17c, .ex_20]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_16 => _root_.ArregiNevins2012.Examples.ex_16
  | .ex_17a => _root_.ArregiNevins2012.Examples.ex_17a
  | .ex_17b => _root_.ArregiNevins2012.Examples.ex_17b
  | .ex_17c => _root_.ArregiNevins2012.Examples.ex_17c
  | .ex_20 => _root_.ArregiNevins2012.Examples.ex_20

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.ArregiNevins2012.Examples.all := rfl

/-- The value the example records under `variety`. -/
def Example.variety : Example → Option Variety
  | .ex_16 => some .ondarru
  | .ex_17a => some .ondarru
  | .ex_17b => some .ondarru
  | .ex_17c => some .ondarru
  | .ex_20 => some .zamudio

theorem Example.variety_datum :
    ∀ x : Example, _root_.ArregiNevins2012.Examples.variety x.datum = x.variety := by
  decide +kernel

/-- The value the example records under `arguments`. -/
def Example.arguments : Example → Option Arguments
  | .ex_16 => some .erg2sgAbs1pl
  | .ex_17a => some .erg2sgAbs1pl
  | .ex_17b => some .erg2sgAbs1pl
  | .ex_17c => some .erg2sgAbs1pl
  | .ex_20 => some .erg1plDat2pl

theorem Example.arguments_datum :
    ∀ x : Example, _root_.ArregiNevins2012.Examples.arguments x.datum = x.arguments := by
  decide +kernel

end ArregiNevins2012.Examples
