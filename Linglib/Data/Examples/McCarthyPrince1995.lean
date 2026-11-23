module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `McCarthyPrince1995` — typed example data

Auto-generated from `Linglib/Data/Examples/McCarthyPrince1995.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace McCarthyPrince1995.Examples`.
-/

@[expose] public section

namespace McCarthyPrince1995.Examples

def ex_6a : Datum :=
  { id := "mccarthyprince1995_6a"
    source := ⟨"mccarthy-prince-1995", "(6a)"⟩
    reportedIn := none
    method := some .description
    language := "java1254"
    primaryText := "bəḍa–bəḍa–e"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("application", "over")] }

def ex_6b : Datum :=
  { id := "mccarthyprince1995_6b"
    source := ⟨"mccarthy-prince-1995", "(6b)"⟩
    reportedIn := none
    method := some .description
    language := "java1254"
    primaryText := "bəḍah–bəḍah–e"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("application", "under")] }

def ex_6c : Datum :=
  { id := "mccarthyprince1995_6c"
    source := ⟨"mccarthy-prince-1995", "(6c)"⟩
    reportedIn := none
    method := some .description
    language := "java1254"
    primaryText := "bəḍah–bəḍa–e"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("application", "normal")] }

def ex_124a : Datum :=
  { id := "mccarthyprince1995_124a"
    source := ⟨"mccarthy-prince-1995", "(124)"⟩
    reportedIn := none
    method := some .description
    language := "akan1250"
    primaryText := "tɕɛ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("kɛ", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def kita : Datum :=
  { id := "mccarthyprince1995_kita"
    source := ⟨"mccarthy-prince-1995", "p. 94"⟩
    reportedIn := none
    method := some .description
    language := "akan1250"
    primaryText := "kita"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("tɕita", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_125a : Datum :=
  { id := "mccarthyprince1995_125a"
    source := ⟨"mccarthy-prince-1995", "(125)"⟩
    reportedIn := none
    method := some .description
    language := "akan1250"
    primaryText := "kɪ–kaʔ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("application", "under")] }

def ex_125a_pal : Datum :=
  { id := "mccarthyprince1995_125a_pal"
    source := ⟨"mccarthy-prince-1995", "(125)"⟩
    reportedIn := none
    method := some .description
    language := "akan1250"
    primaryText := "tɕɪ–kaʔ"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("application", "normal")] }

def fn71 : Datum :=
  { id := "mccarthyprince1995_fn71"
    source := ⟨"mccarthy-prince-1995", "fn. 71"⟩
    reportedIn := none
    method := some .description
    language := "akan1250"
    primaryText := "tɕɪ–tɕa"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("application", "over")] }

def all : List Datum := [ex_6a, ex_6b, ex_6c, ex_124a, kita, ex_125a, ex_125a_pal, fn71]

/-- How a phonological process applies in a candidate reduplicated form. -/
inductive Application where
  /-- over: the process applies in base and reduplicant, though its conditions are met in one -/
  | over
  /-- under: the process applies in neither, though its conditions are met in one -/
  | under
  /-- normal: the process applies only where its conditions are met -/
  | normal
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `application`. -/
def application (e : Datum) : Option Application :=
  e.parse? "application" [("over", .over), ("under", .under), ("normal", .normal)]

end McCarthyPrince1995.Examples
