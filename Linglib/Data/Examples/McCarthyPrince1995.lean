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
    contrasts := []
    readings := []
    paperFeatures := [("input", "divide"), ("velar", "palatalized")] }

def ex_124a_plain : Datum :=
  { id := "mccarthyprince1995_124a_plain"
    source := ⟨"mccarthy-prince-1995", "(124)"⟩
    reportedIn := none
    method := some .description
    language := "akan1250"
    primaryText := "kɛ"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("input", "divide"), ("velar", "plain")] }

def ex_127a_i : Datum :=
  { id := "mccarthyprince1995_127a_i"
    source := ⟨"mccarthy-prince-1995", "(127a)"⟩
    reportedIn := none
    method := some .description
    language := "akan1250"
    primaryText := "kita"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("input", "polish"), ("velar", "plain")] }

def ex_127a_ii : Datum :=
  { id := "mccarthyprince1995_127a_ii"
    source := ⟨"mccarthy-prince-1995", "(127a)"⟩
    reportedIn := none
    method := some .description
    language := "akan1250"
    primaryText := "tɕita"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("input", "polish"), ("velar", "palatalized")] }

def ex_128a : Datum :=
  { id := "mccarthyprince1995_128a"
    source := ⟨"mccarthy-prince-1995", "(128a)"⟩
    reportedIn := none
    method := some .description
    language := "akan1250"
    primaryText := "kɛsɪ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("input", "big"), ("velar", "plain")] }

def fn72 : Datum :=
  { id := "mccarthyprince1995_fn72"
    source := ⟨"mccarthy-prince-1995", "fn. 72"⟩
    reportedIn := none
    method := some .description
    language := "akan1250"
    primaryText := "tɕɛsɪ"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("input", "big"), ("velar", "palatalized")] }

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
    paperFeatures := [("input", "bite"), ("application", "under")] }

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
    paperFeatures := [("input", "bite"), ("application", "normal")] }

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
    paperFeatures := [("input", "bite"), ("application", "over")] }

def all : List Datum := [ex_6a, ex_6b, ex_6c, ex_124a, ex_124a_plain, ex_127a_i, ex_127a_ii, ex_128a, fn72, ex_125a, ex_125a_pal, fn71]

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

/-- The Akan inputs whose outputs the paper judges. -/
inductive Input where
  /-- divide: /kɛ/ 'divide' -/
  | divide
  /-- big: /kɛsɪ/ 'big' -/
  | big
  /-- polish: /kita/ 'polish' -/
  | polish
  /-- bite: /RED–ka/, the reduplication of 'bite' -/
  | bite
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `input`. -/
def input (e : Datum) : Option Input :=
  e.parse? "input" [("divide", .divide), ("big", .big), ("polish", .polish), ("bite", .bite)]

/-- The realization of the initial velar of an unreduplicated Akan word. -/
inductive Velar where
  /-- plain: a velar -/
  | plain
  /-- palatalized: a palatal -/
  | palatalized
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `velar`. -/
def velar (e : Datum) : Option Velar :=
  e.parse? "velar" [("plain", .plain), ("palatalized", .palatalized)]

end McCarthyPrince1995.Examples
