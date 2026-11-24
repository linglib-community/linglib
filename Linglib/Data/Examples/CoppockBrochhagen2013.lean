module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `CoppockBrochhagen2013` — typed example data

Auto-generated from `Linglib/Data/Examples/CoppockBrochhagen2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace CoppockBrochhagen2013.Examples`.
-/

@[expose] public section

namespace CoppockBrochhagen2013.Examples

def ex_70a : Datum :=
  { id := "coppockbrochhagen2013_70a"
    source := ⟨"coppock-brochhagen-2013", "(70a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A hexagon has at least five sides."
    glossedTokens := []
    context := "Spoken by someone who knows how many sides hexagons have."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "at least"), ("numeral", "5")] }

def ex_70b : Datum :=
  { id := "coppockbrochhagen2013_70b"
    source := ⟨"coppock-brochhagen-2013", "(70b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A hexagon has more than four sides."
    glossedTokens := []
    context := "Spoken by someone who knows how many sides hexagons have."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("modifier", "more than"), ("numeral", "4")] }

def all : List Datum := [ex_70a, ex_70b]

/-- The numeral modifiers the paper contrasts. -/
inductive Modifier where
  /-- at least: the superlative modifier *at least* -/
  | atLeast
  /-- more than: the comparative modifier *more than* -/
  | moreThan
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `modifier`. -/
def modifier (e : Datum) : Option Modifier :=
  e.parse? "modifier" [("at least", .atLeast), ("more than", .moreThan)]

end CoppockBrochhagen2013.Examples
