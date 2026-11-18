module

public import Linglib.Data.Examples.Schema

/-!
# `HalleVauxWolfe2000` — typed example data

Auto-generated from `Linglib/Data/Examples/HalleVauxWolfe2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HalleVauxWolfe2000.Examples`.
-/

@[expose] public section

namespace HalleVauxWolfe2000.Examples

def ex44a : Datum :=
  { id := "hallevauxwolfe2000_ex44a"
    source := ⟨"halle-vaux-wolfe-2000", "(44a)"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "dʲekʲhʲinʲ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2.4"), ("phenomenon", "dorsalAssimilation")] }

def ex44a_ii : Datum :=
  { id := "hallevauxwolfe2000_ex44a-ii"
    source := ⟨"halle-vaux-wolfe-2000", "(44a-ii)"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "dʲekʲhʲiŋʲ gan eː"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2.4"), ("phenomenon", "dorsalAssimilation")] }

def ex44b : Datum :=
  { id := "hallevauxwolfe2000_ex44b"
    source := ⟨"halle-vaux-wolfe-2000", "(44b)"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "dʲiːlən"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2.4"), ("phenomenon", "dorsalAssimilation")] }

def ex44b_ii : Datum :=
  { id := "hallevauxwolfe2000_ex44b-ii"
    source := ⟨"halle-vaux-wolfe-2000", "(44b-ii)"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "dʲiːləŋgʲiːvʲrʲi"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2.4"), ("phenomenon", "dorsalAssimilation")] }

def all : List Datum := [ex44a, ex44a_ii, ex44b, ex44b_ii]

end HalleVauxWolfe2000.Examples
