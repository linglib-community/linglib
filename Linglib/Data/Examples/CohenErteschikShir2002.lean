module

public import Linglib.Data.Examples.Schema

/-!
# `CohenErteschikShir2002` — typed example data

Auto-generated from `Linglib/Data/Examples/CohenErteschikShir2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace CohenErteschikShir2002.Examples`.
-/

@[expose] public section

namespace CohenErteschikShir2002.Examples

def boys_brave : Datum :=
  { id := "cohenerteschikshir2002_boys_brave"
    source := ⟨"cohen-erteschik-shir-2002", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Boys are brave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable), ("existential", .unacceptable)]
    paperFeatures := [("predicate_level", "individual")] }

def boys_present : Datum :=
  { id := "cohenerteschikshir2002_boys_present"
    source := ⟨"cohen-erteschik-shir-2002", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Boys are present."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("generic", .acceptable), ("existential", .acceptable)]
    paperFeatures := [("predicate_level", "stage"), ("locative_status", "argument")] }

def firemen_available : Datum :=
  { id := "cohenerteschikshir2002_firemen_available"
    source := ⟨"cohen-erteschik-shir-2002", "(64)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Who is available? B: FIREMEN are available."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("existential", .acceptable)]
    paperFeatures := [("predicate_level", "stage"), ("locative_status", "argument")] }

def all : List Datum := [boys_brave, boys_present, firemen_available]

end CohenErteschikShir2002.Examples
