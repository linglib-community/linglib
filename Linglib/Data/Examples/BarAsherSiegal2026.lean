module

public import Linglib.Data.Examples.Schema

/-!
# `BarAsherSiegal2026` — typed example data

Auto-generated from `Linglib/Data/Examples/BarAsherSiegal2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BarAsherSiegal2026.Examples`.
-/

@[expose] public section

namespace BarAsherSiegal2026.Examples

def bas2026_1a : Datum :=
  { id := "bas2026_1a"
    source := ⟨"bar-asher-siegal-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A kangaroo is a marsupial because it has a pouch."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "because"), ("relation", "grounding")] }

def bas2026_1b : Datum :=
  { id := "bas2026_1b"
    source := ⟨"bar-asher-siegal-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary's living nearby causes John to prefer this neighborhood."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "cause"), ("relation", "grounding")] }

def bas2026_1c : Datum :=
  { id := "bas2026_1c"
    source := ⟨"bar-asher-siegal-2026", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The floor is black because of the ants that might infest it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "because of"), ("relation", "grounding")] }

def bas2026_2a : Datum :=
  { id := "bas2026_2a"
    source := ⟨"bar-asher-siegal-2026", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam opened the door."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "lexical causative"), ("entails", "(2b)")] }

def bas2026_2b : Datum :=
  { id := "bas2026_2b"
    source := ⟨"bar-asher-siegal-2026", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam caused the door to open."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Sam opened a window and a gust blew the door open", .acceptable)]
    paperFeatures := [("construction", "periphrastic causative")] }

def bas2026_i : Datum :=
  { id := "bas2026_i"
    source := ⟨"bar-asher-siegal-2026", "(i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The city council denied the demonstrators the permit because they advocated violence."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "because"), ("pronoun", "they"), ("antecedent", "the demonstrators")] }

def bas2026_ii : Datum :=
  { id := "bas2026_ii"
    source := ⟨"bar-asher-siegal-2026", "(ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The city council denied the demonstrators the permit because they feared violence."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "because"), ("pronoun", "they"), ("antecedent", "the city council")] }

def bas2026_iii : Datum :=
  { id := "bas2026_iii"
    source := ⟨"bar-asher-siegal-2026", "(iii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John drank wine at the party, which caused the accident he was involved in later that night as he drove back home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "cause"), ("enrichment", "John drank enough wine to impair his driving")] }

def all : List Datum := [bas2026_1a, bas2026_1b, bas2026_1c, bas2026_2a, bas2026_2b, bas2026_i, bas2026_ii, bas2026_iii]

end BarAsherSiegal2026.Examples
