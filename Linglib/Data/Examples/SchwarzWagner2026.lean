module

public import Linglib.Data.Examples.Schema

/-!
# `SchwarzWagner2026` — typed example data

Auto-generated from `Linglib/Data/Examples/SchwarzWagner2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace SchwarzWagner2026.Examples`.
-/

@[expose] public section

namespace SchwarzWagner2026.Examples

def ex_1a : Datum :=
  { id := "schwarzwagner2026_1a"
    source := ⟨"schwarz-wagner-2026", "(1), (3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some players responded."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("strengthened: some but not all players responded", .acceptable)]
    paperFeatures := [("case", "bare"), ("excluded", "scalar"), ("available", "yes")] }

def ex_1b : Datum :=
  { id := "schwarzwagner2026_1b"
    source := ⟨"schwarz-wagner-2026", "(1), (8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some players responded."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("strengthened: all players responded", .unacceptable)]
    paperFeatures := [("case", "bare"), ("excluded", "symmetric"), ("available", "no")] }

def ex_33a : Datum :=
  { id := "schwarzwagner2026_33a"
    source := ⟨"schwarz-wagner-2026", "(33), (35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some players have not responded."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("strengthened: some but not all players responded", .acceptable)]
    paperFeatures := [("case", "negated"), ("excluded", "scalar"), ("available", "yes")] }

def ex_33b : Datum :=
  { id := "schwarzwagner2026_33b"
    source := ⟨"schwarz-wagner-2026", "(33), (35b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some players have not responded."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("strengthened: no players responded", .unacceptable)]
    paperFeatures := [("case", "negated"), ("excluded", "symmetric"), ("available", "no")] }

def ex_42a : Datum :=
  { id := "schwarzwagner2026_42a"
    source := ⟨"schwarz-wagner-2026", "(42), (44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some players were inside."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("strengthened: some but not all players were inside", .acceptable)]
    paperFeatures := [("case", "antonym"), ("excluded", "scalar"), ("available", "yes")] }

def ex_42b : Datum :=
  { id := "schwarzwagner2026_42b"
    source := ⟨"schwarz-wagner-2026", "(42), (44b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some players were inside."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("strengthened: all players were inside", .unacceptable)]
    paperFeatures := [("case", "antonym"), ("excluded", "symmetric"), ("available", "no")] }

def ex_52a : Datum :=
  { id := "schwarzwagner2026_52a"
    source := ⟨"schwarz-wagner-2026", "(52), (53b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Going to confession is permitted."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("strengthened: permitted and not required", .acceptable)]
    paperFeatures := [("case", "lexicalized"), ("excluded", "scalar"), ("available", "yes")] }

def ex_52b : Datum :=
  { id := "schwarzwagner2026_52b"
    source := ⟨"schwarz-wagner-2026", "(52), (53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Going to confession is permitted."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("strengthened: permitted and required", .unacceptable)]
    paperFeatures := [("case", "lexicalized"), ("excluded", "symmetric"), ("available", "no")] }

def ex_54a : Datum :=
  { id := "schwarzwagner2026_54a"
    source := ⟨"schwarz-wagner-2026", "(54a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Doing drugs is optional, and in fact it is not (even) permitted"
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_54b : Datum :=
  { id := "schwarzwagner2026_54b"
    source := ⟨"schwarz-wagner-2026", "(54b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Doing drugs is optional, and in fact it is (even) required"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_55a : Datum :=
  { id := "schwarzwagner2026_55a"
    source := ⟨"schwarz-wagner-2026", "(55a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Taking drugs is not optional."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("preferred: taking drugs is required", .acceptable)]
    paperFeatures := [] }

def ex_55b : Datum :=
  { id := "schwarzwagner2026_55b"
    source := ⟨"schwarz-wagner-2026", "(55b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Taking drugs is non-optional."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("preferred: taking drugs is required", .acceptable)]
    paperFeatures := [] }

def ex_76a : Datum :=
  { id := "schwarzwagner2026_76a"
    source := ⟨"schwarz-wagner-2026", "(76)"⟩
    reportedIn := some ⟨"breheny-et-al-2018", "(41)"⟩
    language := "nucl1643"
    primaryText := "John-wa ki-te yoi."
    glossedTokens := [("John-wa", "John-TOP"), ("ki-te", "come-GERUND"), ("yoi", "good")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("strengthened: John is allowed but not required to come", .acceptable)]
    paperFeatures := [("case", "minimal"), ("excluded", "scalar"), ("available", "yes")] }

def ex_76b : Datum :=
  { id := "schwarzwagner2026_76b"
    source := ⟨"schwarz-wagner-2026", "(76)"⟩
    reportedIn := some ⟨"breheny-et-al-2018", "(41)"⟩
    language := "nucl1643"
    primaryText := "John-wa ki-te yoi."
    glossedTokens := [("John-wa", "John-TOP"), ("ki-te", "come-GERUND"), ("yoi", "good")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("strengthened: John must come", .unacceptable)]
    paperFeatures := [("case", "minimal"), ("excluded", "symmetric"), ("available", "no")] }

def all : List Datum := [ex_1a, ex_1b, ex_33a, ex_33b, ex_42a, ex_42b, ex_52a, ex_52b, ex_54a, ex_54b, ex_55a, ex_55b, ex_76a, ex_76b]

end SchwarzWagner2026.Examples
