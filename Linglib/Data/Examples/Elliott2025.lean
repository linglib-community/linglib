module

public import Linglib.Data.Examples.Schema

/-!
# `Elliott2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Elliott2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Elliott2025.Examples`.
-/

@[expose] public section

namespace Elliott2025.Examples

def ex_6 : Datum :=
  { id := "elliott2025_6"
    source := ⟨"elliott-2025", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Three boys gathered."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1")] }

def ex_7 : Datum :=
  { id := "elliott2025_7"
    source := ⟨"elliott-2025", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Three boys are singing or dancing."
    glossedTokens := []
    context := "Boys b1 and b2 are only singing, b3 is only dancing, and no other boys are singing or dancing."
    judgment := .acceptable
    contrasts := []
    readings := [("distributive scope over the disjunction", .acceptable)]
    paperFeatures := [("section", "2.1")] }

def ex_10 : Datum :=
  { id := "elliott2025_10"
    source := ⟨"elliott-2025", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Less than three boys sneezed."
    glossedTokens := []
    context := "Three boys sneezed."
    judgment := .acceptable
    contrasts := []
    readings := [("true in the context", .unacceptable)]
    paperFeatures := [("section", "2.2.1")] }

def ex_12 : Datum :=
  { id := "elliott2025_12"
    source := ⟨"elliott-2025", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Less than three boys sneezed."
    glossedTokens := []
    context := "No boys sneezed."
    judgment := .acceptable
    contrasts := []
    readings := [("true in the context", .acceptable)]
    paperFeatures := [("section", "2.2.2")] }

def ex_47 : Datum :=
  { id := "elliott2025_47"
    source := ⟨"elliott-2025", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If two relatives of mine die, I'll inherit a house."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("∃ > if..then > Dist", .acceptable), ("∃ > Dist > if..then", .unacceptable)]
    paperFeatures := [("section", "5")] }

def ex_48a : Datum :=
  { id := "elliott2025_48a"
    source := ⟨"elliott-2025", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If all relatives of mine die, I'll inherit a house."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("∀ > if..then", .unacceptable)]
    paperFeatures := [("section", "5")] }

def ex_48b : Datum :=
  { id := "elliott2025_48b"
    source := ⟨"elliott-2025", "(48b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If no relatives of mine die, I'll inherit a house."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("no > if..then", .unacceptable)]
    paperFeatures := [("section", "5")] }

def ex_50 : Datum :=
  { id := "elliott2025_50"
    source := ⟨"elliott-2025", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If James bets on exactly two numbers, he'll win this round (I just don't know which two)."
    glossedTokens := []
    context := "James plays a two-ball roulette variant, betting on any two numbers and winning if both balls land on them; the croupier has rigged the wheel so the balls land on two predetermined numbers."
    judgment := .acceptable
    contrasts := []
    readings := [("∃ > if..then (exceptional existential scope)", .acceptable)]
    paperFeatures := [("section", "5")] }

def ex_51a : Datum :=
  { id := "elliott2025_51a"
    source := ⟨"elliott-2025", "(51a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some boy gathered."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1")] }

def ex_51b : Datum :=
  { id := "elliott2025_51b"
    source := ⟨"elliott-2025", "(51b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some boys gathered."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1")] }

def all : List Datum := [ex_6, ex_7, ex_10, ex_12, ex_47, ex_48a, ex_48b, ex_50, ex_51a, ex_51b]

end Elliott2025.Examples
