module

public import Linglib.Data.Examples.Schema

/-!
# `Yalcin2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Yalcin2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Yalcin2010.Examples`.
-/

@[expose] public section

namespace Yalcin2010.Examples

def die_p1 : Datum :=
  { id := "yalcin2010_die_p1"
    source := ⟨"yalcin-2010", "(P1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Probably, a number below 9 came up."
    glossedTokens := []
    context := "A fair twelve-sided die, with the sides numbered one to twelve, has been rolled."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("pattern", "E1"), ("probability", "8/12")] }

def die_p2 : Datum :=
  { id := "yalcin2010_die_p2"
    source := ⟨"yalcin-2010", "(P2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Probably, a number above 4 came up."
    glossedTokens := []
    context := "A fair twelve-sided die, with the sides numbered one to twelve, has been rolled."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("pattern", "E1"), ("probability", "8/12")] }

def die_c : Datum :=
  { id := "yalcin2010_die_c"
    source := ⟨"yalcin-2010", "(C)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Probably, a number above 4 and below 9 came up."
    glossedTokens := []
    context := "A fair twelve-sided die, with the sides numbered one to twelve, has been rolled."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("pattern", "E1"), ("probability", "4/12")] }

def ex8 : Datum :=
  { id := "yalcin2010_ex8"
    source := ⟨"yalcin-2010", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The coin probably landed heads."
    glossedTokens := []
    context := "A fair coin has been biased with a thin piece of tape, so that it is just slightly more likely to land heads than tails, and flipped."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6"), ("reading", "appreciably more likely than not"), ("felicity", "infelicitous")] }

def ex9 : Datum :=
  { id := "yalcin2010_ex9"
    source := ⟨"yalcin-2010", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone probably lost the lottery."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("probably > everyone", .acceptable), ("everyone > probably", .unacceptable)]
    paperFeatures := [("section", "7"), ("principle", "epistemic containment")] }

def ex17 : Datum :=
  { id := "yalcin2010_ex17"
    source := ⟨"yalcin-2010", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John imagines that it is raining but that he doesn't know it is raining."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "8"), ("embedding", "imagine")] }

def ex18 : Datum :=
  { id := "yalcin2010_ex18"
    source := ⟨"yalcin-2010", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John imagines that it is raining but it is not likely that it is raining."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "8"), ("embedding", "imagine")] }

def ex19 : Datum :=
  { id := "yalcin2010_ex19"
    source := ⟨"yalcin-2010", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Probably, Sally is likely to be at the party."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("section", "8"), ("phenomenon", "modal concord")] }

def all : List Datum := [die_p1, die_p2, die_c, ex8, ex9, ex17, ex18, ex19]

end Yalcin2010.Examples
