module

public import Linglib.Data.Examples.Schema

/-!
# `Feinmann2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Feinmann2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Feinmann2026.Examples`.
-/

@[expose] public section

namespace Feinmann2026.Examples

def ex_1B1 : Datum :=
  { id := "feinmann2026_1B1"
    source := ⟨"feinmann-2026", "(1B1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is (coming)."
    glossedTokens := []
    context := "A: Is Mary coming to the party tonight?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "yes")] }

def ex_1B2 : Datum :=
  { id := "feinmann2026_1B2"
    source := ⟨"feinmann-2026", "(1B2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jeff Bezos hates Bill Gates."
    glossedTokens := []
    context := "A: Is Mary coming to the party tonight?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "no")] }

def ex_2B1 : Datum :=
  { id := "feinmann2026_2B1"
    source := ⟨"feinmann-2026", "(2B1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She has an exam tomorrow morning."
    glossedTokens := []
    context := "A: Is Mary coming to the party tonight?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "yes")] }

def ex_2B2 : Datum :=
  { id := "feinmann2026_2B2"
    source := ⟨"feinmann-2026", "(2B2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jeff Bezos hates Bill Gates."
    glossedTokens := []
    context := "A: Is Mary coming to the party tonight?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "no")] }

def ex_3B1 : Datum :=
  { id := "feinmann2026_3B1"
    source := ⟨"feinmann-2026", "(3B1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary's father told me she's coming, but Mary's mother said the opposite."
    glossedTokens := []
    context := "A: Is Mary coming to the party tonight?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "yes")] }

def ex_3B2 : Datum :=
  { id := "feinmann2026_3B2"
    source := ⟨"feinmann-2026", "(3B2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jeff Bezos hates Bill Gates."
    glossedTokens := []
    context := "A: Is Mary coming to the party tonight?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "no")] }

def ex_4B1 : Datum :=
  { id := "feinmann2026_4B1"
    source := ⟨"feinmann-2026", "(4B1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary's parents gave me conflicting reports."
    glossedTokens := []
    context := "A: Is Mary coming to the party tonight?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "yes")] }

def ex_4B2 : Datum :=
  { id := "feinmann2026_4B2"
    source := ⟨"feinmann-2026", "(4B2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jeff Bezos hates Bill Gates."
    glossedTokens := []
    context := "A: Is Mary coming to the party tonight?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "no")] }

def ex_5 : Datum :=
  { id := "feinmann2026_5"
    source := ⟨"feinmann-2026", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "And what does that have to do with anything?"
    glossedTokens := []
    context := "A: Is Mary coming to the party? B: Mary's parents gave me conflicting reports."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_6 : Datum :=
  { id := "feinmann2026_6"
    source := ⟨"feinmann-2026", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "And what does that have to do with anything?"
    glossedTokens := []
    context := "A: Is Mary coming to the party? B: Jeff Bezos hates Bill Gates."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_16 : Datum :=
  { id := "feinmann2026_16"
    source := ⟨"feinmann-2026", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is there a ball inside the box? Some people think there is, while some people think there isn't. Keep voting—we'll open the box at 5 p.m.!"
    glossedTokens := []
    context := "A TV game show host, who is there to build suspense and not to reveal the answer, addresses the audience voting on whether there is a ball inside the box."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "yes")] }

def ex_17 : Datum :=
  { id := "feinmann2026_17"
    source := ⟨"feinmann-2026", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'Is there a ball inside the box?' Jeff Bezos hates Bill Gates. Keep voting—we'll open the box at 5 p.m.!"
    glossedTokens := []
    context := "A TV game show host, who is there to build suspense and not to reveal the answer, addresses the audience voting on whether there is a ball inside the box."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "no")] }

def ex_20 : Datum :=
  { id := "feinmann2026_20"
    source := ⟨"feinmann-2026", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She has a difficult exam tomorrow."
    glossedTokens := []
    context := "A: Is Mary coming to the party tonight?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "yes")] }

def ex_21 : Datum :=
  { id := "feinmann2026_21"
    source := ⟨"feinmann-2026", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The roads are piled high with snow."
    glossedTokens := []
    context := "A: Is Mary driving to the party?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "yes")] }

def ex_22B1 : Datum :=
  { id := "feinmann2026_22B1"
    source := ⟨"feinmann-2026", "(22B1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her father told me she's in a party mood, but her mother told me she isn't."
    glossedTokens := []
    context := "A: Is Mary coming to the party tonight?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "yes")] }

def ex_22B2 : Datum :=
  { id := "feinmann2026_22B2"
    source := ⟨"feinmann-2026", "(22B2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her parents can't agree on whether she is in a party mood tonight."
    glossedTokens := []
    context := "A: Is Mary coming to the party tonight?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "yes")] }

def ex_22B3 : Datum :=
  { id := "feinmann2026_22B3"
    source := ⟨"feinmann-2026", "(22B3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jeff Bezos hates Bill Gates."
    glossedTokens := []
    context := "A: Is Mary coming to the party tonight?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "no")] }

def ex_23 : Datum :=
  { id := "feinmann2026_23"
    source := ⟨"feinmann-2026", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "On the assumption Mary is not coming to the party tonight, setting off fireworks may not be a bad idea."
    glossedTokens := []
    context := "A: Is Mary coming to the party tonight?"
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("relevant", "no")] }

def all : List Datum := [ex_1B1, ex_1B2, ex_2B1, ex_2B2, ex_3B1, ex_3B2, ex_4B1, ex_4B2, ex_5, ex_6, ex_16, ex_17, ex_20, ex_21, ex_22B1, ex_22B2, ex_22B3, ex_23]

end Feinmann2026.Examples
