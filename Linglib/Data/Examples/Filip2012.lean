module

public import Linglib.Data.Examples.Schema

/-!
# `Filip2012` — typed example data

Auto-generated from `Linglib/Data/Examples/Filip2012.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Filip2012.Examples`.
-/

@[expose] public section

namespace Filip2012.Examples

def ex_1a_in : Datum :=
  { id := "filip2012_1a_in"
    source := ⟨"filip-2012", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John recovered in an hour."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "telic"), ("object", "none"), ("adverbial", "in")] }

def ex_1a_for : Datum :=
  { id := "filip2012_1a_for"
    source := ⟨"filip-2012", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John recovered for an hour."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "telic"), ("object", "none"), ("adverbial", "for")] }

def ex_1b_in : Datum :=
  { id := "filip2012_1b_in"
    source := ⟨"filip-2012", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John swam in an hour."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "atelic"), ("object", "none"), ("adverbial", "in")] }

def ex_1b_for : Datum :=
  { id := "filip2012_1b_for"
    source := ⟨"filip-2012", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John swam for an hour."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "atelic"), ("object", "none"), ("adverbial", "for")] }

def ex_25a_in : Datum :=
  { id := "filip2012_25a_in"
    source := ⟨"filip-2012", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John ate two apples in an hour."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "incremental"), ("object", "quantized"), ("adverbial", "in")] }

def ex_25a_for : Datum :=
  { id := "filip2012_25a_for"
    source := ⟨"filip-2012", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John ate two apples for an hour."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "incremental"), ("object", "quantized"), ("adverbial", "for")] }

def ex_25b_in : Datum :=
  { id := "filip2012_25b_in"
    source := ⟨"filip-2012", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John ate apples in an hour."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "incremental"), ("object", "cumulative"), ("adverbial", "in")] }

def ex_25b_for : Datum :=
  { id := "filip2012_25b_for"
    source := ⟨"filip-2012", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John ate apples for an hour."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "incremental"), ("object", "cumulative"), ("adverbial", "for")] }

def ex_26a_in : Datum :=
  { id := "filip2012_26a_in"
    source := ⟨"filip-2012", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John watched two apples on the display in an hour."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "atelic"), ("object", "quantized"), ("adverbial", "in")] }

def ex_26a_for : Datum :=
  { id := "filip2012_26a_for"
    source := ⟨"filip-2012", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John watched two apples on the display for an hour."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "atelic"), ("object", "quantized"), ("adverbial", "for")] }

def ex_26b_in : Datum :=
  { id := "filip2012_26b_in"
    source := ⟨"filip-2012", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John watched apples on the display in an hour."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "atelic"), ("object", "cumulative"), ("adverbial", "in")] }

def ex_26b_for : Datum :=
  { id := "filip2012_26b_for"
    source := ⟨"filip-2012", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John watched apples on the display for an hour."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "atelic"), ("object", "cumulative"), ("adverbial", "for")] }

def ex_31a_for : Datum :=
  { id := "filip2012_31a_for"
    source := ⟨"filip-2012", "(31a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John proved the theorem for an hour."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "incremental"), ("object", "quantized"), ("adverbial", "for")] }

def ex_37a_for : Datum :=
  { id := "filip2012_37a_for"
    source := ⟨"filip-2012", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The climbers reached the summit for an hour."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "telic"), ("object", "quantized"), ("adverbial", "for")] }

def ex_37a_in : Datum :=
  { id := "filip2012_37a_in"
    source := ⟨"filip-2012", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The climbers reached the summit in an hour."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("verbClass", "telic"), ("object", "quantized"), ("adverbial", "in")] }

def all : List Datum := [ex_1a_in, ex_1a_for, ex_1b_in, ex_1b_for, ex_25a_in, ex_25a_for, ex_25b_in, ex_25b_for, ex_26a_in, ex_26a_for, ex_26b_in, ex_26b_for, ex_31a_for, ex_37a_for, ex_37a_in]

end Filip2012.Examples
