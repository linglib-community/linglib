module

public import Linglib.Data.Examples.Schema

/-!
# `Geurts2005` — typed example data

Auto-generated from `Linglib/Data/Examples/Geurts2005.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Geurts2005.Examples`.
-/

@[expose] public section

namespace Geurts2005.Examples

def ex_1a : Datum :=
  { id := "geurts2005_1a"
    source := ⟨"geurts-2005", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may do this or (else) you may do that."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("force1", "may"), ("force2", "may"), ("flavor", "deontic")] }

def ex_1b : Datum :=
  { id := "geurts2005_1b"
    source := ⟨"geurts-2005", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You must do this or (else) you must do that."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("force1", "must"), ("force2", "must"), ("flavor", "deontic")] }

def ex_1c : Datum :=
  { id := "geurts2005_1c"
    source := ⟨"geurts-2005", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may do this or (else) you must do that."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("force1", "may"), ("force2", "must"), ("flavor", "deontic")] }

def ex_1d : Datum :=
  { id := "geurts2005_1d"
    source := ⟨"geurts-2005", "(1d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You must do this or (else) you may do that."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("force1", "must"), ("force2", "may"), ("flavor", "deontic")] }

def ex_2a : Datum :=
  { id := "geurts2005_2a"
    source := ⟨"geurts-2005", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It may be here or (else) it may be there."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("force1", "may"), ("force2", "may"), ("flavor", "epistemic")] }

def ex_2b : Datum :=
  { id := "geurts2005_2b"
    source := ⟨"geurts-2005", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be here or (else) it must be there."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("force1", "must"), ("force2", "must"), ("flavor", "epistemic")] }

def ex_2c : Datum :=
  { id := "geurts2005_2c"
    source := ⟨"geurts-2005", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It may be here or (else) it must be there."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("force1", "may"), ("force2", "must"), ("flavor", "epistemic")] }

def ex_2d : Datum :=
  { id := "geurts2005_2d"
    source := ⟨"geurts-2005", "(2d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be here or (else) it may be there."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("force1", "must"), ("force2", "may"), ("flavor", "epistemic")] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_1d, ex_2a, ex_2b, ex_2c, ex_2d]

end Geurts2005.Examples
