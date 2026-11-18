module

public import Linglib.Data.Examples.Schema

/-!
# `Ryding2005` — typed example data

Auto-generated from `Linglib/Data/Examples/Ryding2005.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ryding2005.Examples`.
-/

@[expose] public section

namespace Ryding2005.Examples

def ex_642a : Datum :=
  { id := "ryding2005_642a"
    source := ⟨"ryding-2005", "p. 642"⟩
    reportedIn := none
    language := "stan1318"
    primaryText := "lays-a l-ʾustaadh-u muʾarrix-an."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("affirmative", "ryding2005_642b")] }

def ex_642b : Datum :=
  { id := "ryding2005_642b"
    source := ⟨"ryding-2005", "p. 642"⟩
    reportedIn := none
    language := "stan1318"
    primaryText := "al-ʾustaadh-u muʾarrix-un."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_642c : Datum :=
  { id := "ryding2005_642c"
    source := ⟨"ryding-2005", "p. 642"⟩
    reportedIn := none
    language := "stan1318"
    primaryText := "las-tu lubnaaniyyat-an."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("affirmative", "ryding2005_643a")] }

def ex_643a : Datum :=
  { id := "ryding2005_643a"
    source := ⟨"ryding-2005", "p. 643"⟩
    reportedIn := none
    language := "stan1318"
    primaryText := "ʾanaa lubnaaniyyat-un."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_642a, ex_642b, ex_642c, ex_643a]

end Ryding2005.Examples
