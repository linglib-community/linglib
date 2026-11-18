module

public import Linglib.Data.Examples.Schema

/-!
# `YolyanComer2026` — typed example data

Auto-generated from `Linglib/Data/Examples/YolyanComer2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace YolyanComer2026.Examples`.
-/

@[expose] public section

namespace YolyanComer2026.Examples

def ex_5a : Datum :=
  { id := "yolyancomer2026_5a"
    source := ⟨"yolyan-comer-2026", "(5a)"⟩
    reportedIn := some ⟨"osborn-1966", ""⟩
    language := "wara1303"
    primaryText := "esoha-ya"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nasal_spreading", "none")] }

def ex_5b : Datum :=
  { id := "yolyancomer2026_5b"
    source := ⟨"yolyan-comer-2026", "(5b)"⟩
    reportedIn := some ⟨"osborn-1966", ""⟩
    language := "wara1303"
    primaryText := "nãõ-ỹã"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nasal_spreading", "to word end")] }

def ex_5c : Datum :=
  { id := "yolyancomer2026_5c"
    source := ⟨"yolyan-comer-2026", "(5c)"⟩
    reportedIn := some ⟨"osborn-1966", ""⟩
    language := "wara1303"
    primaryText := "nãõ-te"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nasal_spreading", "blocked by voiceless stop"), ("underlying_form", "/naote/")] }

def ex_5d : Datum :=
  { id := "yolyancomer2026_5d"
    source := ⟨"yolyan-comer-2026", "(5d)"⟩
    reportedIn := some ⟨"osborn-1966", ""⟩
    language := "wara1303"
    primaryText := "honĩw̃ãku-hae"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nasal_spreading", "blocked by voiceless stop")] }

def ex_5e : Datum :=
  { id := "yolyancomer2026_5e"
    source := ⟨"yolyan-comer-2026", "(5e)"⟩
    reportedIn := some ⟨"osborn-1966", ""⟩
    language := "wara1303"
    primaryText := "panãpanã-h̃ãẽ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nasal_spreading", "blocked by voiceless stop")] }

def all : List Datum := [ex_5a, ex_5b, ex_5c, ex_5d, ex_5e]

end YolyanComer2026.Examples
