module

public import Linglib.Data.Examples.Schema

/-!
# `Jardine2016b` — typed example data

Auto-generated from `Linglib/Data/Examples/Jardine2016b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Jardine2016b.Examples`.
-/

@[expose] public section

namespace Jardine2016b.Examples

def ex_7_5_pa : Datum :=
  { id := "jardine2016b_7_5_pa"
    source := ⟨"jardine-2016b", "(7.5)"⟩
    reportedIn := none
    language := ""
    primaryText := "pa → pa"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.1"), ("input", "pa"), ("output", "pa"), ("in_rvoice", "yes")] }

def ex_7_5_aaa : Datum :=
  { id := "jardine2016b_7_5_aaa"
    source := ⟨"jardine-2016b", "(7.5)"⟩
    reportedIn := none
    language := ""
    primaryText := "aaa → aaa"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.1"), ("input", "aaa"), ("output", "aaa"), ("in_rvoice", "yes")] }

def ex_7_5_apa : Datum :=
  { id := "jardine2016b_7_5_apa"
    source := ⟨"jardine-2016b", "(7.5)"⟩
    reportedIn := none
    language := ""
    primaryText := "apa → aba"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.1"), ("input", "apa"), ("output", "aba"), ("in_rvoice", "yes")] }

def ex_7_5_aba : Datum :=
  { id := "jardine2016b_7_5_aba"
    source := ⟨"jardine-2016b", "(7.5)"⟩
    reportedIn := none
    language := ""
    primaryText := "aba → aba"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.1"), ("input", "aba"), ("output", "aba"), ("in_rvoice", "yes")] }

def ex_7_5_appa : Datum :=
  { id := "jardine2016b_7_5_appa"
    source := ⟨"jardine-2016b", "(7.5)"⟩
    reportedIn := none
    language := ""
    primaryText := "appa → appa"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.1"), ("input", "appa"), ("output", "appa"), ("in_rvoice", "yes")] }

def ex_7_5_aapaaapa : Datum :=
  { id := "jardine2016b_7_5_aapaaapa"
    source := ⟨"jardine-2016b", "(7.5)"⟩
    reportedIn := none
    language := ""
    primaryText := "aapaaapa → aabaaaba"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.1"), ("input", "aapaaapa"), ("output", "aabaaaba"), ("in_rvoice", "yes")] }

def ex_7_17_pa_ba : Datum :=
  { id := "jardine2016b_7_17_pa_ba"
    source := ⟨"jardine-2016b", "(7.17)"⟩
    reportedIn := none
    language := ""
    primaryText := "pa → ba"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.2"), ("input", "pa"), ("output", "ba"), ("in_rvoice", "no")] }

def ex_7_17_apa_apa : Datum :=
  { id := "jardine2016b_7_17_apa_apa"
    source := ⟨"jardine-2016b", "(7.17)"⟩
    reportedIn := none
    language := ""
    primaryText := "apa → apa"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.2"), ("input", "apa"), ("output", "apa"), ("in_rvoice", "no")] }

def ex_7_17_appa_abpa : Datum :=
  { id := "jardine2016b_7_17_appa_abpa"
    source := ⟨"jardine-2016b", "(7.17)"⟩
    reportedIn := none
    language := ""
    primaryText := "appa → abpa"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.2"), ("input", "appa"), ("output", "abpa"), ("in_rvoice", "no")] }

def all : List Datum := [ex_7_5_pa, ex_7_5_aaa, ex_7_5_apa, ex_7_5_aba, ex_7_5_appa, ex_7_5_aapaaapa, ex_7_17_pa_ba, ex_7_17_apa_apa, ex_7_17_appa_abpa]

end Jardine2016b.Examples
