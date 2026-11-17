module

public import Linglib.Data.Examples.Schema

/-!
# `Flemming2021` — typed example data

Auto-generated from `Linglib/Data/Examples/Flemming2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Flemming2021.Examples`.
-/

@[expose] public section

namespace Flemming2021.Examples

def ctx1 : Datum :=
  { id := "flemming2021_ctx1"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "yn bɔt(ə) ʃinˈwaz"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("underlying", "zero"), ("onset", "C"), ("following", "disyllable")] }

def ctx2 : Datum :=
  { id := "flemming2021_ctx2"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "yn bɔt(ə) ˈʒon"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("underlying", "zero"), ("onset", "C"), ("following", "monosyllable")] }

def ctx3 : Datum :=
  { id := "flemming2021_ctx3"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "yn vɛst(ə) ʃinˈwaz"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("underlying", "zero"), ("onset", "CC"), ("following", "disyllable")] }

def ctx4 : Datum :=
  { id := "flemming2021_ctx4"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "yn vɛst(ə) ˈʒon"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("underlying", "zero"), ("onset", "CC"), ("following", "monosyllable")] }

def ctx5 : Datum :=
  { id := "flemming2021_ctx5"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "eva t(ə) ʃɔˈkɛ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("underlying", "schwa"), ("onset", "C"), ("following", "disyllable")] }

def ctx6 : Datum :=
  { id := "flemming2021_ctx6"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "eva t(ə) ˈʃɔk"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("underlying", "schwa"), ("onset", "C"), ("following", "monosyllable")] }

def ctx7 : Datum :=
  { id := "flemming2021_ctx7"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "mɔʁiz t(ə) siˈtɛ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("underlying", "schwa"), ("onset", "CC"), ("following", "disyllable")] }

def ctx8 : Datum :=
  { id := "flemming2021_ctx8"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "mɔʁiz t(ə) ˈsit"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("underlying", "schwa"), ("onset", "CC"), ("following", "monosyllable")] }

def all : List Datum := [ctx1, ctx2, ctx3, ctx4, ctx5, ctx6, ctx7, ctx8]

end Flemming2021.Examples
