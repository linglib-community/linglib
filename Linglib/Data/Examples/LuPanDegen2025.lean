module

public import Linglib.Data.Examples.Schema

/-!
# `LuPanDegen2025` — typed example data

Auto-generated from `Linglib/Data/Examples/LuPanDegen2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace LuPanDegen2025.Examples`.
-/

@[expose] public section

namespace LuPanDegen2025.Examples

def exp1_verbfocus : Datum :=
  { id := "lupandegen2025_exp1_verbfocus"
    source := ⟨"lu-pan-degen-2025", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't WHISPER that Mary met with the lawyer. Then who did John whisper that Mary met with?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1"), ("focus_condition", "verbFocus"), ("verb_type", "mos")] }

def exp1_embeddedfocus : Datum :=
  { id := "lupandegen2025_exp1_embeddedfocus"
    source := ⟨"lu-pan-degen-2025", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't whisper that Mary met with the LAWYER. Then who did John whisper that Mary met with?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1"), ("focus_condition", "embeddedFocus"), ("verb_type", "mos")] }

def exp2a_say_verbfocus : Datum :=
  { id := "lupandegen2025_exp2a_say_verbfocus"
    source := ⟨"lu-pan-degen-2025", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't SAY that Mary met with the lawyer. Then who did John say that Mary met with?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "2a"), ("focus_condition", "verbFocus"), ("verb_type", "say")] }

def exp2a_say_embeddedfocus : Datum :=
  { id := "lupandegen2025_exp2a_say_embeddedfocus"
    source := ⟨"lu-pan-degen-2025", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't say that Mary met with the LAWYER. Then who did John say that Mary met with?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "2a"), ("focus_condition", "embeddedFocus"), ("verb_type", "say")] }

def exp3a_say : Datum :=
  { id := "lupandegen2025_exp3a_say"
    source := ⟨"lu-pan-degen-2025", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't say that Mary met with the lawyer. Then who did John say that Mary met with?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "3a"), ("focus_condition", "none"), ("verb_type", "say")] }

def exp3a_sayadverb : Datum :=
  { id := "lupandegen2025_exp3a_sayadverb"
    source := ⟨"lu-pan-degen-2025", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't say softly that Mary met with the lawyer. Then who did John say softly that Mary met with?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "3a"), ("focus_condition", "none"), ("verb_type", "sayAdverb")] }

def exp3b_adverbfocus : Datum :=
  { id := "lupandegen2025_exp3b_adverbfocus"
    source := ⟨"lu-pan-degen-2025", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't say SOFTLY that Mary met with the lawyer. Then who did John say softly that Mary met with?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "3b"), ("focus_condition", "adverbFocus"), ("verb_type", "sayAdverb")] }

def exp3b_embeddedfocus : Datum :=
  { id := "lupandegen2025_exp3b_embeddedfocus"
    source := ⟨"lu-pan-degen-2025", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't say softly that Mary met with the LAWYER. Then who did John say softly that Mary met with?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "3b"), ("focus_condition", "embeddedFocus"), ("verb_type", "sayAdverb")] }

def all : List Datum := [exp1_verbfocus, exp1_embeddedfocus, exp2a_say_verbfocus, exp2a_say_embeddedfocus, exp3a_say, exp3a_sayadverb, exp3b_adverbfocus, exp3b_embeddedfocus]

end LuPanDegen2025.Examples
