module

public import Linglib.Data.Examples.Schema

/-!
# `Kalin2018` — typed example data

Auto-generated from `Linglib/Data/Examples/Kalin2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kalin2018.Examples`.
-/

@[expose] public section

namespace Kalin2018.Examples

def ex_8a : Datum :=
  { id := "kalin2018_8a"
    source := ⟨"kalin-2018", "(8a)"⟩
    reportedIn := none
    language := "sena1268"
    primaryText := "Xa ksūta lapl-ā."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "imperfective"), ("object", "none"), ("subject_suffix", "S"), ("object_suffix", "none")] }

def ex_9a : Datum :=
  { id := "kalin2018_9a"
    source := ⟨"kalin-2018", "(9a)"⟩
    reportedIn := none
    language := "sena1268"
    primaryText := "Xa ksūta mpel-ā."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "perfective"), ("object", "none"), ("subject_suffix", "L"), ("object_suffix", "none")] }

def ex_9b : Datum :=
  { id := "kalin2018_9b"
    source := ⟨"kalin-2018", "(9b)"⟩
    reportedIn := none
    language := "sena1268"
    primaryText := "Āyet ksū-wā-lox."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "perfective"), ("object", "none"), ("subject_suffix", "L"), ("object_suffix", "none")] }

def ex_10a : Datum :=
  { id := "kalin2018_10a"
    source := ⟨"kalin-2018", "(10a)"⟩
    reportedIn := none
    language := "sena1268"
    primaryText := "Āna (xa) ksūta xazy-an-ā."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "imperfective"), ("object", "specific"), ("subject_suffix", "S"), ("object_suffix", "L")] }

def ex_10b : Datum :=
  { id := "kalin2018_10b"
    source := ⟨"kalin-2018", "(10b)"⟩
    reportedIn := none
    language := "sena1268"
    primaryText := "Āna ō ksūta kasw-an-ā."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "imperfective"), ("object", "specific"), ("subject_suffix", "S"), ("object_suffix", "L")] }

def ex_10c : Datum :=
  { id := "kalin2018_10c"
    source := ⟨"kalin-2018", "(10c)"⟩
    reportedIn := none
    language := "sena1268"
    primaryText := "Pōles kod yōma baxt-ē nāsheq-∅-lā."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "imperfective"), ("object", "specific"), ("subject_suffix", "S"), ("object_suffix", "L")] }

def ex_11a : Datum :=
  { id := "kalin2018_11a"
    source := ⟨"kalin-2018", "(11a)"⟩
    reportedIn := none
    language := "sena1268"
    primaryText := "Āna (xa) ksūta kasw-an."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "imperfective"), ("object", "nonspecific"), ("subject_suffix", "S"), ("object_suffix", "none")] }

def ex_11b : Datum :=
  { id := "kalin2018_11b"
    source := ⟨"kalin-2018", "(11b)"⟩
    reportedIn := none
    language := "sena1268"
    primaryText := "Āna kod yōma yāle xazy-an."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "imperfective"), ("object", "nonspecific"), ("subject_suffix", "S"), ("object_suffix", "none")] }

def ex_12a : Datum :=
  { id := "kalin2018_12a"
    source := ⟨"kalin-2018", "(12a)"⟩
    reportedIn := none
    language := "sena1268"
    primaryText := "Axnī ō ksūta ksū-lan."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "perfective"), ("object", "specific"), ("subject_suffix", "L"), ("object_suffix", "none")] }

def ex_12c : Datum :=
  { id := "kalin2018_12c"
    source := ⟨"kalin-2018", "(12c)"⟩
    reportedIn := none
    language := "sena1268"
    primaryText := "Axnī xa ksūta ksū-lan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("aspect", "perfective"), ("object", "nonspecific"), ("subject_suffix", "L"), ("object_suffix", "none")] }

def ex_38 : Datum :=
  { id := "kalin2018_38"
    source := ⟨"kalin-2018", "(38)"⟩
    reportedIn := none
    language := "sena1268"
    primaryText := "Axnī ō ksūta kasw-ox-lā."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1"), ("aspect", "imperfective"), ("object", "specific"), ("subject_suffix", "S"), ("object_suffix", "L")] }

def all : List Datum := [ex_8a, ex_9a, ex_9b, ex_10a, ex_10b, ex_10c, ex_11a, ex_11b, ex_12a, ex_12c, ex_38]

end Kalin2018.Examples
