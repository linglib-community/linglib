module

public import Linglib.Data.Examples.Schema

/-!
# `Svenonius2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Svenonius2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Svenonius2026.Examples`.
-/

@[expose] public section

namespace Svenonius2026.Examples

def ex13a : Datum :=
  { id := "svenonius2026_ex13a"
    source := ⟨"mcintosh-1982", ""⟩
    reportedIn := some ⟨"svenonius-2026", "(13a)"⟩
    language := "adam1253"
    primaryText := "Raa no ndef-ir-ay-mi-ndi."
    glossedTokens := [("Raa", "see"), ("no", "how"), ("ndef-ir-ay-mi-ndi", "cook-EXT-INC-I-it")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "27.3.2"), ("phenomenon", "outwardSensitivePCSA"), ("allomorph", "ay"), ("environment", "elsewhere")] }

def ex13b : Datum :=
  { id := "svenonius2026_ex13b"
    source := ⟨"mcintosh-1982", "p. 211"⟩
    reportedIn := some ⟨"svenonius-2026", "(13b)"⟩
    language := "adam1253"
    primaryText := "Walaa to ndur-ot-on-ɗi."
    glossedTokens := [("Walaa", "is.NEG"), ("to", "where"), ("ndur-ot-on-ɗi", "graze-INC-you-them")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "27.3.2"), ("phenomenon", "outwardSensitivePCSA"), ("allomorph", "ot"), ("environment", "prevocalic")] }

def fn7return : Datum :=
  { id := "svenonius2026_fn7return"
    source := ⟨"van-driem-1987", "p. 385"⟩
    reportedIn := some ⟨"svenonius-2026", "fn. 7"⟩
    language := "limb1266"
    primaryText := "nuːŋ-s-i-ge~nuːks-i-ge"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "27.3.2"), ("phenomenon", "outwardSensitivePCSA"), ("elsewhereForm", "nuːŋ"), ("prevocalicForm", "nuːks")] }

def fn7live : Datum :=
  { id := "svenonius2026_fn7live"
    source := ⟨"van-driem-1987", "p. 385"⟩
    reportedIn := some ⟨"svenonius-2026", "fn. 7"⟩
    language := "limb1266"
    primaryText := "hiŋ-s-i-ge~hiŋ-i-ge"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "27.3.2"), ("phenomenon", "outwardSensitivePCSA"), ("elsewhereForm", "hiŋ"), ("prevocalicForm", "hiŋ")] }

def all : List Datum := [ex13a, ex13b, fn7return, fn7live]

end Svenonius2026.Examples
