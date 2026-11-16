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
    glossedWords := [⟨['R', 'a', 'a'], ['s', 'e', 'e'], [⟨['R', 'a', 'a'], ['s', 'e', 'e'], none⟩]⟩, ⟨['n', 'o'], ['h', 'o', 'w'], [⟨['n', 'o'], ['h', 'o', 'w'], none⟩]⟩, ⟨['n', 'd', 'e', 'f', '-', 'i', 'r', '-', 'a', 'y', '-', 'm', 'i', '-', 'n', 'd', 'i'], ['c', 'o', 'o', 'k', '-', 'E', 'X', 'T', '-', 'I', 'N', 'C', '-', 'I', '-', 'i', 't'], [⟨['n', 'd', 'e', 'f'], ['c', 'o', 'o', 'k'], none⟩, ⟨['i', 'r'], ['E', 'X', 'T'], some '-'⟩, ⟨['a', 'y'], ['I', 'N', 'C'], some '-'⟩, ⟨['m', 'i'], ['I'], some '-'⟩, ⟨['n', 'd', 'i'], ['i', 't'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
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
    glossedWords := [⟨['W', 'a', 'l', 'a', 'a'], ['i', 's', '.', 'N', 'E', 'G'], [⟨['W', 'a', 'l', 'a', 'a'], ['i', 's', '.', 'N', 'E', 'G'], none⟩]⟩, ⟨['t', 'o'], ['w', 'h', 'e', 'r', 'e'], [⟨['t', 'o'], ['w', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['n', 'd', 'u', 'r', '-', 'o', 't', '-', 'o', 'n', '-', 'ɗ', 'i'], ['g', 'r', 'a', 'z', 'e', '-', 'I', 'N', 'C', '-', 'y', 'o', 'u', '-', 't', 'h', 'e', 'm'], [⟨['n', 'd', 'u', 'r'], ['g', 'r', 'a', 'z', 'e'], none⟩, ⟨['o', 't'], ['I', 'N', 'C'], some '-'⟩, ⟨['o', 'n'], ['y', 'o', 'u'], some '-'⟩, ⟨['ɗ', 'i'], ['t', 'h', 'e', 'm'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
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
