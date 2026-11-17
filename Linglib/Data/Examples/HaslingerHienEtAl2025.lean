module

public import Linglib.Data.Examples.Schema

/-!
# `HaslingerHienEtAl2025` — typed example data

Auto-generated from `Linglib/Data/Examples/HaslingerHienEtAl2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HaslingerHienEtAl2025.Examples`.
-/

@[expose] public section

namespace HaslingerHienEtAl2025.Examples

def ex_71a : Datum :=
  { id := "haslingerhienetal2025_71a"
    source := ⟨"haslinger-etal-2025-nllt", "(71a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A train arrives every ten minutes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "nonOverlap"), ("form", "every")] }

def ex_71b : Datum :=
  { id := "haslingerhienetal2025_71b"
    source := ⟨"haslinger-etal-2025-nllt", "(71b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Alle zehn Minuten kommt ein Zug."
    glossedTokens := [("Alle", "UQ"), ("zehn", "ten"), ("Minuten", "minute.PL"), ("kommt", "come.3SG"), ("ein", "a"), ("Zug.", "train")]
    glossedWords := [⟨['A', 'l', 'l', 'e'], ['U', 'Q'], [⟨['A', 'l', 'l', 'e'], ['U', 'Q'], none⟩]⟩, ⟨['z', 'e', 'h', 'n'], ['t', 'e', 'n'], [⟨['z', 'e', 'h', 'n'], ['t', 'e', 'n'], none⟩]⟩, ⟨['M', 'i', 'n', 'u', 't', 'e', 'n'], ['m', 'i', 'n', 'u', 't', 'e', '.', 'P', 'L'], [⟨['M', 'i', 'n', 'u', 't', 'e', 'n'], ['m', 'i', 'n', 'u', 't', 'e', '.', 'P', 'L'], none⟩]⟩, ⟨['k', 'o', 'm', 'm', 't'], ['c', 'o', 'm', 'e', '.', '3', 'S', 'G'], [⟨['k', 'o', 'm', 'm', 't'], ['c', 'o', 'm', 'e', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 'i', 'n'], ['a'], [⟨['e', 'i', 'n'], ['a'], none⟩]⟩, ⟨['Z', 'u', 'g', '.'], ['t', 'r', 'a', 'i', 'n'], [⟨['Z', 'u', 'g'], ['t', 'r', 'a', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "bare"), ("form", "alle")] }

def ex_73a : Datum :=
  { id := "haslingerhienetal2025_73a"
    source := ⟨"haslinger-etal-2025-nllt", "(73a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "every ten minutes"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "nonOverlap"), ("form", "every")] }

def ex_73b : Datum :=
  { id := "haslingerhienetal2025_73b"
    source := ⟨"haslinger-etal-2025-nllt", "(73b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "each ten minutes"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("structure", "atomic"), ("form", "each")] }

def ex_74a : Datum :=
  { id := "haslingerhienetal2025_74a"
    source := ⟨"haslinger-etal-2025-nllt", "(74a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "alle zehn Minuten"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("structure", "bare"), ("form", "alle")] }

def ex_74b : Datum :=
  { id := "haslingerhienetal2025_74b"
    source := ⟨"haslinger-etal-2025-nllt", "(74b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "jede zehn Minuten"
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("structure", "atomicOnly"), ("form", "jeder")] }

def all : List Datum := [ex_71a, ex_71b, ex_73a, ex_73b, ex_74a, ex_74b]

end HaslingerHienEtAl2025.Examples
