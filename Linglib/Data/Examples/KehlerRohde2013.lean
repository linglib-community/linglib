module

public import Linglib.Data.Examples.Schema

/-!
# `KehlerRohde2013` — typed example data

Auto-generated from `Linglib/Data/Examples/KehlerRohde2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace KehlerRohde2013.Examples`.
-/

@[expose] public section

namespace KehlerRohde2013.Examples

def ex_7 : Datum :=
  { id := "kehlerrohde2013_7"
    source := ⟨"kehler-rohde-2013", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John passed a comic to Bill. He"
    glossedTokens := []
    context := "Passage completion after a Source-Goal transfer-of-possession context with a pronoun prompt; the continuation's first mention is coded for its referent (Rohde, Kehler & Elman 2006)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_8 : Datum :=
  { id := "kehlerrohde2013_8"
    source := ⟨"kehler-rohde-2013", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was passing a comic to Bill. He"
    glossedTokens := []
    context := "Passage completion after a Source-Goal transfer-of-possession context with a pronoun prompt; the continuation's first mention is coded for its referent (Rohde, Kehler & Elman 2006)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_10a : Datum :=
  { id := "kehlerrohde2013_10a"
    source := ⟨"kehler-rohde-2013", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John passed the comic to Bill. He"
    glossedTokens := []
    context := "Passage completion after a Source-Goal transfer-of-possession context with a pronoun prompt: the pronoun prompt condition of Stevenson et al. (1994), paired with the no-pronoun prompt (10b) in Rohde & Kehler (2008)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_10b : Datum :=
  { id := "kehlerrohde2013_10b"
    source := ⟨"kehler-rohde-2013", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John passed the comic to Bill."
    glossedTokens := []
    context := "Passage completion after a Source-Goal transfer context, with or without a pronoun prompt; continuations coded for coherence relation and first-mentioned referent (Rohde & Kehler 2008)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_20a : Datum :=
  { id := "kehlerrohde2013_20a"
    source := ⟨"kehler-rohde-2013", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Amanda amazed Brittany. She"
    glossedTokens := []
    context := "Passage completion after a subject-biased implicit-causality context in the active or passive voice, with or without a pronoun prompt (Rohde & Kehler 2009, 2013)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_20c : Datum :=
  { id := "kehlerrohde2013_20c"
    source := ⟨"kehler-rohde-2013", "(20c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Amanda amazed Brittany."
    glossedTokens := []
    context := "Passage completion after a subject-biased implicit-causality context in the active or passive voice, with or without a pronoun prompt (Rohde & Kehler 2009, 2013)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_20b : Datum :=
  { id := "kehlerrohde2013_20b"
    source := ⟨"kehler-rohde-2013", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Brittany was amazed by Amanda. She"
    glossedTokens := []
    context := "Passage completion after a subject-biased implicit-causality context in the active or passive voice, with or without a pronoun prompt (Rohde & Kehler 2009, 2013)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_20d : Datum :=
  { id := "kehlerrohde2013_20d"
    source := ⟨"kehler-rohde-2013", "(20d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Brittany was amazed by Amanda."
    glossedTokens := []
    context := "Passage completion after a subject-biased implicit-causality context in the active or passive voice, with or without a pronoun prompt (Rohde & Kehler 2009, 2013)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_7, ex_8, ex_10a, ex_10b, ex_20a, ex_20c, ex_20b, ex_20d]

end KehlerRohde2013.Examples
