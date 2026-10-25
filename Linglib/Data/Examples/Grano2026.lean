module

public import Linglib.Data.Examples.Schema

/-!
# `Grano2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Grano2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Grano2026.Examples`.
-/

@[expose] public section

namespace Grano2026.Examples

def ex_1 : Datum :=
  { id := "grano2026_1"
    source := ⟨"grano-2026", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a book for you to read on the table."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("weakNecessity", .acceptable)]
    paperFeatures := [("modal", "for"), ("determiner", "a"), ("interpretation", "weak")] }

def ex_2_the : Datum :=
  { id := "grano2026_2_the"
    source := ⟨"grano-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book for you to read is on the table."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .unacceptable), ("weakNecessity", .acceptable)]
    paperFeatures := [("modal", "for"), ("determiner", "the"), ("interpretation", "strong")] }

def ex_2_each : Datum :=
  { id := "grano2026_2_each"
    source := ⟨"grano-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each book for you to read is on the table."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .unacceptable), ("weakNecessity", .acceptable)]
    paperFeatures := [("modal", "for"), ("determiner", "each"), ("interpretation", "strong")] }

def ex_2_every : Datum :=
  { id := "grano2026_2_every"
    source := ⟨"grano-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every book for you to read is on the table."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .unacceptable), ("weakNecessity", .acceptable)]
    paperFeatures := [("modal", "for"), ("determiner", "every"), ("interpretation", "strong")] }

def ex_8a : Datum :=
  { id := "grano2026_8a"
    source := ⟨"grano-2026", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... Cats that you could adopt are in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "could"), ("determiner", "bare plural"), ("interpretation", "weak")] }

def ex_8b : Datum :=
  { id := "grano2026_8b"
    source := ⟨"grano-2026", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... There are several cats that you could adopt in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "could"), ("determiner", "several"), ("interpretation", "weak")] }

def ex_8c : Datum :=
  { id := "grano2026_8c"
    source := ⟨"grano-2026", "(8c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... Several cats that you could adopt are in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "could"), ("determiner", "several"), ("interpretation", "either")] }

def ex_8d : Datum :=
  { id := "grano2026_8d"
    source := ⟨"grano-2026", "(8d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... Several of the cats that you could adopt are in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "could"), ("determiner", "several of the"), ("interpretation", "strong")] }

def ex_8e : Datum :=
  { id := "grano2026_8e"
    source := ⟨"grano-2026", "(8e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... Every cat that you could adopt is in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "could"), ("determiner", "every"), ("interpretation", "strong")] }

def ex_9a : Datum :=
  { id := "grano2026_9a"
    source := ⟨"grano-2026", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... Cats that you should adopt are in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "should"), ("determiner", "bare plural"), ("interpretation", "weak")] }

def ex_9b : Datum :=
  { id := "grano2026_9b"
    source := ⟨"grano-2026", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... There are several cats that you should adopt in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "should"), ("determiner", "several"), ("interpretation", "weak")] }

def ex_9c : Datum :=
  { id := "grano2026_9c"
    source := ⟨"grano-2026", "(9c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... Several cats that you should adopt are in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "should"), ("determiner", "several"), ("interpretation", "either")] }

def ex_9d : Datum :=
  { id := "grano2026_9d"
    source := ⟨"grano-2026", "(9d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... Several of the cats that you should adopt are in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "should"), ("determiner", "several of the"), ("interpretation", "strong")] }

def ex_9e : Datum :=
  { id := "grano2026_9e"
    source := ⟨"grano-2026", "(9e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... Every cat that you should adopt is in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "should"), ("determiner", "every"), ("interpretation", "strong")] }

def ex_10a : Datum :=
  { id := "grano2026_10a"
    source := ⟨"grano-2026", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... Cats for you to adopt are in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "for"), ("determiner", "bare plural"), ("interpretation", "weak")] }

def ex_10b : Datum :=
  { id := "grano2026_10b"
    source := ⟨"grano-2026", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... There are several cats for you to adopt in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "for"), ("determiner", "several"), ("interpretation", "weak")] }

def ex_10c : Datum :=
  { id := "grano2026_10c"
    source := ⟨"grano-2026", "(10c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... Several cats for you to adopt are in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .variable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "for"), ("determiner", "several"), ("interpretation", "either")] }

def ex_10d : Datum :=
  { id := "grano2026_10d"
    source := ⟨"grano-2026", "(10d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... Several of the cats for you to adopt are in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "for"), ("determiner", "several of the"), ("interpretation", "strong")] }

def ex_10e : Datum :=
  { id := "grano2026_10e"
    source := ⟨"grano-2026", "(10e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may adopt at most one cat... Every cat for you to adopt is in the next room."
    glossedTokens := []
    context := "At an animal shelter whose policy allows only one cat adoption per family, the speaker says the preamble and one of the continuations."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "for"), ("determiner", "every"), ("interpretation", "strong")] }

def ex_61a : Datum :=
  { id := "grano2026_61a"
    source := ⟨"grano-2026", "(61a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Books for my first grader to read are not heavy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable)]
    paperFeatures := [("modal", "for"), ("determiner", "bare plural"), ("interpretation", "generic")] }

def ex_61b : Datum :=
  { id := "grano2026_61b"
    source := ⟨"grano-2026", "(61b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Snacks for you to eat before dinner are low in calories."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable)]
    paperFeatures := [("modal", "for"), ("determiner", "bare plural"), ("interpretation", "generic")] }

def ex_66_1 : Datum :=
  { id := "grano2026_66_1"
    source := ⟨"grano-2026", "(66)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Always, books for my first grader to read are not heavy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable)]
    paperFeatures := [("modal", "for"), ("determiner", "bare plural"), ("interpretation", "adverb")] }

def ex_66_2 : Datum :=
  { id := "grano2026_66_2"
    source := ⟨"grano-2026", "(66)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In general, books for my first grader to read are not heavy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable)]
    paperFeatures := [("modal", "for"), ("determiner", "bare plural"), ("interpretation", "adverb")] }

def ex_66_3 : Datum :=
  { id := "grano2026_66_3"
    source := ⟨"grano-2026", "(66)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For the most part, books for my first grader to read are not heavy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable)]
    paperFeatures := [("modal", "for"), ("determiner", "bare plural"), ("interpretation", "adverb")] }

def ex_66_4 : Datum :=
  { id := "grano2026_66_4"
    source := ⟨"grano-2026", "(66)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sometimes, books for my first grader to read are not heavy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable)]
    paperFeatures := [("modal", "for"), ("determiner", "bare plural"), ("interpretation", "adverb")] }

def ex_67_the : Datum :=
  { id := "grano2026_67_the"
    source := ⟨"grano-2026", "(67)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book for my first grader to read is not heavy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .unacceptable), ("weakNecessity", .acceptable)]
    paperFeatures := [("modal", "for"), ("determiner", "the"), ("interpretation", "strong")] }

def ex_67_each : Datum :=
  { id := "grano2026_67_each"
    source := ⟨"grano-2026", "(67)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Each book for my first grader to read is not heavy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .unacceptable), ("weakNecessity", .acceptable)]
    paperFeatures := [("modal", "for"), ("determiner", "each"), ("interpretation", "strong")] }

def ex_67_every : Datum :=
  { id := "grano2026_67_every"
    source := ⟨"grano-2026", "(67)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every book for my first grader to read is not heavy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .unacceptable), ("weakNecessity", .acceptable)]
    paperFeatures := [("modal", "for"), ("determiner", "every"), ("interpretation", "strong")] }

def all : List Datum := [ex_1, ex_2_the, ex_2_each, ex_2_every, ex_8a, ex_8b, ex_8c, ex_8d, ex_8e, ex_9a, ex_9b, ex_9c, ex_9d, ex_9e, ex_10a, ex_10b, ex_10c, ex_10d, ex_10e, ex_61a, ex_61b, ex_66_1, ex_66_2, ex_66_3, ex_66_4, ex_67_the, ex_67_each, ex_67_every]

end Grano2026.Examples
