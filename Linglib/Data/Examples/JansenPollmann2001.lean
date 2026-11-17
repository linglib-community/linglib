module

public import Linglib.Data.Examples.Schema

/-!
# `JansenPollmann2001` — typed example data

Auto-generated from `Linglib/Data/Examples/JansenPollmann2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace JansenPollmann2001.Examples`.
-/

@[expose] public section

namespace JansenPollmann2001.Examples

def pair_5_6 : Datum :=
  { id := "jansenpollmann2001_pair_5_6"
    source := ⟨"jansen-pollmann-2001", "p. 195"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "about 5 or 6 books"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pair"), ("first", "5"), ("second", "6")] }

def pair_10_12 : Datum :=
  { id := "jansenpollmann2001_pair_10_12"
    source := ⟨"jansen-pollmann-2001", "p. 195"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "about 10 or 12 articles"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pair"), ("first", "10"), ("second", "12")] }

def pair_20_25 : Datum :=
  { id := "jansenpollmann2001_pair_20_25"
    source := ⟨"jansen-pollmann-2001", "p. 195"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "about 20 or 25 papers"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pair"), ("first", "20"), ("second", "25")] }

def pair_10_13 : Datum :=
  { id := "jansenpollmann2001_pair_10_13"
    source := ⟨"jansen-pollmann-2001", "p. 195"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "about 10 or 13 grandparents"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pair"), ("first", "10"), ("second", "13")] }

def pair_80_91 : Datum :=
  { id := "jansenpollmann2001_pair_80_91"
    source := ⟨"jansen-pollmann-2001", "p. 195"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "about 80 or 91 grandchildren"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pair"), ("first", "80"), ("second", "91")] }

def pair_350_300 : Datum :=
  { id := "jansenpollmann2001_pair_350_300"
    source := ⟨"jansen-pollmann-2001", "pp. 195-196"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "about 350 or 300 presents"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "pair"), ("first", "350"), ("second", "300")] }

def all : List Datum := [pair_5_6, pair_10_12, pair_20_25, pair_10_13, pair_80_91, pair_350_300]

end JansenPollmann2001.Examples
