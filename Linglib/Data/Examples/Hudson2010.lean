module

public import Linglib.Data.Examples.Schema

/-!
# `Hudson2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Hudson2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hudson2010.Examples`.
-/

@[expose] public section

namespace Hudson2010.Examples

def ch7_11 : Datum :=
  { id := "hudson2010_ch7_11"
    source := ⟨"hudson-2010", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He has swum."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.2.6"), ("triangle", "he is the subject of has and of swum"), ("verb", "HAVE")] }

def ch7_12 : Datum :=
  { id := "hudson2010_ch7_12"
    source := ⟨"hudson-2010", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There was an accident."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.2.6"), ("subject", "meaningless there"), ("verb", "BE")] }

def ch7_13 : Datum :=
  { id := "hudson2010_ch7_13"
    source := ⟨"hudson-2010", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Was there an accident?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.2.6"), ("subject", "there"), ("construction", "inversion test for subjecthood")] }

def ch7_14 : Datum :=
  { id := "hudson2010_ch7_14"
    source := ⟨"hudson-2010", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There has been an accident."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.2.6"), ("triangle", "there is the subject of has and of been"), ("verb", "HAVE")] }

def ch7_8 : Datum :=
  { id := "hudson2010_ch7_8"
    source := ⟨"hudson-2010", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He keeps talking."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.4.4"), ("triangle", "he is the subject of keeps and of talking"), ("landmark", "keeps")] }

def ch7_9 : Datum :=
  { id := "hudson2010_ch7_9"
    source := ⟨"hudson-2010", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Keeps he talking."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.4.4"), ("landmark", "talking"), ("rule", "a verb's subject stands just before it")] }

def ch7_10 : Datum :=
  { id := "hudson2010_ch7_10"
    source := ⟨"hudson-2010", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He never keeps talking."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.4.4"), ("adverb", "never between the subject and its landmark verb")] }

def ch7_11b : Datum :=
  { id := "hudson2010_ch7_11b"
    source := ⟨"hudson-2010", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He keeps never talking."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.4.4"), ("adverb", "never between the subject and the lower verb")] }

def fig7_12 : Datum :=
  { id := "hudson2010_fig7_12"
    source := ⟨"hudson-2010", "Figure 7.12"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He keeps seeming to have forgotten to go."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7.4.5"), ("triangle", "he is the subject of every verb in the valent chain"), ("recursion", "triangles multiplied freely")] }

def all : List Datum := [ch7_11, ch7_12, ch7_13, ch7_14, ch7_8, ch7_9, ch7_10, ch7_11b, fig7_12]

end Hudson2010.Examples
