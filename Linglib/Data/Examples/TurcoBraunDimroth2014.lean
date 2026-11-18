module

public import Linglib.Data.Examples.Schema

/-!
# `TurcoBraunDimroth2014` — typed example data

Auto-generated from `Linglib/Data/Examples/TurcoBraunDimroth2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TurcoBraunDimroth2014.Examples`.
-/

@[expose] public section

namespace TurcoBraunDimroth2014.Examples

def ex_1A : Datum :=
  { id := "turcobraundimroth2014_1A"
    source := ⟨"turco-braun-dimroth-2014", "(1) A"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Auf meinem Bild hat das Kind nicht geweint."
    glossedTokens := []
    context := "Polarity contrast: speaker A describes their own picture; B will describe a different picture."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "contrast"), ("polarity", "negative"), ("turn", "A")] }

def ex_1B1 : Datum :=
  { id := "turcobraundimroth2014_1B1"
    source := ⟨"turco-braun-dimroth-2014", "(1) B1"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Auf meinem Bild HAT das Kind geweint."
    glossedTokens := []
    context := "Reply to (1) A about a different picture."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "contrast"), ("polarity", "positive"), ("marking", "verumFocus")] }

def ex_1B2 : Datum :=
  { id := "turcobraundimroth2014_1B2"
    source := ⟨"turco-braun-dimroth-2014", "(1) B2"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Auf meinem Bild hat das Kind SCHON/WOHL geweint."
    glossedTokens := []
    context := "Reply to (1) A about a different picture."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "contrast"), ("polarity", "positive"), ("marking", "particle")] }

def ex_2A : Datum :=
  { id := "turcobraundimroth2014_2A"
    source := ⟨"turco-braun-dimroth-2014", "(2) A"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Kind hat nicht geweint."
    glossedTokens := []
    context := "Polarity correction: A and B talk about the same situation."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "correction"), ("polarity", "negative"), ("turn", "A")] }

def ex_2B1 : Datum :=
  { id := "turcobraundimroth2014_2B1"
    source := ⟨"turco-braun-dimroth-2014", "(2) B1"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Kind HAT geweint."
    glossedTokens := []
    context := "Reply to (2) A about the same situation."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "correction"), ("polarity", "positive"), ("marking", "verumFocus")] }

def ex_2B2 : Datum :=
  { id := "turcobraundimroth2014_2B2"
    source := ⟨"turco-braun-dimroth-2014", "(2) B2"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Kind hat SCHON/WOHL geweint."
    glossedTokens := []
    context := "Reply to (2) A about the same situation."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "correction"), ("polarity", "positive"), ("marking", "particle")] }

def ex_3 : Datum :=
  { id := "turcobraundimroth2014_3"
    source := ⟨"turco-braun-dimroth-2014", "(3)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Meneer Rood durft niet te springen. Meneer Blauw is WEL gesprongen want het vuur stond inmiddels ook al in zijn kamer."
    glossedTokens := []
    context := "A house is on fire; a native speaker of Dutch retells the Finite Story film."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "contrast"), ("polarity", "positive"), ("marking", "particle"), ("genre", "monologue")] }

def vf_negated : Datum :=
  { id := "turcobraundimroth2014_vf_negated"
    source := ⟨"turco-braun-dimroth-2014", "section 4"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Kind HAT nicht geweint."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("marking", "verumFocus")] }

def wel_negated : Datum :=
  { id := "turcobraundimroth2014_wel_negated"
    source := ⟨"turco-braun-dimroth-2014", "section 4"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Het kind heeft wel niet gehuild."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("marking", "particle")] }

def all : List Datum := [ex_1A, ex_1B1, ex_1B2, ex_2A, ex_2B1, ex_2B2, ex_3, vf_negated, wel_negated]

end TurcoBraunDimroth2014.Examples
