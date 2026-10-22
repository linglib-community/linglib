module

public import Linglib.Data.Examples.Schema

/-!
# `Boskovic2018` — typed example data

Auto-generated from `Linglib/Data/Examples/Boskovic2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Boskovic2018.Examples`.
-/

@[expose] public section

namespace Boskovic2018.Examples

def ex17 : Datum :=
  { id := "boskovic2018_ex17"
    source := ⟨"boskovic-2018", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wonder who friends of hired Mary."
    glossedTokens := []
    context := "Extraction from a subject that has raised from the specifier of vP."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "subjectSubextraction")] }

def ex20 : Datum :=
  { id := "boskovic2018_ex20"
    source := ⟨"boskovic-2018", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kiss Mary Jane did."
    glossedTokens := []
    context := "Remnant vP fronting after the subject has raised out of vP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "remnantFronting")] }

def ex22a : Datum :=
  { id := "boskovic2018_ex22a"
    source := ⟨"boskovic-2018", "(22a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "... weil den Peter mag niemand allgemein bekannt ist."
    glossedTokens := [("weil", "since"), ("den", "the.ACC"), ("Peter", "Peter"), ("mag", "likes"), ("niemand", "nobody.NOM"), ("allgemein", "commonly"), ("bekannt", "known"), ("ist", "is")]
    context := "A verb-second clause moved to Spec,IP."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "v2Moved")] }

def ex22c : Datum :=
  { id := "boskovic2018_ex22c"
    source := ⟨"boskovic-2018", "(22c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie sagte den Peter mag niemand."
    glossedTokens := [("Sie", "she"), ("sagte", "said"), ("den", "the.ACC"), ("Peter", "Peter"), ("mag", "likes"), ("niemand", "nobody.NOM")]
    context := "A verb-second clause in situ."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "v2InSitu")] }

def ex25a : Datum :=
  { id := "boskovic2018_ex25a"
    source := ⟨"boskovic-2018", "(25a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Jovanovu je on sliku vidio."
    glossedTokens := [("Jovanovu", "John's.ACC"), ("je", "is"), ("on", "he"), ("sliku", "picture.ACC"), ("vidio", "seen")]
    context := "A possessor extracted from a fronted object."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "possessorExtraction")] }

def ex42a : Datum :=
  { id := "boskovic2018_ex42a"
    source := ⟨"boskovic-2018", "(42a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Waar had jij dan mee gedacht dat je de vis zou moeten snijden?"
    glossedTokens := [("Waar", "where"), ("had", "had"), ("jij", "you"), ("dan", "then"), ("mee", "with"), ("gedacht", "thought"), ("dat", "that"), ("je", "you"), ("de", "the"), ("vis", "fish"), ("zou", "would"), ("moeten", "must"), ("snijden", "cut")]
    context := "An r-pronoun extracted from a PP moved out of the embedded clause."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "rPronounExtraction")] }

def ex58 : Datum :=
  { id := "boskovic2018_ex58"
    source := ⟨"boskovic-2018", "(58)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was arrested by Mary."
    glossedTokens := []
    context := "Collins's smuggling derivation of the passive: PartP to Spec,VoiceP, then the object out of it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "smugglingPassive")] }

def all : List Datum := [ex17, ex20, ex22a, ex22c, ex25a, ex42a, ex58]

end Boskovic2018.Examples
