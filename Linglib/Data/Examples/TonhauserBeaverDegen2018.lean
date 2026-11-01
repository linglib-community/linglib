module

public import Linglib.Data.Examples.Schema

/-!
# `TonhauserBeaverDegen2018` — typed example data

Auto-generated from `Linglib/Data/Examples/TonhauserBeaverDegen2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TonhauserBeaverDegen2018.Examples`.
-/

@[expose] public section

namespace TonhauserBeaverDegen2018.Examples

def tbd2018_1a_nrrc : Datum :=
  { id := "tbd2018_1a_nrrc"
    source := ⟨"tonhauser-beaver-degen-2018", "(12), Exp 1a materials, target expression / projective content pairs"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These muffins, which have blueberries in them, are gluten-free and low-fat."
    glossedTokens := []
    context := "Projective content: 'These muffins have blueberries in them.'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "NRRC")] }

def tbd2018_1a_nominalAppositive : Datum :=
  { id := "tbd2018_1a_nominalAppositive"
    source := ⟨"tonhauser-beaver-degen-2018", "(12), Exp 1a materials, target expression / projective content pairs"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Martha's new car, a BMW, was expensive."
    glossedTokens := []
    context := "Projective content: 'Martha's new car is a BMW'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "nominalAppositive")] }

def tbd2018_1a_possessiveNP : Datum :=
  { id := "tbd2018_1a_possessiveNP"
    source := ⟨"tonhauser-beaver-degen-2018", "(12), Exp 1a materials, target expression / projective content pairs"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Martha's new BMW was expensive."
    glossedTokens := []
    context := "Projective content: 'Martha's new car is a BMW'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "possessiveNP")] }

def tbd2018_1a_annoyed : Datum :=
  { id := "tbd2018_1a_annoyed"
    source := ⟨"tonhauser-beaver-degen-2018", "(12), Exp 1a materials, target expression / projective content pairs"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Martha's neighbor is annoyed that Martha has a new BMW."
    glossedTokens := []
    context := "Projective content: 'Martha has a new BMW.'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "annoyed")] }

def tbd2018_1a_discover : Datum :=
  { id := "tbd2018_1a_discover"
    source := ⟨"tonhauser-beaver-degen-2018", "(12), Exp 1a materials, target expression / projective content pairs"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary discovered that her daughter has been biting her nails."
    glossedTokens := []
    context := "Projective content: 'Mary's daughter has been biting her nails'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "discover")] }

def tbd2018_1a_know : Datum :=
  { id := "tbd2018_1a_know"
    source := ⟨"tonhauser-beaver-degen-2018", "(12), Exp 1a materials, target expression / projective content pairs"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Billy knows that Martha has a new BMW."
    glossedTokens := []
    context := "Projective content: 'Martha has a new BMW.'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "know")] }

def tbd2018_1a_only : Datum :=
  { id := "tbd2018_1a_only"
    source := ⟨"tonhauser-beaver-degen-2018", "(12), Exp 1a materials, target expression / projective content pairs"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "These muffins only have blueberries in them."
    glossedTokens := []
    context := "Projective content: 'These muffins have blueberries in them.'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "only")] }

def tbd2018_1a_stop : Datum :=
  { id := "tbd2018_1a_stop"
    source := ⟨"tonhauser-beaver-degen-2018", "(12), Exp 1a materials, target expression / projective content pairs"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary's daughter stopped biting her nails."
    glossedTokens := []
    context := "Projective content: 'Mary's daughter has been biting her nails'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "stop")] }

def tbd2018_1a_stupid : Datum :=
  { id := "tbd2018_1a_stupid"
    source := ⟨"tonhauser-beaver-degen-2018", "(12), Exp 1a materials, target expression / projective content pairs"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary's daughter is stupid to be biting her nails."
    glossedTokens := []
    context := "Projective content: 'Mary's daughter has been biting her nails'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "stupid")] }

def tbd2018_1a_sampleTarget_nominalAppositive : Datum :=
  { id := "tbd2018_1a_sampleTarget_nominalAppositive"
    source := ⟨"tonhauser-beaver-degen-2018", "(14a), Exp 1a materials, sample target stimulus"⟩
    reportedIn := none
    method := some .experiment
    language := "stan1293"
    primaryText := "Ronald asks: Did Richie, a stuntman, break his leg?"
    glossedTokens := []
    context := "Projective content: 'Richie is a stuntman'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "nominal appositive")] }

def tbd2018_1a_sampleTarget_beStupidTo : Datum :=
  { id := "tbd2018_1a_sampleTarget_beStupidTo"
    source := ⟨"tonhauser-beaver-degen-2018", "(14b), Exp 1a materials, sample target stimulus"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Linda asks: Is Richie stupid to be a stuntman?"
    glossedTokens := []
    context := "Projective content: 'Richie is a stuntman'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "be stupid to")] }

def tbd2018_1a_control : Datum :=
  { id := "tbd2018_1a_control"
    source := ⟨"tonhauser-beaver-degen-2018", "(15), Exp 1a materials, sample control stimulus"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan asks: Is Richie a stuntman?"
    glossedTokens := []
    context := "Main-clause control: the content 'Richie is a stuntman' is at-issue and not projective."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "main clause")] }

def tbd2018_1b_sample_aware : Datum :=
  { id := "tbd2018_1b_sample_aware"
    source := ⟨"tonhauser-beaver-degen-2018", "(16a), Exp 1b materials, sample target stimuli"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily asks: Is Shirley aware that Raul was drinking chamomile tea?"
    glossedTokens := []
    context := "Projective content: 'Raul was drinking chamomile tea'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "be aware")] }

def tbd2018_1b_sample_discover : Datum :=
  { id := "tbd2018_1b_sample_discover"
    source := ⟨"tonhauser-beaver-degen-2018", "(16b), Exp 1b materials, sample target stimuli"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Gary asks: Did Samuel discover that Raul was drinking chamomile tea?"
    glossedTokens := []
    context := "Projective content: 'Raul was drinking chamomile tea'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("expression", "discover")] }

def all : List Datum := [tbd2018_1a_nrrc, tbd2018_1a_nominalAppositive, tbd2018_1a_possessiveNP, tbd2018_1a_annoyed, tbd2018_1a_discover, tbd2018_1a_know, tbd2018_1a_only, tbd2018_1a_stop, tbd2018_1a_stupid, tbd2018_1a_sampleTarget_nominalAppositive, tbd2018_1a_sampleTarget_beStupidTo, tbd2018_1a_control, tbd2018_1b_sample_aware, tbd2018_1b_sample_discover]

end TonhauserBeaverDegen2018.Examples
