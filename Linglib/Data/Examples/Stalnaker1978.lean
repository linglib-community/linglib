module

public import Linglib.Data.Examples.Schema

/-!
# `Stalnaker1978` — typed example data

Auto-generated from `Linglib/Data/Examples/Stalnaker1978.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Stalnaker1978.Examples`.
-/

@[expose] public section

namespace Stalnaker1978.Examples

def fool : Datum :=
  { id := "stalnaker1978_fool"
    source := ⟨"stalnaker-1978", "p. 317"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You are a fool."
    glossedTokens := []
    context := "Said to O'Leary, who is a fool. Daniels, who is no fool, is standing nearby and thinks he is the one addressed."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def meter : Datum :=
  { id := "stalnaker1978_meter"
    source := ⟨"stalnaker-1978", "p. 321"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This bar is one meter long."
    glossedTokens := []
    context := "Said by an authority fixing the reference of 'one meter' by means of a certain metal bar."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def holmes : Datum :=
  { id := "stalnaker1978_holmes"
    source := ⟨"stalnaker-1978", "p. 330"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sherlock Holmes does not exist."
    glossedTokens := []
    context := "Said in the actual world by a speaker who has heard three rumors about the origin of the Sherlock Holmes stories and does not know which is true."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def all : List Datum := [fool, meter, holmes]

end Stalnaker1978.Examples
