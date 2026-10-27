module

public import Linglib.Data.Examples.Schema

/-!
# `Ferreira2016` — typed example data

Auto-generated from `Linglib/Data/Examples/Ferreira2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ferreira2016.Examples`.
-/

@[expose] public section

namespace Ferreira2016.Examples

def ex45 : Datum :=
  { id := "ferreira2016_ex45"
    source := ⟨"ferreira-2016", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was crossing the street."
    glossedTokens := []
    context := "John started walking toward the other side of the street, but a bus hit him and he never actually made it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def ex46 : Datum :=
  { id := "ferreira2016_ex46"
    source := ⟨"ferreira-2016", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was crossing the Atlantic (when a shark killed him)."
    glossedTokens := []
    context := "Uttered half an hour after John, a normal human being, started swimming from the west coast of Africa towards the Brazilian coast."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "false")] }

def ex54 : Datum :=
  { id := "ferreira2016_ex54"
    source := ⟨"ferreira-2016", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John plays soccer (regularly)."
    glossedTokens := []
    context := "John, who loves soccer, does not live far from a local college campus where the only soccer field in the neighborhood is located, and goes there regularly to play with his friends."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def ex54_accident : Datum :=
  { id := "ferreira2016_ex54_accident"
    source := ⟨"ferreira-2016", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John plays soccer (regularly)."
    glossedTokens := []
    context := "Due to a tragic car accident, John cannot control the movements of his legs anymore, and the sentence is uttered after these facts became known to the speaker."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "false")] }

def all : List Datum := [ex45, ex46, ex54, ex54_accident]

end Ferreira2016.Examples
