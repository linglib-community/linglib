module

public import Linglib.Data.Examples.Schema

/-!
# `Svenonius2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Svenonius2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Svenonius2004.Examples`.
-/

@[expose] public section

namespace Svenonius2004.Examples

def ex_1a : Datum :=
  { id := "svenonius2004_1a"
    source := ⟨"svenonius-2004", "(1a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Helder za-brosil mjač v vorota angličan."
    glossedTokens := [("Helder", "Helder"), ("za-brosil", "into-threw"), ("mjač", "ball"), ("v", "in"), ("vorota", "goal"), ("angličan", "English")]
    context := "Spatial-resultative za-: the goal is the endpoint of the ball's path."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_1b : Datum :=
  { id := "svenonius2004_1b"
    source := ⟨"svenonius-2004", "(1b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "David sovsem za-brosil futbol."
    glossedTokens := [("David", "David"), ("sovsem", "completely"), ("za-brosil", "into-threw"), ("futbol", "soccer")]
    context := "Idiomatic use of the same lexical za- as in the spatial (1a): idiosyncratic meaning is available to lexical prefixes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_1c : Datum :=
  { id := "svenonius2004_1c"
    source := ⟨"svenonius-2004", "(1c)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Ricardo nervno za-brosal mjač."
    glossedTokens := [("Ricardo", "Ricardo"), ("nervno", "nervously"), ("za-brosal", "incp-threw"), ("mjač", "ball")]
    context := "Inceptive (superlexical) za- on the imperfective stem brosat', versus the lexical za- of (1a)/(1b) on perfective brosit'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_1a, ex_1b, ex_1c]

end Svenonius2004.Examples
