module

public import Linglib.Data.Examples.Schema

/-!
# `Landman1992` — typed example data

Auto-generated from `Linglib/Data/Examples/Landman1992.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Landman1992.Examples`.
-/

@[expose] public section

namespace Landman1992.Examples

def ex3 : Datum :=
  { id := "landman1992_ex3"
    source := ⟨"landman-1992", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary was drawing a circle."
    glossedTokens := []
    context := "Mary started drawing a circle and was interrupted before she came even close to having drawn one."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def ex4 : Datum :=
  { id := "landman1992_ex4"
    source := ⟨"landman-1992", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary drew a circle."
    glossedTokens := []
    context := "Mary started drawing a circle and was interrupted before she came even close to having drawn one."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "false")] }

def ex13 : Datum :=
  { id := "landman1992_ex13"
    source := ⟨"landman-1992", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary was crossing the street, when the truck hit her."
    glossedTokens := []
    context := "Mary was halfway across the street when a truck hit her; evaluated at the interval at which the truck is seconds away."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def ex17_sink : Datum :=
  { id := "landman1992_ex17_sink"
    source := ⟨"landman-1992", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary was crossing the Atlantic."
    glossedTokens := []
    context := "Mary gets into the water in France; she is not a very good swimmer; she swims for an hour, and sinks."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "false")] }

def ex17_miracle : Datum :=
  { id := "landman1992_ex17_miracle"
    source := ⟨"landman-1992", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary was crossing the Atlantic."
    glossedTokens := []
    context := "Mary gets into the water in France; she is not a very good swimmer, but through divine intervention she actually manages to make it across the ocean. Asked after half an hour of swimming."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def ex18 : Datum :=
  { id := "landman1992_ex18"
    source := ⟨"landman-1992", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary was crossing the street, when the first truck hit her."
    glossedTokens := []
    context := "A big and busy street with two trucks in two lanes: the first truck hits Mary, and the second drives one truck-length behind the first, so that if the first truck hadn't hit her, the second would have (19)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def ex20 : Datum :=
  { id := "landman1992_ex20"
    source := ⟨"landman-1992", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary was wiping out the Roman army."
    glossedTokens := []
    context := "Mary, a person of moderate physical capacities, is battling the Roman army. She manages to kill a couple of soldiers before she gets killed."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "false")] }

def all : List Datum := [ex3, ex4, ex13, ex17_sink, ex17_miracle, ex18, ex20]

end Landman1992.Examples
