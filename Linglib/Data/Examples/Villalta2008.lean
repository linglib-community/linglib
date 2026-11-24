module

public import Linglib.Data.Examples.Schema

/-!
# `Villalta2008` — typed example data

Auto-generated from `Linglib/Data/Examples/Villalta2008.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Villalta2008.Examples`.
-/

@[expose] public section

namespace Villalta2008.Examples

def ex_30 : Datum :=
  { id := "villalta2008_30"
    source := ⟨"villalta-2008", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Victoria wishes Sofía would bring an apple pie."
    glossedTokens := []
    context := "Sofía has promised to bring a dessert to the picnic. Victoria believes that there are three possibilities for what she may actually do. She could prepare a chocolate cake, even though Victoria considers that extremely unlikely because it represents far too much work. She might bring an apple pie, which Victoria considers very likely since she can just buy it at the bakery nearby. Or Sofía might bring ice-cream, which seems most likely to Victoria, since she usually has some in her freezer. Victoria prefers the chocolate cake over the apple pie and the apple pie over the ice-cream."
    judgment := .acceptable
    verdict := some false
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_31 : Datum :=
  { id := "villalta2008_31"
    source := ⟨"villalta-2008", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Victoria is disappointed that Sofía brought an apple pie."
    glossedTokens := []
    context := "Sofía has promised to bring a dessert to the picnic. Victoria believes that there are three possibilities for what she may actually do. She could prepare a chocolate cake, even though Victoria considers that extremely unlikely because it represents far too much work. She might bring an apple pie, which Victoria considers very likely since she can just buy it at the bakery nearby. Or Sofía might bring ice-cream, which seems most likely to Victoria, since she usually has some in her freezer. Victoria prefers the chocolate cake over the apple pie and the apple pie over the ice-cream. Sofía does in fact bring the apple pie to the picnic."
    judgment := .acceptable
    verdict := some true
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_30, ex_31]

end Villalta2008.Examples
