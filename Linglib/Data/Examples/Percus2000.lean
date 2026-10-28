module

public import Linglib.Data.Examples.Schema

/-!
# `Percus2000` — typed example data

Auto-generated from `Linglib/Data/Examples/Percus2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Percus2000.Examples`.
-/

@[expose] public section

namespace Percus2000.Examples

def ex26a_allon : Datum :=
  { id := "percus2000_ex26a_allon"
    source := ⟨"percus-2000", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary thinks that my brother is Canadian."
    glossedTokens := []
    context := "My brother's name is Allon. Mary thinks Allon is not my brother but she also thinks that Allon is Canadian."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def ex26a_pierreCanadian : Datum :=
  { id := "percus2000_ex26a_pierreCanadian"
    source := ⟨"percus-2000", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary thinks that my brother is Canadian."
    glossedTokens := []
    context := "Mary mistakenly thinks that Pierre is my brother but she correctly takes him to be Canadian."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def ex26a_pierreAmerican : Datum :=
  { id := "percus2000_ex26a_pierreAmerican"
    source := ⟨"percus-2000", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary thinks that my brother is Canadian."
    glossedTokens := []
    context := "Mary thinks that Pierre (the Canadian) is my brother and, since she knows that I am American, concludes that Pierre too is American."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "false")] }

def ex35a_unaware : Datum :=
  { id := "percus2000_ex35a_unaware"
    source := ⟨"percus-2000", "(35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary thinks that my brother always won the game."
    glossedTokens := []
    context := "I am talking about a game that lasted several rounds. Mary wrongly takes Pierre to be my brother, she is unaware that Pierre and I played the series of games, and Pierre won all of those games."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "false")] }

def ex35a_deluded : Datum :=
  { id := "percus2000_ex35a_deluded"
    source := ⟨"percus-2000", "(35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary thinks that my brother always won the game."
    glossedTokens := []
    context := "I am talking about a game that lasted several rounds. Mary is aware that Pierre and I played a series of games but is under the delusion that Pierre won every one, when in fact Pierre's performance was hopeless."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("truthValue", "true")] }

def all : List Datum := [ex26a_allon, ex26a_pierreCanadian, ex26a_pierreAmerican, ex35a_unaware, ex35a_deluded]

end Percus2000.Examples
