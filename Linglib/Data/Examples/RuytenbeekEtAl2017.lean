module

public import Linglib.Data.Examples.Schema

/-!
# `RuytenbeekEtAl2017` — typed example data

Auto-generated from `Linglib/Data/Examples/RuytenbeekEtAl2017.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace RuytenbeekEtAl2017.Examples`.
-/

@[expose] public section

namespace RuytenbeekEtAl2017.Examples

def ruytenbeek2017_ex17 : Datum :=
  { id := "ruytenbeek2017_ex17"
    source := ⟨"ruytenbeek-etal-2017", "(17)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Mettez le cercle rouge à gauche du rectangle jaune."
    glossedTokens := []
    context := "Study 1: a grid of coloured shapes with yes and no buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("study", "1"), ("construction", "imperative")] }

def ruytenbeek2017_ex18 : Datum :=
  { id := "ruytenbeek2017_ex18"
    source := ⟨"ruytenbeek-etal-2017", "(18)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Le cercle rouge est-il à gauche du rectangle jaune ?"
    glossedTokens := []
    context := "Study 1: a grid of coloured shapes with yes and no buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("study", "1"), ("construction", "controlInterrogative")] }

def ruytenbeek2017_ex19 : Datum :=
  { id := "ruytenbeek2017_ex19"
    source := ⟨"ruytenbeek-etal-2017", "(19)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Pouvez-vous mettre le cercle rouge à gauche du rectangle jaune ?"
    glossedTokens := []
    context := "Study 1: a grid of coloured shapes with yes and no buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("study", "1"), ("construction", "canYou")] }

def ruytenbeek2017_ex20 : Datum :=
  { id := "ruytenbeek2017_ex20"
    source := ⟨"ruytenbeek-etal-2017", "(20)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Est-il possible de mettre le cercle rouge à gauche du rectangle jaune ?"
    glossedTokens := []
    context := "Study 1: a grid of coloured shapes with yes and no buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("study", "1"), ("construction", "isItPossible")] }

def ruytenbeek2017_ex23 : Datum :=
  { id := "ruytenbeek2017_ex23"
    source := ⟨"ruytenbeek-etal-2017", "(23)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Vous devez mettre le cercle rouge à gauche du rectangle jaune."
    glossedTokens := []
    context := "Study 2: a grid of coloured shapes with true and false buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("study", "2"), ("construction", "youMust")] }

def ruytenbeek2017_ex24 : Datum :=
  { id := "ruytenbeek2017_ex24"
    source := ⟨"ruytenbeek-etal-2017", "(24)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Mettez le cercle rouge à gauche du rectangle jaune."
    glossedTokens := []
    context := "Study 2: a grid of coloured shapes with true and false buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("study", "2"), ("construction", "imperative")] }

def ruytenbeek2017_ex25 : Datum :=
  { id := "ruytenbeek2017_ex25"
    source := ⟨"ruytenbeek-etal-2017", "(25)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Vous pouvez mettre le cercle rouge à gauche du rectangle jaune."
    glossedTokens := []
    context := "Study 2: a grid of coloured shapes with true and false buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("study", "2"), ("construction", "youCan")] }

def ruytenbeek2017_ex26 : Datum :=
  { id := "ruytenbeek2017_ex26"
    source := ⟨"ruytenbeek-etal-2017", "(26)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Il est possible de mettre le cercle rouge à gauche du rectangle jaune."
    glossedTokens := []
    context := "Study 2: a grid of coloured shapes with true and false buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("study", "2"), ("construction", "itIsPossible")] }

def ruytenbeek2017_ex27 : Datum :=
  { id := "ruytenbeek2017_ex27"
    source := ⟨"ruytenbeek-etal-2017", "(27)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Le cercle rouge est à gauche du rectangle jaune."
    glossedTokens := []
    context := "Study 2: a grid of coloured shapes with true and false buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("study", "2"), ("construction", "controlDeclarative")] }

def ruytenbeek2017_corpus_pouvezvous : Datum :=
  { id := "ruytenbeek2017_corpus_pouvezvous"
    source := ⟨"ruytenbeek-etal-2017", "(9)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Pouvez-vous VP ?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "canYou")] }

def ruytenbeek2017_corpus_estilpossible : Datum :=
  { id := "ruytenbeek2017_corpus_estilpossible"
    source := ⟨"ruytenbeek-etal-2017", "(10)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Est-il possible de VP ?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "isItPossible")] }

def all : List Datum := [ruytenbeek2017_ex17, ruytenbeek2017_ex18, ruytenbeek2017_ex19, ruytenbeek2017_ex20, ruytenbeek2017_ex23, ruytenbeek2017_ex24, ruytenbeek2017_ex25, ruytenbeek2017_ex26, ruytenbeek2017_ex27, ruytenbeek2017_corpus_pouvezvous, ruytenbeek2017_corpus_estilpossible]

end RuytenbeekEtAl2017.Examples
