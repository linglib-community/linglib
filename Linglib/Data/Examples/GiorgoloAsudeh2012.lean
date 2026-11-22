module

public import Linglib.Data.Examples.Schema

/-!
# `GiorgoloAsudeh2012` — typed example data

Auto-generated from `Linglib/Data/Examples/GiorgoloAsudeh2012.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GiorgoloAsudeh2012.Examples`.
-/

@[expose] public section

namespace GiorgoloAsudeh2012.Examples

def ga2012_1 : Datum :=
  { id := "ga2012_1"
    source := ⟨"giorgolo-asudeh-2012", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most fucking neighbourhood dogs crap on my damn lawn. No, that's not true."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("the denial targets the claim that the neighbourhood dogs crap on the speaker's lawn", .acceptable), ("the denial targets the speaker's attitude towards the dogs or their crapping on the lawn", .unacceptable)]
    paperFeatures := [] }

def ga2012_2 : Datum :=
  { id := "ga2012_2"
    source := ⟨"giorgolo-asudeh-2012", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John Lee Hooker, the bluesman from Tennessee, appeared in The Blues Brothers. No, that's not true."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("the denial targets the claim that John Lee Hooker appeared in The Blues Brothers", .acceptable), ("the denial targets the claim that John Lee Hooker was from Tennessee", .unacceptable)]
    paperFeatures := [] }

def ga2012_3 : Datum :=
  { id := "ga2012_3"
    source := ⟨"anderbois-brasoveanu-henderson-2010", ""⟩
    reportedIn := some ⟨"giorgolo-asudeh-2012", "(3)"⟩
    language := "stan1293"
    primaryText := "John, who by the way almost destroyed his car yesterday, has bought a motorcycle, too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ga2012_4 : Datum :=
  { id := "ga2012_4"
    source := ⟨"anderbois-brasoveanu-henderson-2010", ""⟩
    reportedIn := some ⟨"giorgolo-asudeh-2012", "(4)"⟩
    language := "stan1293"
    primaryText := "Mary, a good drummer, is a good singer too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ga2012_5 : Datum :=
  { id := "ga2012_5"
    source := ⟨"anderbois-brasoveanu-henderson-2010", ""⟩
    reportedIn := some ⟨"giorgolo-asudeh-2012", "(5)"⟩
    language := "stan1293"
    primaryText := "Jake, who almost killed a woman with his car, visited her in the hospital."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ga2012_6 : Datum :=
  { id := "ga2012_6"
    source := ⟨"anderbois-brasoveanu-henderson-2010", ""⟩
    reportedIn := some ⟨"giorgolo-asudeh-2012", "(6)"⟩
    language := "stan1293"
    primaryText := "Lucy, who doesn't help her sister, told Jane to."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ga2012_7 : Datum :=
  { id := "ga2012_7"
    source := ⟨"anderbois-brasoveanu-henderson-2010", ""⟩
    reportedIn := some ⟨"giorgolo-asudeh-2012", "(7)"⟩
    language := "stan1293"
    primaryText := "Melinda, who won three games of tennis, lost because Betty won six."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ga2012_8 : Datum :=
  { id := "ga2012_8"
    source := ⟨"giorgolo-asudeh-2012", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Luke Skywalker is so gullible that he believes that Jabba the Hutt, a notorious scammer, is a trustworthy business partner."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("that Jabba is a notorious scammer is the speaker's comment", .acceptable), ("that Jabba is a notorious scammer is among Skywalker's beliefs", .unacceptable)]
    paperFeatures := [] }

def ga2012_9 : Datum :=
  { id := "ga2012_9"
    source := ⟨"giorgolo-asudeh-2012", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All Cairo taxi drivers, who by the way painted their taxis red in protest, are on strike."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ga2012_10 : Datum :=
  { id := "ga2012_10"
    source := ⟨"giorgolo-asudeh-2012", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every Cairo taxi driver, who by the way would threaten me with his gun, is on strike."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ga2012_20 : Datum :=
  { id := "ga2012_20"
    source := ⟨"giorgolo-asudeh-2012", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John, who likes cats, likes dogs also."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ga2012_1, ga2012_2, ga2012_3, ga2012_4, ga2012_5, ga2012_6, ga2012_7, ga2012_8, ga2012_9, ga2012_10, ga2012_20]

end GiorgoloAsudeh2012.Examples
