module

public import Linglib.Data.Examples.Schema

/-!
# `ZwickyPullum1983` — typed example data

Auto-generated from `Linglib/Data/Examples/ZwickyPullum1983.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ZwickyPullum1983.Examples`.
-/

@[expose] public section

namespace ZwickyPullum1983.Examples

def ex_1a : Datum :=
  { id := "zwickypullum1983_1a"
    source := ⟨"zwicky-pullum-1983", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She's gone"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clitic", "'s")] }

def ex_1b : Datum :=
  { id := "zwickypullum1983_1b"
    source := ⟨"zwicky-pullum-1983", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They've all seen this movie before"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clitic", "'ve")] }

def ex_2a : Datum :=
  { id := "zwickypullum1983_2a"
    source := ⟨"zwicky-pullum-1983", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The person I was talking to's going to be angry with me"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "A"), ("host", "preposition")] }

def ex_2b : Datum :=
  { id := "zwickypullum1983_2b"
    source := ⟨"zwicky-pullum-1983", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ball you hit's just broken my dining room window"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "A"), ("host", "verb")] }

def ex_2c : Datum :=
  { id := "zwickypullum1983_2c"
    source := ⟨"zwicky-pullum-1983", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Any answer not entirely right's going to be marked as an error"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "A"), ("host", "adjective")] }

def ex_2d : Datum :=
  { id := "zwickypullum1983_2d"
    source := ⟨"zwicky-pullum-1983", "(2d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The drive home tonight's been really easy"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "A"), ("host", "adverb")] }

def ex_3 : Datum :=
  { id := "zwickypullum1983_3"
    source := ⟨"zwicky-pullum-1983", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'd've done it if you'd asked me"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "F")] }

def ex_4a : Datum :=
  { id := "zwickypullum1983_4a"
    source := ⟨"zwicky-pullum-1983", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You haven't been here"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("morpheme", "-n't")] }

def ex_4b : Datum :=
  { id := "zwickypullum1983_4b"
    source := ⟨"zwicky-pullum-1983", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Haven't you been there?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "E")] }

def ex_5 : Datum :=
  { id := "zwickypullum1983_5"
    source := ⟨"zwicky-pullum-1983", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You have not been there"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_6 : Datum :=
  { id := "zwickypullum1983_6"
    source := ⟨"zwicky-pullum-1983", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have not you been there?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "E")] }

def ex_7a : Datum :=
  { id := "zwickypullum1983_7a"
    source := ⟨"zwicky-pullum-1983", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have you been there?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_7b : Datum :=
  { id := "zwickypullum1983_7b"
    source := ⟨"zwicky-pullum-1983", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have you not been there?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_8a : Datum :=
  { id := "zwickypullum1983_8a"
    source := ⟨"zwicky-pullum-1983", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You could've been there"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("clitic", "'ve")] }

def ex_8b : Datum :=
  { id := "zwickypullum1983_8b"
    source := ⟨"zwicky-pullum-1983", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Could've you been there?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "E")] }

def ex_9 : Datum :=
  { id := "zwickypullum1983_9"
    source := ⟨"zwicky-pullum-1983", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'dn't be doing this unless I had to"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "F")] }

def ex_10a : Datum :=
  { id := "zwickypullum1983_10a"
    source := ⟨"zwicky-pullum-1983", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wouldn't be doing this unless I had to"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_10b : Datum :=
  { id := "zwickypullum1983_10b"
    source := ⟨"zwicky-pullum-1983", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'd not be doing this unless I had to"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_12a : Datum :=
  { id := "zwickypullum1983_12a"
    source := ⟨"zwicky-pullum-1983", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It would be a shame to have not ever had a chance to see it"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "A")] }

def ex_12b : Datum :=
  { id := "zwickypullum1983_12b"
    source := ⟨"zwicky-pullum-1983", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It would be a shame to haven't ever had a chance to see it"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "A")] }

def ex_13a : Datum :=
  { id := "zwickypullum1983_13a"
    source := ⟨"zwicky-pullum-1983", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The police have not been informed"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_13b : Datum :=
  { id := "zwickypullum1983_13b"
    source := ⟨"zwicky-pullum-1983", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The police haven't been informed"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_14a : Datum :=
  { id := "zwickypullum1983_14a"
    source := ⟨"zwicky-pullum-1983", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Would the police have not been informed?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_14b : Datum :=
  { id := "zwickypullum1983_14b"
    source := ⟨"zwicky-pullum-1983", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Would the police haven't been informed?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "A")] }

def ex_15a : Datum :=
  { id := "zwickypullum1983_15a"
    source := ⟨"zwicky-pullum-1983", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A good Christian can nót attend church and still be saved"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "D"), ("reading", "CAN(NOT(P))")] }

def ex_15b : Datum :=
  { id := "zwickypullum1983_15b"
    source := ⟨"zwicky-pullum-1983", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A good Christian can't attend church and still be saved"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "D"), ("reading", "NOT(CAN(P))")] }

def ex_16a : Datum :=
  { id := "zwickypullum1983_16a"
    source := ⟨"zwicky-pullum-1983", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Well, I just would not not sunbathe on such a beautiful day"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "D")] }

def ex_16b : Datum :=
  { id := "zwickypullum1983_16b"
    source := ⟨"zwicky-pullum-1983", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When he's nervous, he can't not smoke"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "D")] }

def ex_17 : Datum :=
  { id := "zwickypullum1983_17"
    source := ⟨"zwicky-pullum-1983", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Could this group of sixteen energetic youngsters not travel down the Colorado in a bark canoe?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("criterion", "D")] }

def all : List Datum := [ex_1a, ex_1b, ex_2a, ex_2b, ex_2c, ex_2d, ex_3, ex_4a, ex_4b, ex_5, ex_6, ex_7a, ex_7b, ex_8a, ex_8b, ex_9, ex_10a, ex_10b, ex_12a, ex_12b, ex_13a, ex_13b, ex_14a, ex_14b, ex_15a, ex_15b, ex_16a, ex_16b, ex_17]

end ZwickyPullum1983.Examples
