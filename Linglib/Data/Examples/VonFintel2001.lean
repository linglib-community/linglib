module

public import Linglib.Data.Examples.Schema

/-!
# `VonFintel2001` — typed example data

Auto-generated from `Linglib/Data/Examples/VonFintel2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VonFintel2001.Examples`.
-/

@[expose] public section

namespace VonFintel2001.Examples

def ex_1 : Datum :=
  { id := "vonfintel2001_1"
    source := ⟨"geis-zwicky-1971", "(4)"⟩
    reportedIn := some ⟨"von-fintel-2001", "(1)"⟩
    language := "stan1293"
    primaryText := "If you mow the lawn, I'll give you five dollars."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("perfection: no five dollars without mowing", .questionable), ("strengthening: the five dollars are not free for the taking", .acceptable)]
    paperFeatures := [("inference", "conditional perfection"), ("flavor", "bouletic")] }

def ex_2 : Datum :=
  { id := "vonfintel2001_2"
    source := ⟨"geis-zwicky-1971", "(1)"⟩
    reportedIn := some ⟨"von-fintel-2001", "(2)"⟩
    language := "stan1293"
    primaryText := "If John leans out of that window any further, he'll fall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("inference", "conditional perfection")] }

def ex_3 : Datum :=
  { id := "vonfintel2001_3"
    source := ⟨"geis-zwicky-1971", "(8)"⟩
    reportedIn := some ⟨"von-fintel-2001", "(3)"⟩
    language := "stan1293"
    primaryText := "If you disturb me tonight, I won't let you go to the movies tomorrow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("inference", "conditional perfection")] }

def ex_4 : Datum :=
  { id := "vonfintel2001_4"
    source := ⟨"geis-zwicky-1971", "(9)"⟩
    reportedIn := some ⟨"von-fintel-2001", "(4)"⟩
    language := "stan1293"
    primaryText := "If you heat iron in a fire, it turns red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("inference", "conditional perfection")] }

def ex_6 : Datum :=
  { id := "vonfintel2001_6"
    source := ⟨"lilje-1972", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(6)"⟩
    language := "stan1293"
    primaryText := "If it doesn't say 'Goodyear', it isn't Polyglas."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("perfection", .unacceptable), ("strengthening: the object is not necessarily not Polyglas", .acceptable)]
    paperFeatures := [("inference", "no perfection")] }

def ex_7 : Datum :=
  { id := "vonfintel2001_7"
    source := ⟨"lilje-1972", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(7)"⟩
    language := "stan1293"
    primaryText := "If this cactus grows native to Idaho, then it's not an Astrophytum."
    glossedTokens := []
    context := "An information-seeking dialogue on whether the cactus is an Astrophytum."
    judgment := .acceptable
    contrasts := []
    readings := [("perfection", .unacceptable), ("strengthening: it is not settled that the cactus is not an Astrophytum", .acceptable)]
    paperFeatures := [("inference", "no perfection"), ("question", "information-seeking")] }

def ex_8 : Datum :=
  { id := "vonfintel2001_8"
    source := ⟨"lilje-1972", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(8)"⟩
    language := "stan1293"
    primaryText := "If you scratch on the eight-ball, then you lost the game."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("perfection", .unacceptable)]
    paperFeatures := [("inference", "no perfection")] }

def ex_9 : Datum :=
  { id := "vonfintel2001_9"
    source := ⟨"lilje-1972", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(9)"⟩
    language := "stan1293"
    primaryText := "If the axioms aren't consistent with each other, then every WFF in the system is a theorem."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("perfection", .unacceptable)]
    paperFeatures := [("inference", "no perfection")] }

def ex_10 : Datum :=
  { id := "vonfintel2001_10"
    source := ⟨"boer-lycan-1973", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "(10)"⟩
    language := "stan1293"
    primaryText := "If John quits, he will be replaced."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("perfection", .unacceptable), ("strengthening: it is not settled that John will be replaced", .acceptable)]
    paperFeatures := [("inference", "no perfection")] }

def ex_11 : Datum :=
  { id := "vonfintel2001_11"
    source := ⟨"von-fintel-2001", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you get a \"B\" on your next history test, I will give you $5."
    glossedTokens := []
    context := "Uttered by the wealthy aunt of an uninspired C-average high school student."
    judgment := .acceptable
    contrasts := []
    readings := [("perfection: the student must avoid an A", .unacceptable), ("strengthening: no $5 for another C", .acceptable)]
    paperFeatures := [("inference", "no perfection")] }

def ex_17a : Datum :=
  { id := "vonfintel2001_17a"
    source := ⟨"von-fintel-2001", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "not only warm but hot"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("not only some but all", .acceptable), ("not only John but John and Mary", .acceptable)]
    readings := []
    paperFeatures := [("test", "not only α but β"), ("scale", "same monotonicity")] }

def ex_17b : Datum :=
  { id := "vonfintel2001_17b"
    source := ⟨"von-fintel-2001", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "not only some but some and not all"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := [("not only John but only John", .unacceptable), ("not only John but John and not Mary", .unacceptable)]
    readings := []
    paperFeatures := [("test", "not only α but β"), ("scale", "mixed monotonicity")] }

def seat : Datum :=
  { id := "vonfintel2001_seat"
    source := ⟨"cornulier-1983", ""⟩
    reportedIn := some ⟨"von-fintel-2001", "p. 10"⟩
    language := "stan1293"
    primaryText := "One is allowed to sit in this seat if one is disabled or one is older than 70."
    glossedTokens := []
    context := "A sign on public transportation."
    judgment := .acceptable
    contrasts := []
    readings := [("perfection: only the disabled or the over-70 may sit here", .acceptable)]
    paperFeatures := [("inference", "conditional perfection"), ("presumption", "exhaustivity")] }

def p14_2 : Datum :=
  { id := "vonfintel2001_p14_2"
    source := ⟨"von-fintel-2001", "(2) p. 15"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Q: Who left the party early? A: Robin and Hilary left the party early."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("exhaustive: Robin and Hilary and nobody else", .acceptable)]
    paperFeatures := [("answer", "exhaustive")] }

def p15_3 : Datum :=
  { id := "vonfintel2001_p15_3"
    source := ⟨"von-fintel-2001", "(3) p. 16"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Q: Will Robin come to the party? A: If there is vegetarian food Robin will come to the party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("exhaustive: Robin comes only if there is vegetarian food", .acceptable)]
    paperFeatures := [("answer", "exhaustive"), ("inference", "conditional perfection")] }

def p17_4a : Datum :=
  { id := "vonfintel2001_p17_4a"
    source := ⟨"von-fintel-2001", "(4) p. 18"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Q: Will you give me $5 if I mow the lawn for you? A: Sure, I will give you $5 if you mow the lawn."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Q: Will the TV work if it is humid? A: Yes, the TV will work if it is humid.", .acceptable)]
    readings := [("perfection", .unacceptable)]
    paperFeatures := [("question", "yes/no conditional"), ("inference", "no perfection")] }

def p17_5 : Datum :=
  { id := "vonfintel2001_p17_5"
    source := ⟨"von-fintel-2001", "(5) p. 18"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: John is in Amherst today. B: If he is in Amherst, he'll be home late tonight."
    glossedTokens := []
    context := "Implicit question: what of current interest follows from John's being in Amherst today?"
    judgment := .acceptable
    contrasts := []
    readings := [("perfection: he is home late only if in Amherst", .unacceptable)]
    paperFeatures := [("question", "consequences of an antecedent"), ("inference", "no perfection")] }

def p17_6 : Datum :=
  { id := "vonfintel2001_p17_6"
    source := ⟨"von-fintel-2001", "(6) p. 18"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Q: Where around here can I buy Italian newspapers? A: You can get them at Out of Town News in Harvard Square."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("exhaustive", .unacceptable)]
    paperFeatures := [("question", "mention-some")] }

def ex_18 : Datum :=
  { id := "vonfintel2001_18"
    source := ⟨"von-fintel-2001", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Q: Will you be upset if I call you at home tonight? A: I will be upset if you call me after midnight."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("relativized perfection: a call before midnight will not upset her about its time", .acceptable), ("full perfection: nothing but a call after midnight upsets her", .unacceptable)]
    paperFeatures := [("inference", "relativized perfection"), ("question", "antecedents from a narrow set")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_17a, ex_17b, seat, p14_2, p15_3, p17_4a, p17_5, p17_6, ex_18]

end VonFintel2001.Examples
