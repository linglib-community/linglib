module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Karttunen1974` — typed example data

Auto-generated from `Linglib/Data/Examples/Karttunen1974.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Karttunen1974.Examples`.
-/

@[expose] public section

namespace Karttunen1974.Examples

def ex_1a : Datum :=
  { id := "karttunen1974_1a"
    source := ⟨"karttunen-1974", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess slept until the prince kissed her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative")] }

def ex_1b : Datum :=
  { id := "karttunen1974_1b"
    source := ⟨"karttunen-1974", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John studied the piano until he got married."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative")] }

def ex_1c : Datum :=
  { id := "karttunen1974_1c"
    source := ⟨"karttunen-1974", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill was writing a novel until he became an actor."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative")] }

def ex_1c_cf : Datum :=
  { id := "karttunen1974_1c_cf"
    source := ⟨"karttunen-1974", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill wrote a novel until he became an actor."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative")] }

def ex_1d : Datum :=
  { id := "karttunen1974_1d"
    source := ⟨"karttunen-1974", "(1d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Guests arrived until midnight."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative")] }

def ex_1d_cf : Datum :=
  { id := "karttunen1974_1d_cf"
    source := ⟨"karttunen-1974", "(1d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A guest arrived until midnight."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative")] }

def ex_1e : Datum :=
  { id := "karttunen1974_1e"
    source := ⟨"karttunen-1974", "(1e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess didn't wake up until the prince kissed her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_1e_cf : Datum :=
  { id := "karttunen1974_1e_cf"
    source := ⟨"karttunen-1974", "(1e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess woke up until the prince kissed her."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative")] }

def p284 : Datum :=
  { id := "karttunen1974_p284"
    source := ⟨"karttunen-1974", "p. 284"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess woke up until 9."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative")] }

def ex_2 : Datum :=
  { id := "karttunen1974_2"
    source := ⟨"karttunen-1974", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't think the princess woke up until the prince kissed her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "superordinate")] }

def ex_5a : Datum :=
  { id := "karttunen1974_5a"
    source := ⟨"karttunen-1974", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The investigation will continue until all the questions have been answered."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative")] }

def ex_5b : Datum :=
  { id := "karttunen1974_5b"
    source := ⟨"karttunen-1974", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The investigation will continue as long as there are unanswered questions."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "asLongAs"), ("host", "durative")] }

def ex_5c : Datum :=
  { id := "karttunen1974_5c"
    source := ⟨"karttunen-1974", "(5c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The investigation will continue for two more years."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "for"), ("host", "durative")] }

def ex_6a : Datum :=
  { id := "karttunen1974_6a"
    source := ⟨"karttunen-1974", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The investigation will not end until all the questions have been answered."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_6b : Datum :=
  { id := "karttunen1974_6b"
    source := ⟨"karttunen-1974", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The investigation will not end as long as there are unanswered questions."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "asLongAs"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_6c : Datum :=
  { id := "karttunen1974_6c"
    source := ⟨"karttunen-1974", "(6c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The investigation will not end for two more years."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "for"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_7a : Datum :=
  { id := "karttunen1974_7a"
    source := ⟨"karttunen-1974", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The investigation will end until all the questions have been answered."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative")] }

def ex_7b : Datum :=
  { id := "karttunen1974_7b"
    source := ⟨"karttunen-1974", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The investigation will end as long as there are unanswered questions."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "asLongAs"), ("host", "nondurative")] }

def ex_7c : Datum :=
  { id := "karttunen1974_7c"
    source := ⟨"karttunen-1974", "(7c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The investigation will end for two more years."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "for"), ("host", "nondurative")] }

def ex_8a : Datum :=
  { id := "karttunen1974_8a"
    source := ⟨"karttunen-1974", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess slept to 9 o'clock."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "to"), ("host", "durative")] }

def ex_8b : Datum :=
  { id := "karttunen1974_8b"
    source := ⟨"karttunen-1974", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess woke up to 9 o'clock."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "to"), ("host", "nondurative")] }

def ex_8c : Datum :=
  { id := "karttunen1974_8c"
    source := ⟨"karttunen-1974", "(8c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess didn't wake up to 9 o'clock."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "to"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_9a : Datum :=
  { id := "karttunen1974_9a"
    source := ⟨"karttunen-1974", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How long did the princess sleep?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "howLong"), ("host", "durative")] }

def ex_9b : Datum :=
  { id := "karttunen1974_9b"
    source := ⟨"karttunen-1974", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How long did the princess not wake up?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "howLong"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_10a : Datum :=
  { id := "karttunen1974_10a"
    source := ⟨"karttunen-1974", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I washed the dishes while you slept."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "while"), ("host", "durative")] }

def ex_10b : Datum :=
  { id := "karttunen1974_10b"
    source := ⟨"karttunen-1974", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I washed the dishes while you were not in the kitchen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "while"), ("host", "durative"), ("negation", "clausal")] }

def ex_10c : Datum :=
  { id := "karttunen1974_10c"
    source := ⟨"karttunen-1974", "(10c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I washed the dishes while you didn't wake up."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "while"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_11a_earliest : Datum :=
  { id := "karttunen1974_11a_earliest"
    source := ⟨"karttunen-1974", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess slept until 9 at the earliest."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative"), ("modifier", "atTheEarliest")] }

def ex_11a_latest : Datum :=
  { id := "karttunen1974_11a_latest"
    source := ⟨"karttunen-1974", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess slept until 9 at the latest."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative"), ("modifier", "atTheLatest")] }

def ex_11b_earliest : Datum :=
  { id := "karttunen1974_11b_earliest"
    source := ⟨"karttunen-1974", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess didn't wake up until 9 at the earliest."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal"), ("modifier", "atTheEarliest")] }

def ex_11b_latest : Datum :=
  { id := "karttunen1974_11b_latest"
    source := ⟨"karttunen-1974", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess didn't wake up until 9 at the latest."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal"), ("modifier", "atTheLatest")] }

def ex_12a : Datum :=
  { id := "karttunen1974_12a"
    source := ⟨"karttunen-1974", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess slept only until 9."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative"), ("modifier", "only")] }

def ex_12b : Datum :=
  { id := "karttunen1974_12b"
    source := ⟨"karttunen-1974", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess didn't wake up only until 9."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal"), ("modifier", "only")] }

def ex_13a_longer : Datum :=
  { id := "karttunen1974_13a_longer"
    source := ⟨"karttunen-1974", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess slept until 9 or longer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative"), ("modifier", "orLonger")] }

def ex_13a_more : Datum :=
  { id := "karttunen1974_13a_more"
    source := ⟨"karttunen-1974", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess slept until 9 or more."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative"), ("modifier", "orMore")] }

def ex_13b_longer : Datum :=
  { id := "karttunen1974_13b_longer"
    source := ⟨"karttunen-1974", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess didn't wake up until 9 or longer."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal"), ("modifier", "orLonger")] }

def ex_13b_more : Datum :=
  { id := "karttunen1974_13b_more"
    source := ⟨"karttunen-1974", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess didn't wake up until 9 or more."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal"), ("modifier", "orMore")] }

def ex_14a : Datum :=
  { id := "karttunen1974_14a"
    source := ⟨"karttunen-1974", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess slept until 9 and beyond."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative"), ("modifier", "andBeyond")] }

def ex_14b : Datum :=
  { id := "karttunen1974_14b"
    source := ⟨"karttunen-1974", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess didn't wake up until 9 and beyond."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal"), ("modifier", "andBeyond")] }

def ex_15 : Datum :=
  { id := "karttunen1974_15"
    source := ⟨"karttunen-1974", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess didn't sleep until 9."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("durative", .acceptable), ("inchoative", .acceptable)]
    paperFeatures := [("adverbial", "until"), ("host", "durative"), ("negation", "clausal")] }

def ex_17 : Datum :=
  { id := "karttunen1974_17"
    source := ⟨"karttunen-1974", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't think the princess slept until 9."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative"), ("negation", "superordinate")] }

def ex_18 : Datum :=
  { id := "karttunen1974_18"
    source := ⟨"karttunen-1974", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The frog waited until the princess slept."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative"), ("complement", "inchoative")] }

def ex_19 : Datum :=
  { id := "karttunen1974_19"
    source := ⟨"karttunen-1974", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess slept before the Queen left the room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("inchoative", .acceptable), ("accomplishment", .acceptable)]
    paperFeatures := [("adverbial", "before"), ("host", "durative")] }

def ex_20a : Datum :=
  { id := "karttunen1974_20a"
    source := ⟨"karttunen-1974", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The frog waited until the party lasted."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative"), ("complement", "durative")] }

def ex_20b : Datum :=
  { id := "karttunen1974_20b"
    source := ⟨"karttunen-1974", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The party didn't last until morning."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative"), ("negation", "clausal")] }

def ex_21 : Datum :=
  { id := "karttunen1974_21"
    source := ⟨"karttunen-1974", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nancy remained a spinster until 1974."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative")] }

def ex_22 : Datum :=
  { id := "karttunen1974_22"
    source := ⟨"karttunen-1974", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nancy remained a spinster until she died."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative")] }

def ex_23 : Datum :=
  { id := "karttunen1974_23"
    source := ⟨"karttunen-1974", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nancy didn't get married until she died."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_24 : Datum :=
  { id := "karttunen1974_24"
    source := ⟨"karttunen-1974", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nancy didn't get married until 1974."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_25a : Datum :=
  { id := "karttunen1974_25a"
    source := ⟨"karttunen-1974", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I won't marry you until my mother dies."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_25b : Datum :=
  { id := "karttunen1974_25b"
    source := ⟨"karttunen-1974", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I won't marry you before my mother dies."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "before"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_26 : Datum :=
  { id := "karttunen1974_26"
    source := ⟨"karttunen-1974", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nancy didn't marry until she met Henry."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_28 : Datum :=
  { id := "karttunen1974_28"
    source := ⟨"karttunen-1974", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess didn't wake up until 9."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_30a : Datum :=
  { id := "karttunen1974_30a"
    source := ⟨"karttunen-1974", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wish the princess hadn't woken up until 9."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_30b : Datum :=
  { id := "karttunen1974_30b"
    source := ⟨"karttunen-1974", "(30b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the princess hadn't woken up until 9, the Queen would have been much happier than she was."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_32a : Datum :=
  { id := "karttunen1974_32a"
    source := ⟨"karttunen-1974", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wish the princess had slept until 9."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative")] }

def ex_32b : Datum :=
  { id := "karttunen1974_32b"
    source := ⟨"karttunen-1974", "(32b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wish the princess had slept only until 9."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until"), ("host", "durative"), ("modifier", "only")] }

def ex_38a : Datum :=
  { id := "karttunen1974_38a"
    source := ⟨"karttunen-1974", "(38a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Prinzessin wachte erst um 9 Uhr auf."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "erst"), ("host", "nondurative")] }

def ex_38a_neg : Datum :=
  { id := "karttunen1974_38a_neg"
    source := ⟨"karttunen-1974", "(38a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Prinzessin wachte nicht erst um 9 Uhr auf."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "erst"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_38b : Datum :=
  { id := "karttunen1974_38b"
    source := ⟨"karttunen-1974", "(38b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ich wünschte die Prinzessin wäre erst um 9 Uhr aufgewacht."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "erst"), ("host", "nondurative")] }

def ex_39a : Datum :=
  { id := "karttunen1974_39a"
    source := ⟨"karttunen-1974", "(39a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Prinsessa ei herännyt ennenkuin yhdeksältä."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "ennenKuin"), ("host", "nondurative"), ("negation", "clausal")] }

def ex_39b : Datum :=
  { id := "karttunen1974_39b"
    source := ⟨"karttunen-1974", "(39b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Prinsessa heräsi vasta yhdeksältä."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "vasta"), ("host", "nondurative")] }

def fn3 : Datum :=
  { id := "karttunen1974_fn3"
    source := ⟨"karttunen-1974", "p. 295, fn. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess woke up for two years."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "for"), ("host", "nondurative")] }

def fn6_before_reduced : Datum :=
  { id := "karttunen1974_fn6_before_reduced"
    source := ⟨"karttunen-1974", "p. 295, fn. 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I won't leave before you."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "before")] }

def fn6_until_reduced : Datum :=
  { id := "karttunen1974_fn6_until_reduced"
    source := ⟨"karttunen-1974", "p. 295, fn. 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I won't leave until you."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until")] }

def fn6_before_measure : Datum :=
  { id := "karttunen1974_fn6_before_measure"
    source := ⟨"karttunen-1974", "p. 295, fn. 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't arrive five hours before Bill came."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "before")] }

def fn6_until_measure : Datum :=
  { id := "karttunen1974_fn6_until_measure"
    source := ⟨"karttunen-1974", "pp. 295-296, fn. 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't arrive five hours until Bill came."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "until")] }

def fn8_clause : Datum :=
  { id := "karttunen1974_fn8_clause"
    source := ⟨"karttunen-1974", "p. 296, fn. 8"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Prinzessin wachte nicht auf, bis ich sie um 9 Uhr weckte."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "bis"), ("host", "nondurative"), ("negation", "clausal")] }

def fn8_np : Datum :=
  { id := "karttunen1974_fn8_np"
    source := ⟨"karttunen-1974", "p. 296, fn. 8"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Prinzessin wachte nicht auf, bis 9 Uhr."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("adverbial", "bis"), ("host", "nondurative"), ("negation", "clausal")] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_1c_cf, ex_1d, ex_1d_cf, ex_1e, ex_1e_cf, p284, ex_2, ex_5a, ex_5b, ex_5c, ex_6a, ex_6b, ex_6c, ex_7a, ex_7b, ex_7c, ex_8a, ex_8b, ex_8c, ex_9a, ex_9b, ex_10a, ex_10b, ex_10c, ex_11a_earliest, ex_11a_latest, ex_11b_earliest, ex_11b_latest, ex_12a, ex_12b, ex_13a_longer, ex_13a_more, ex_13b_longer, ex_13b_more, ex_14a, ex_14b, ex_15, ex_17, ex_18, ex_19, ex_20a, ex_20b, ex_21, ex_22, ex_23, ex_24, ex_25a, ex_25b, ex_26, ex_28, ex_30a, ex_30b, ex_32a, ex_32b, ex_38a, ex_38a_neg, ex_38b, ex_39a, ex_39b, fn3, fn6_before_reduced, fn6_until_reduced, fn6_before_measure, fn6_until_measure, fn8_clause, fn8_np]

/-- The time expression a sentence tests. -/
inductive Adverbial where
  /-- until: English until -/
  | until
  /-- before: English before -/
  | before
  /-- to: English to, as in to 9 o'clock -/
  | to
  /-- howLong: English how long -/
  | howLong
  /-- while: English while -/
  | whilePhrase
  /-- asLongAs: English as long as -/
  | asLongAs
  /-- for: English for, as in for two more years -/
  | forPhrase
  /-- erst: German erst -/
  | erst
  /-- bis: German bis -/
  | bis
  /-- ennenKuin: Finnish ennen kuin, printed ennenkuin -/
  | ennenKuin
  /-- vasta: Finnish vasta -/
  | vasta
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `adverbial`. -/
def adverbial (e : Datum) : Option Adverbial :=
  e.parse? "adverbial" [("until", .until), ("before", .before), ("to", .to), ("howLong", .howLong),
    ("while", .whilePhrase), ("asLongAs", .asLongAs), ("for", .forPhrase), ("erst", .erst),
    ("bis", .bis), ("ennenKuin", .ennenKuin), ("vasta", .vasta)]

/-- The class of the clause the time expression modifies, apart from its negation. -/
inductive Host where
  /-- durative: about something that takes place over an interval of time: an activity, a generic, a progressive or an iterative clause -/
  | durative
  /-- nondurative: of the achievement or accomplishment type -/
  | nondurative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `host`. -/
def host (e : Datum) : Option Host :=
  e.parse? "host" [("durative", .durative), ("nondurative", .nondurative)]

/-- The negation the time expression stands under, where there is one. -/
inductive Negation where
  /-- clausal: negation of the clause the expression modifies -/
  | clausal
  /-- superordinate: negation of a superordinate think, as in (2) and (17) -/
  | superordinate
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `negation`. -/
def negation (e : Datum) : Option Negation :=
  e.parse? "negation" [("clausal", .clausal), ("superordinate", .superordinate)]

/-- The qualification of the until-phrase in (11)-(14) and (32b). -/
inductive Modifier where
  /-- atTheEarliest: at the earliest -/
  | atTheEarliest
  /-- atTheLatest: at the latest -/
  | atTheLatest
  /-- only: only -/
  | only
  /-- orLonger: or longer -/
  | orLonger
  /-- orMore: or more -/
  | orMore
  /-- andBeyond: and beyond -/
  | andBeyond
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `modifier`. -/
def modifier (e : Datum) : Option Modifier :=
  e.parse? "modifier" [("atTheEarliest", .atTheEarliest), ("atTheLatest", .atTheLatest), ("only", .only),
    ("orLonger", .orLonger), ("orMore", .orMore), ("andBeyond", .andBeyond)]

/-- The clause an until-phrase contains, in (18) and (20a). -/
inductive Complement where
  /-- inchoative: a clause with a punctual, inchoative interpretation, as the princess slept 'the princess began to sleep' -/
  | inchoative
  /-- durative: a clause with a verb that is exclusively durative, as last -/
  | durative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `complement`. -/
def complement (e : Datum) : Option Complement :=
  e.parse? "complement" [("inchoative", .inchoative), ("durative", .durative)]

/-- The examples of the file. -/
inductive Example where
  | ex_1a
  | ex_1b
  | ex_1c
  | ex_1c_cf
  | ex_1d
  | ex_1d_cf
  | ex_1e
  | ex_1e_cf
  | p284
  | ex_2
  | ex_5a
  | ex_5b
  | ex_5c
  | ex_6a
  | ex_6b
  | ex_6c
  | ex_7a
  | ex_7b
  | ex_7c
  | ex_8a
  | ex_8b
  | ex_8c
  | ex_9a
  | ex_9b
  | ex_10a
  | ex_10b
  | ex_10c
  | ex_11a_earliest
  | ex_11a_latest
  | ex_11b_earliest
  | ex_11b_latest
  | ex_12a
  | ex_12b
  | ex_13a_longer
  | ex_13a_more
  | ex_13b_longer
  | ex_13b_more
  | ex_14a
  | ex_14b
  | ex_15
  | ex_17
  | ex_18
  | ex_19
  | ex_20a
  | ex_20b
  | ex_21
  | ex_22
  | ex_23
  | ex_24
  | ex_25a
  | ex_25b
  | ex_26
  | ex_28
  | ex_30a
  | ex_30b
  | ex_32a
  | ex_32b
  | ex_38a
  | ex_38a_neg
  | ex_38b
  | ex_39a
  | ex_39b
  | fn3
  | fn6_before_reduced
  | fn6_until_reduced
  | fn6_before_measure
  | fn6_until_measure
  | fn8_clause
  | fn8_np
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_1a, .ex_1b, .ex_1c, .ex_1c_cf, .ex_1d, .ex_1d_cf, .ex_1e, .ex_1e_cf, .p284, .ex_2, .ex_5a,
    .ex_5b, .ex_5c, .ex_6a, .ex_6b, .ex_6c, .ex_7a, .ex_7b, .ex_7c, .ex_8a, .ex_8b, .ex_8c,
    .ex_9a, .ex_9b, .ex_10a, .ex_10b, .ex_10c, .ex_11a_earliest, .ex_11a_latest, .ex_11b_earliest,
    .ex_11b_latest, .ex_12a, .ex_12b, .ex_13a_longer, .ex_13a_more, .ex_13b_longer, .ex_13b_more,
    .ex_14a, .ex_14b, .ex_15, .ex_17, .ex_18, .ex_19, .ex_20a, .ex_20b, .ex_21, .ex_22, .ex_23,
    .ex_24, .ex_25a, .ex_25b, .ex_26, .ex_28, .ex_30a, .ex_30b, .ex_32a, .ex_32b, .ex_38a,
    .ex_38a_neg, .ex_38b, .ex_39a, .ex_39b, .fn3, .fn6_before_reduced, .fn6_until_reduced,
    .fn6_before_measure, .fn6_until_measure, .fn8_clause, .fn8_np]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_1a => _root_.Karttunen1974.Examples.ex_1a
  | .ex_1b => _root_.Karttunen1974.Examples.ex_1b
  | .ex_1c => _root_.Karttunen1974.Examples.ex_1c
  | .ex_1c_cf => _root_.Karttunen1974.Examples.ex_1c_cf
  | .ex_1d => _root_.Karttunen1974.Examples.ex_1d
  | .ex_1d_cf => _root_.Karttunen1974.Examples.ex_1d_cf
  | .ex_1e => _root_.Karttunen1974.Examples.ex_1e
  | .ex_1e_cf => _root_.Karttunen1974.Examples.ex_1e_cf
  | .p284 => _root_.Karttunen1974.Examples.p284
  | .ex_2 => _root_.Karttunen1974.Examples.ex_2
  | .ex_5a => _root_.Karttunen1974.Examples.ex_5a
  | .ex_5b => _root_.Karttunen1974.Examples.ex_5b
  | .ex_5c => _root_.Karttunen1974.Examples.ex_5c
  | .ex_6a => _root_.Karttunen1974.Examples.ex_6a
  | .ex_6b => _root_.Karttunen1974.Examples.ex_6b
  | .ex_6c => _root_.Karttunen1974.Examples.ex_6c
  | .ex_7a => _root_.Karttunen1974.Examples.ex_7a
  | .ex_7b => _root_.Karttunen1974.Examples.ex_7b
  | .ex_7c => _root_.Karttunen1974.Examples.ex_7c
  | .ex_8a => _root_.Karttunen1974.Examples.ex_8a
  | .ex_8b => _root_.Karttunen1974.Examples.ex_8b
  | .ex_8c => _root_.Karttunen1974.Examples.ex_8c
  | .ex_9a => _root_.Karttunen1974.Examples.ex_9a
  | .ex_9b => _root_.Karttunen1974.Examples.ex_9b
  | .ex_10a => _root_.Karttunen1974.Examples.ex_10a
  | .ex_10b => _root_.Karttunen1974.Examples.ex_10b
  | .ex_10c => _root_.Karttunen1974.Examples.ex_10c
  | .ex_11a_earliest => _root_.Karttunen1974.Examples.ex_11a_earliest
  | .ex_11a_latest => _root_.Karttunen1974.Examples.ex_11a_latest
  | .ex_11b_earliest => _root_.Karttunen1974.Examples.ex_11b_earliest
  | .ex_11b_latest => _root_.Karttunen1974.Examples.ex_11b_latest
  | .ex_12a => _root_.Karttunen1974.Examples.ex_12a
  | .ex_12b => _root_.Karttunen1974.Examples.ex_12b
  | .ex_13a_longer => _root_.Karttunen1974.Examples.ex_13a_longer
  | .ex_13a_more => _root_.Karttunen1974.Examples.ex_13a_more
  | .ex_13b_longer => _root_.Karttunen1974.Examples.ex_13b_longer
  | .ex_13b_more => _root_.Karttunen1974.Examples.ex_13b_more
  | .ex_14a => _root_.Karttunen1974.Examples.ex_14a
  | .ex_14b => _root_.Karttunen1974.Examples.ex_14b
  | .ex_15 => _root_.Karttunen1974.Examples.ex_15
  | .ex_17 => _root_.Karttunen1974.Examples.ex_17
  | .ex_18 => _root_.Karttunen1974.Examples.ex_18
  | .ex_19 => _root_.Karttunen1974.Examples.ex_19
  | .ex_20a => _root_.Karttunen1974.Examples.ex_20a
  | .ex_20b => _root_.Karttunen1974.Examples.ex_20b
  | .ex_21 => _root_.Karttunen1974.Examples.ex_21
  | .ex_22 => _root_.Karttunen1974.Examples.ex_22
  | .ex_23 => _root_.Karttunen1974.Examples.ex_23
  | .ex_24 => _root_.Karttunen1974.Examples.ex_24
  | .ex_25a => _root_.Karttunen1974.Examples.ex_25a
  | .ex_25b => _root_.Karttunen1974.Examples.ex_25b
  | .ex_26 => _root_.Karttunen1974.Examples.ex_26
  | .ex_28 => _root_.Karttunen1974.Examples.ex_28
  | .ex_30a => _root_.Karttunen1974.Examples.ex_30a
  | .ex_30b => _root_.Karttunen1974.Examples.ex_30b
  | .ex_32a => _root_.Karttunen1974.Examples.ex_32a
  | .ex_32b => _root_.Karttunen1974.Examples.ex_32b
  | .ex_38a => _root_.Karttunen1974.Examples.ex_38a
  | .ex_38a_neg => _root_.Karttunen1974.Examples.ex_38a_neg
  | .ex_38b => _root_.Karttunen1974.Examples.ex_38b
  | .ex_39a => _root_.Karttunen1974.Examples.ex_39a
  | .ex_39b => _root_.Karttunen1974.Examples.ex_39b
  | .fn3 => _root_.Karttunen1974.Examples.fn3
  | .fn6_before_reduced => _root_.Karttunen1974.Examples.fn6_before_reduced
  | .fn6_until_reduced => _root_.Karttunen1974.Examples.fn6_until_reduced
  | .fn6_before_measure => _root_.Karttunen1974.Examples.fn6_before_measure
  | .fn6_until_measure => _root_.Karttunen1974.Examples.fn6_until_measure
  | .fn8_clause => _root_.Karttunen1974.Examples.fn8_clause
  | .fn8_np => _root_.Karttunen1974.Examples.fn8_np

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.Karttunen1974.Examples.all := rfl

/-- The value the example records under `adverbial`. -/
def Example.adverbial : Example → Option Adverbial
  | .ex_1a => some .until
  | .ex_1b => some .until
  | .ex_1c => some .until
  | .ex_1c_cf => some .until
  | .ex_1d => some .until
  | .ex_1d_cf => some .until
  | .ex_1e => some .until
  | .ex_1e_cf => some .until
  | .p284 => some .until
  | .ex_2 => some .until
  | .ex_5a => some .until
  | .ex_5b => some .asLongAs
  | .ex_5c => some .forPhrase
  | .ex_6a => some .until
  | .ex_6b => some .asLongAs
  | .ex_6c => some .forPhrase
  | .ex_7a => some .until
  | .ex_7b => some .asLongAs
  | .ex_7c => some .forPhrase
  | .ex_8a => some .to
  | .ex_8b => some .to
  | .ex_8c => some .to
  | .ex_9a => some .howLong
  | .ex_9b => some .howLong
  | .ex_10a => some .whilePhrase
  | .ex_10b => some .whilePhrase
  | .ex_10c => some .whilePhrase
  | .ex_11a_earliest => some .until
  | .ex_11a_latest => some .until
  | .ex_11b_earliest => some .until
  | .ex_11b_latest => some .until
  | .ex_12a => some .until
  | .ex_12b => some .until
  | .ex_13a_longer => some .until
  | .ex_13a_more => some .until
  | .ex_13b_longer => some .until
  | .ex_13b_more => some .until
  | .ex_14a => some .until
  | .ex_14b => some .until
  | .ex_15 => some .until
  | .ex_17 => some .until
  | .ex_18 => some .until
  | .ex_19 => some .before
  | .ex_20a => some .until
  | .ex_20b => some .until
  | .ex_21 => some .until
  | .ex_22 => some .until
  | .ex_23 => some .until
  | .ex_24 => some .until
  | .ex_25a => some .until
  | .ex_25b => some .before
  | .ex_26 => some .until
  | .ex_28 => some .until
  | .ex_30a => some .until
  | .ex_30b => some .until
  | .ex_32a => some .until
  | .ex_32b => some .until
  | .ex_38a => some .erst
  | .ex_38a_neg => some .erst
  | .ex_38b => some .erst
  | .ex_39a => some .ennenKuin
  | .ex_39b => some .vasta
  | .fn3 => some .forPhrase
  | .fn6_before_reduced => some .before
  | .fn6_until_reduced => some .until
  | .fn6_before_measure => some .before
  | .fn6_until_measure => some .until
  | .fn8_clause => some .bis
  | .fn8_np => some .bis

theorem Example.adverbial_datum :
    ∀ x : Example, _root_.Karttunen1974.Examples.adverbial x.datum = x.adverbial := by
  decide +kernel

/-- The value the example records under `host`. -/
def Example.host : Example → Option Host
  | .ex_1a => some .durative
  | .ex_1b => some .durative
  | .ex_1c => some .durative
  | .ex_1c_cf => some .nondurative
  | .ex_1d => some .durative
  | .ex_1d_cf => some .nondurative
  | .ex_1e => some .nondurative
  | .ex_1e_cf => some .nondurative
  | .p284 => some .nondurative
  | .ex_2 => some .nondurative
  | .ex_5a => some .durative
  | .ex_5b => some .durative
  | .ex_5c => some .durative
  | .ex_6a => some .nondurative
  | .ex_6b => some .nondurative
  | .ex_6c => some .nondurative
  | .ex_7a => some .nondurative
  | .ex_7b => some .nondurative
  | .ex_7c => some .nondurative
  | .ex_8a => some .durative
  | .ex_8b => some .nondurative
  | .ex_8c => some .nondurative
  | .ex_9a => some .durative
  | .ex_9b => some .nondurative
  | .ex_10a => some .durative
  | .ex_10b => some .durative
  | .ex_10c => some .nondurative
  | .ex_11a_earliest => some .durative
  | .ex_11a_latest => some .durative
  | .ex_11b_earliest => some .nondurative
  | .ex_11b_latest => some .nondurative
  | .ex_12a => some .durative
  | .ex_12b => some .nondurative
  | .ex_13a_longer => some .durative
  | .ex_13a_more => some .durative
  | .ex_13b_longer => some .nondurative
  | .ex_13b_more => some .nondurative
  | .ex_14a => some .durative
  | .ex_14b => some .nondurative
  | .ex_15 => some .durative
  | .ex_17 => some .durative
  | .ex_18 => some .durative
  | .ex_19 => some .durative
  | .ex_20a => some .durative
  | .ex_20b => some .durative
  | .ex_21 => some .durative
  | .ex_22 => some .durative
  | .ex_23 => some .nondurative
  | .ex_24 => some .nondurative
  | .ex_25a => some .nondurative
  | .ex_25b => some .nondurative
  | .ex_26 => some .nondurative
  | .ex_28 => some .nondurative
  | .ex_30a => some .nondurative
  | .ex_30b => some .nondurative
  | .ex_32a => some .durative
  | .ex_32b => some .durative
  | .ex_38a => some .nondurative
  | .ex_38a_neg => some .nondurative
  | .ex_38b => some .nondurative
  | .ex_39a => some .nondurative
  | .ex_39b => some .nondurative
  | .fn3 => some .nondurative
  | .fn6_before_reduced => none
  | .fn6_until_reduced => none
  | .fn6_before_measure => none
  | .fn6_until_measure => none
  | .fn8_clause => some .nondurative
  | .fn8_np => some .nondurative

theorem Example.host_datum :
    ∀ x : Example, _root_.Karttunen1974.Examples.host x.datum = x.host := by
  decide +kernel

/-- The value the example records under `negation`. -/
def Example.negation : Example → Option Negation
  | .ex_1a => none
  | .ex_1b => none
  | .ex_1c => none
  | .ex_1c_cf => none
  | .ex_1d => none
  | .ex_1d_cf => none
  | .ex_1e => some .clausal
  | .ex_1e_cf => none
  | .p284 => none
  | .ex_2 => some .superordinate
  | .ex_5a => none
  | .ex_5b => none
  | .ex_5c => none
  | .ex_6a => some .clausal
  | .ex_6b => some .clausal
  | .ex_6c => some .clausal
  | .ex_7a => none
  | .ex_7b => none
  | .ex_7c => none
  | .ex_8a => none
  | .ex_8b => none
  | .ex_8c => some .clausal
  | .ex_9a => none
  | .ex_9b => some .clausal
  | .ex_10a => none
  | .ex_10b => some .clausal
  | .ex_10c => some .clausal
  | .ex_11a_earliest => none
  | .ex_11a_latest => none
  | .ex_11b_earliest => some .clausal
  | .ex_11b_latest => some .clausal
  | .ex_12a => none
  | .ex_12b => some .clausal
  | .ex_13a_longer => none
  | .ex_13a_more => none
  | .ex_13b_longer => some .clausal
  | .ex_13b_more => some .clausal
  | .ex_14a => none
  | .ex_14b => some .clausal
  | .ex_15 => some .clausal
  | .ex_17 => some .superordinate
  | .ex_18 => none
  | .ex_19 => none
  | .ex_20a => none
  | .ex_20b => some .clausal
  | .ex_21 => none
  | .ex_22 => none
  | .ex_23 => some .clausal
  | .ex_24 => some .clausal
  | .ex_25a => some .clausal
  | .ex_25b => some .clausal
  | .ex_26 => some .clausal
  | .ex_28 => some .clausal
  | .ex_30a => some .clausal
  | .ex_30b => some .clausal
  | .ex_32a => none
  | .ex_32b => none
  | .ex_38a => none
  | .ex_38a_neg => some .clausal
  | .ex_38b => none
  | .ex_39a => some .clausal
  | .ex_39b => none
  | .fn3 => none
  | .fn6_before_reduced => none
  | .fn6_until_reduced => none
  | .fn6_before_measure => none
  | .fn6_until_measure => none
  | .fn8_clause => some .clausal
  | .fn8_np => some .clausal

theorem Example.negation_datum :
    ∀ x : Example, _root_.Karttunen1974.Examples.negation x.datum = x.negation := by
  decide +kernel

/-- The value the example records under `modifier`. -/
def Example.modifier : Example → Option Modifier
  | .ex_1a => none
  | .ex_1b => none
  | .ex_1c => none
  | .ex_1c_cf => none
  | .ex_1d => none
  | .ex_1d_cf => none
  | .ex_1e => none
  | .ex_1e_cf => none
  | .p284 => none
  | .ex_2 => none
  | .ex_5a => none
  | .ex_5b => none
  | .ex_5c => none
  | .ex_6a => none
  | .ex_6b => none
  | .ex_6c => none
  | .ex_7a => none
  | .ex_7b => none
  | .ex_7c => none
  | .ex_8a => none
  | .ex_8b => none
  | .ex_8c => none
  | .ex_9a => none
  | .ex_9b => none
  | .ex_10a => none
  | .ex_10b => none
  | .ex_10c => none
  | .ex_11a_earliest => some .atTheEarliest
  | .ex_11a_latest => some .atTheLatest
  | .ex_11b_earliest => some .atTheEarliest
  | .ex_11b_latest => some .atTheLatest
  | .ex_12a => some .only
  | .ex_12b => some .only
  | .ex_13a_longer => some .orLonger
  | .ex_13a_more => some .orMore
  | .ex_13b_longer => some .orLonger
  | .ex_13b_more => some .orMore
  | .ex_14a => some .andBeyond
  | .ex_14b => some .andBeyond
  | .ex_15 => none
  | .ex_17 => none
  | .ex_18 => none
  | .ex_19 => none
  | .ex_20a => none
  | .ex_20b => none
  | .ex_21 => none
  | .ex_22 => none
  | .ex_23 => none
  | .ex_24 => none
  | .ex_25a => none
  | .ex_25b => none
  | .ex_26 => none
  | .ex_28 => none
  | .ex_30a => none
  | .ex_30b => none
  | .ex_32a => none
  | .ex_32b => some .only
  | .ex_38a => none
  | .ex_38a_neg => none
  | .ex_38b => none
  | .ex_39a => none
  | .ex_39b => none
  | .fn3 => none
  | .fn6_before_reduced => none
  | .fn6_until_reduced => none
  | .fn6_before_measure => none
  | .fn6_until_measure => none
  | .fn8_clause => none
  | .fn8_np => none

theorem Example.modifier_datum :
    ∀ x : Example, _root_.Karttunen1974.Examples.modifier x.datum = x.modifier := by
  decide +kernel

/-- The value the example records under `complement`. -/
def Example.complement : Example → Option Complement
  | .ex_1a => none
  | .ex_1b => none
  | .ex_1c => none
  | .ex_1c_cf => none
  | .ex_1d => none
  | .ex_1d_cf => none
  | .ex_1e => none
  | .ex_1e_cf => none
  | .p284 => none
  | .ex_2 => none
  | .ex_5a => none
  | .ex_5b => none
  | .ex_5c => none
  | .ex_6a => none
  | .ex_6b => none
  | .ex_6c => none
  | .ex_7a => none
  | .ex_7b => none
  | .ex_7c => none
  | .ex_8a => none
  | .ex_8b => none
  | .ex_8c => none
  | .ex_9a => none
  | .ex_9b => none
  | .ex_10a => none
  | .ex_10b => none
  | .ex_10c => none
  | .ex_11a_earliest => none
  | .ex_11a_latest => none
  | .ex_11b_earliest => none
  | .ex_11b_latest => none
  | .ex_12a => none
  | .ex_12b => none
  | .ex_13a_longer => none
  | .ex_13a_more => none
  | .ex_13b_longer => none
  | .ex_13b_more => none
  | .ex_14a => none
  | .ex_14b => none
  | .ex_15 => none
  | .ex_17 => none
  | .ex_18 => some .inchoative
  | .ex_19 => none
  | .ex_20a => some .durative
  | .ex_20b => none
  | .ex_21 => none
  | .ex_22 => none
  | .ex_23 => none
  | .ex_24 => none
  | .ex_25a => none
  | .ex_25b => none
  | .ex_26 => none
  | .ex_28 => none
  | .ex_30a => none
  | .ex_30b => none
  | .ex_32a => none
  | .ex_32b => none
  | .ex_38a => none
  | .ex_38a_neg => none
  | .ex_38b => none
  | .ex_39a => none
  | .ex_39b => none
  | .fn3 => none
  | .fn6_before_reduced => none
  | .fn6_until_reduced => none
  | .fn6_before_measure => none
  | .fn6_until_measure => none
  | .fn8_clause => none
  | .fn8_np => none

theorem Example.complement_datum :
    ∀ x : Example, _root_.Karttunen1974.Examples.complement x.datum = x.complement := by
  decide +kernel

end Karttunen1974.Examples
