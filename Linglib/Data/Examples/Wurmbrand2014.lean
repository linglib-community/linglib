module

public import Linglib.Data.Examples.Schema

/-!
# `Wurmbrand2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Wurmbrand2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Wurmbrand2014.Examples`.
-/

@[expose] public section

namespace Wurmbrand2014.Examples

def ex_1 : Datum :=
  { id := "wurmbrand2014_1"
    source := ⟨"wurmbrand-2014", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo decided to read a book."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "future")] }

def ex_2 : Datum :=
  { id := "wurmbrand2014_2"
    source := ⟨"wurmbrand-2014", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo believes Julia to be a princess."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "propositional")] }

def ex_3 : Datum :=
  { id := "wurmbrand2014_3"
    source := ⟨"wurmbrand-2014", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo decided to bring the toys tomorrow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "future"), ("episodic", "possible")] }

def ex_4 : Datum :=
  { id := "wurmbrand2014_4"
    source := ⟨"wurmbrand-2014", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo believed Julia to bring the toys right then."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Leo believed Julia to be bringing the toys right then.", .acceptable)]
    readings := []
    paperFeatures := [("class", "propositional"), ("episodic", "impossible")] }

def ex_5 : Datum :=
  { id := "wurmbrand2014_5"
    source := ⟨"wurmbrand-2014", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo claimed to be rich."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "propositional"), ("syntax", "control")] }

def ex_6 : Datum :=
  { id := "wurmbrand2014_6"
    source := ⟨"wurmbrand-2014", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo claimed to eat dinner yesterday."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Leo claimed to eat dinner.", .acceptable)]
    readings := []
    paperFeatures := [("class", "propositional"), ("episodic", "impossible")] }

def ex_7 : Datum :=
  { id := "wurmbrand2014_7"
    source := ⟨"wurmbrand-2014", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday, John decided to leave tomorrow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "future")] }

def ex_8 : Datum :=
  { id := "wurmbrand2014_8"
    source := ⟨"wurmbrand-2014", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday, John tried to leave tomorrow."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Yesterday, John tried to leave.", .acceptable)]
    readings := []
    paperFeatures := [("class", "tenseless simultaneous")] }

def ex_9 : Datum :=
  { id := "wurmbrand2014_9"
    source := ⟨"wurmbrand-2014", "(6d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday, John claimed to leave tomorrow."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("class", "propositional")] }

def ex_10 : Datum :=
  { id := "wurmbrand2014_10"
    source := ⟨"wurmbrand-2014", "(6e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday, John claimed to be leaving tomorrow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("scheduled future", .acceptable)]
    paperFeatures := [("class", "propositional")] }

def ex_11 : Datum :=
  { id := "wurmbrand2014_11"
    source := ⟨"wurmbrand-2014", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bridge is expected to collapse tomorrow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "future"), ("syntax", "ECM")] }

def ex_12 : Datum :=
  { id := "wurmbrand2014_12"
    source := ⟨"wurmbrand-2014", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo decided a week ago to go to the party yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "future"), ("future", "relative")] }

def ex_13 : Datum :=
  { id := "wurmbrand2014_13"
    source := ⟨"wurmbrand-2014", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo decided a week ago that he will go to the party yesterday."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Leo decided a week ago that he will go to the party.", .acceptable)]
    readings := []
    paperFeatures := [("future", "absolute")] }

def ex_14 : Datum :=
  { id := "wurmbrand2014_14"
    source := ⟨"wurmbrand-2014", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John will promise me tonight to tell his mother tomorrow that ..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "future")] }

def ex_15 : Datum :=
  { id := "wurmbrand2014_15"
    source := ⟨"wurmbrand-2014", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John will promise me tonight that he would tell his mother tomorrow that ..."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("would", "temporal")] }

def ex_16 : Datum :=
  { id := "wurmbrand2014_16"
    source := ⟨"wurmbrand-2014", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim decided a week ago that she would go to the party yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("would", "relative")] }

def ex_17 : Datum :=
  { id := "wurmbrand2014_17"
    source := ⟨"wurmbrand-2014", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John promised me yesterday that he will tell his mother tomorrow that they were having their last meal together (when ...)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (SOT)", .unacceptable), ("shifted past", .acceptable)]
    paperFeatures := [("SOT", "blocked")] }

def ex_18 : Datum :=
  { id := "wurmbrand2014_18"
    source := ⟨"wurmbrand-2014", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John promised me yesterday to tell his mother tomorrow that they were having their last meal together."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (SOT)", .acceptable)]
    paperFeatures := [("SOT", "applies")] }

def ex_19 : Datum :=
  { id := "wurmbrand2014_19"
    source := ⟨"wurmbrand-2014", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John promised me yesterday that he would tell his mother tomorrow that they were having their last meal together."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (SOT)", .acceptable)]
    paperFeatures := [("SOT", "applies")] }

def ex_20 : Datum :=
  { id := "wurmbrand2014_20"
    source := ⟨"wurmbrand-2014", "(28b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo found out that Mary would be pregnant."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (SOT)", .acceptable), ("shifted past", .unacceptable)]
    paperFeatures := [("would", "obligatory SOT")] }

def ex_21 : Datum :=
  { id := "wurmbrand2014_21"
    source := ⟨"wurmbrand-2014", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John will promise me tonight that he would tell his mother tomorrow that ..."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("would", "temporal"), ("SOT", "blocked")] }

def ex_22 : Datum :=
  { id := "wurmbrand2014_22"
    source := ⟨"wurmbrand-2014", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John will promise me tonight to tell his mother tomorrow that they were having their last meal together (when ...)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (SOT)", .unacceptable), ("shifted past", .acceptable)]
    paperFeatures := [("SOT", "blocked")] }

def ex_23 : Datum :=
  { id := "wurmbrand2014_23"
    source := ⟨"wurmbrand-2014", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo sings in the shower right now."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Leo sings in the shower.", .acceptable)]
    readings := []
    paperFeatures := [("tense", "present"), ("episodic", "impossible")] }

def ex_24 : Datum :=
  { id := "wurmbrand2014_24"
    source := ⟨"wurmbrand-2014", "(45b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo sang in the shower yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("tense", "past"), ("episodic", "possible")] }

def ex_25 : Datum :=
  { id := "wurmbrand2014_25"
    source := ⟨"wurmbrand-2014", "(45c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo will sing in the shower tomorrow."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("tense", "future"), ("episodic", "possible")] }

def ex_26 : Datum :=
  { id := "wurmbrand2014_26"
    source := ⟨"wurmbrand-2014", "(49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John sang in the shower when the mailman arrived."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("John was singing in the shower when the mailman arrived.", .acceptable)]
    readings := []
    paperFeatures := [("reference time", "restricted")] }

def ex_27 : Datum :=
  { id := "wurmbrand2014_27"
    source := ⟨"wurmbrand-2014", "(50a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said that Mary was reading Middlemarch."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (SOT)", .acceptable), ("shifted past", .acceptable)]
    paperFeatures := [] }

def ex_28 : Datum :=
  { id := "wurmbrand2014_28"
    source := ⟨"wurmbrand-2014", "(50b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said that Mary read Middlemarch."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (SOT)", .unacceptable), ("shifted past", .acceptable)]
    paperFeatures := [] }

def ex_29 : Datum :=
  { id := "wurmbrand2014_29"
    source := ⟨"wurmbrand-2014", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Probably not. He expects to work tomorrow."
    glossedTokens := []
    context := "Is John available tomorrow at 5 p.m.?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "future"), ("aspect", "perfective")] }

def ex_30 : Datum :=
  { id := "wurmbrand2014_30"
    source := ⟨"wurmbrand-2014", "(53b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't think so. He expects to work at 5 p.m. tomorrow."
    glossedTokens := []
    context := "Is John available tomorrow at 5 p.m.?"
    judgment := .ungrammatical
    alternatives := [("I don't think so. He expects to be working at 5 p.m. tomorrow.", .acceptable)]
    readings := []
    paperFeatures := [("class", "future"), ("reference time", "restricted")] }

def ex_31 : Datum :=
  { id := "wurmbrand2014_31"
    source := ⟨"wurmbrand-2014", "(55a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo believes Julia to sing in the shower right now."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("class", "propositional"), ("aspect", "perfective")] }

def ex_32 : Datum :=
  { id := "wurmbrand2014_32"
    source := ⟨"wurmbrand-2014", "(55b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo believed Julia to sing in the shower yesterday."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("class", "propositional"), ("aspect", "perfective")] }

def ex_33 : Datum :=
  { id := "wurmbrand2014_33"
    source := ⟨"wurmbrand-2014", "(55c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo believes Julia to like bagels."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "propositional"), ("predicate", "stative")] }

def ex_34 : Datum :=
  { id := "wurmbrand2014_34"
    source := ⟨"wurmbrand-2014", "(55e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo believed Julia to be singing in the shower yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "propositional"), ("aspect", "imperfective")] }

def ex_35 : Datum :=
  { id := "wurmbrand2014_35"
    source := ⟨"wurmbrand-2014", "(56b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo claimed to sing in the shower yesterday."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("class", "propositional"), ("syntax", "control")] }

def ex_36 : Datum :=
  { id := "wurmbrand2014_36"
    source := ⟨"wurmbrand-2014", "(56e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo claimed to be singing in the shower yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "propositional"), ("aspect", "imperfective")] }

def ex_37 : Datum :=
  { id := "wurmbrand2014_37"
    source := ⟨"wurmbrand-2014", "(57a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo seems to sing in the shower right now."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("class", "tenseless simultaneous"), ("matrix tense", "present")] }

def ex_38 : Datum :=
  { id := "wurmbrand2014_38"
    source := ⟨"wurmbrand-2014", "(57b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo seems to be singing in the shower right now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "tenseless simultaneous"), ("aspect", "imperfective")] }

def ex_39 : Datum :=
  { id := "wurmbrand2014_39"
    source := ⟨"wurmbrand-2014", "(57c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo seemed to sing in the shower yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "tenseless simultaneous"), ("matrix tense", "past")] }

def ex_40 : Datum :=
  { id := "wurmbrand2014_40"
    source := ⟨"wurmbrand-2014", "(58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Five years ago, Julia claimed that she is pregnant."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "double access")] }

def ex_41 : Datum :=
  { id := "wurmbrand2014_41"
    source := ⟨"wurmbrand-2014", "(58c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Five years ago, Julia claimed to be pregnant."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "propositional")] }

def ex_42 : Datum :=
  { id := "wurmbrand2014_42"
    source := ⟨"wurmbrand-2014", "(59a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A year ago, Mary claimed to know that she was pregnant."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (SOT)", .acceptable)]
    paperFeatures := [] }

def ex_43 : Datum :=
  { id := "wurmbrand2014_43"
    source := ⟨"wurmbrand-2014", "(61a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bridge is expected to collapse right now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("near future", .acceptable), ("simultaneous", .unacceptable)]
    paperFeatures := [] }

def ex_44 : Datum :=
  { id := "wurmbrand2014_44"
    source := ⟨"wurmbrand-2014", "(61b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bridge is expected to be collapsing right now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [] }

def ex_45 : Datum :=
  { id := "wurmbrand2014_45"
    source := ⟨"wurmbrand-2014", "(66a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday, John managed to sing tomorrow."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Yesterday, John managed to sing.", .acceptable)]
    readings := []
    paperFeatures := [("class", "tenseless simultaneous")] }

def ex_46 : Datum :=
  { id := "wurmbrand2014_46"
    source := ⟨"wurmbrand-2014", "(66b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bridge began to tremble tomorrow."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("The bridge began to tremble.", .acceptable)]
    readings := []
    paperFeatures := [("class", "tenseless simultaneous"), ("syntax", "raising")] }

def ex_47 : Datum :=
  { id := "wurmbrand2014_47"
    source := ⟨"wurmbrand-2014", "(67c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bridge seems to tremble right now."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("The bridge seems to be trembling right now.", .acceptable)]
    readings := []
    paperFeatures := [("class", "tenseless simultaneous"), ("matrix tense", "present")] }

def ex_48 : Datum :=
  { id := "wurmbrand2014_48"
    source := ⟨"wurmbrand-2014", "(67d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bridge seemed to tremble yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "tenseless simultaneous"), ("matrix tense", "past")] }

def ex_49 : Datum :=
  { id := "wurmbrand2014_49"
    source := ⟨"wurmbrand-2014", "(68a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo seemed to sing at 5 p.m. yesterday."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("Leo seemed to be singing at 5 p.m. yesterday.", .acceptable)]
    readings := []
    paperFeatures := [("reference time", "restricted")] }

def ex_50 : Datum :=
  { id := "wurmbrand2014_50"
    source := ⟨"wurmbrand-2014", "(69a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John tried to eat his breakfast."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("class", "tenseless simultaneous"), ("matrix tense", "past")] }

def ex_51 : Datum :=
  { id := "wurmbrand2014_51"
    source := ⟨"wurmbrand-2014", "(69b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John tries to eat his breakfast right now."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := [("John is trying to eat his breakfast right now.", .acceptable)]
    readings := []
    paperFeatures := [("matrix aspect", "perfective")] }

def ex_52 : Datum :=
  { id := "wurmbrand2014_52"
    source := ⟨"wurmbrand-2014", "(70a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "From 2:00 to 4:00 John seemed to his parents to be writing his one-hour exam."
    glossedTokens := []
    context := "John had an exam scheduled for yesterday, taken online at home. His parents knew the exam was yesterday but not its time. At 2:00 the music in John's room stopped and they thought he might be doing the exam. At 2:30 their clock stopped for exactly one hour, unnoticed. When it showed 3:00 the music came back on, so they thought he did the exam from 2:00 to 3:00. In fact he did the exam from 2:00 to 3:00 and then played computer games with headphones until 4:00."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("attitude holder", "overt"), ("aspect", "imperfective")] }

def ex_53 : Datum :=
  { id := "wurmbrand2014_53"
    source := ⟨"wurmbrand-2014", "(70b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "From 2:00 to 4:00 John seemed to his parents to write his one-hour exam."
    glossedTokens := []
    context := "John had an exam scheduled for yesterday, taken online at home. His parents knew the exam was yesterday but not its time. At 2:00 the music in John's room stopped and they thought he might be doing the exam. At 2:30 their clock stopped for exactly one hour, unnoticed. When it showed 3:00 the music came back on, so they thought he did the exam from 2:00 to 3:00. In fact he did the exam from 2:00 to 3:00 and then played computer games with headphones until 4:00."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("attitude holder", "overt"), ("aspect", "perfective")] }

def ex_54 : Datum :=
  { id := "wurmbrand2014_54"
    source := ⟨"wurmbrand-2014", "(70d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "From 2:00 to 4:00 John seemed to write his one-hour exam."
    glossedTokens := []
    context := "John had an exam scheduled for yesterday, taken online at home. His parents knew the exam was yesterday but not its time. At 2:00 the music in John's room stopped and they thought he might be doing the exam. At 2:30 their clock stopped for exactly one hour, unnoticed. When it showed 3:00 the music came back on, so they thought he did the exam from 2:00 to 3:00. In fact he did the exam from 2:00 to 3:00 and then played computer games with headphones until 4:00."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("attitude holder", "understood"), ("aspect", "perfective")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23, ex_24, ex_25, ex_26, ex_27, ex_28, ex_29, ex_30, ex_31, ex_32, ex_33, ex_34, ex_35, ex_36, ex_37, ex_38, ex_39, ex_40, ex_41, ex_42, ex_43, ex_44, ex_45, ex_46, ex_47, ex_48, ex_49, ex_50, ex_51, ex_52, ex_53, ex_54]

end Wurmbrand2014.Examples
