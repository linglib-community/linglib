module

public import Linglib.Data.Examples.Schema

/-!
# `Abusch1997` — typed example data

Auto-generated from `Linglib/Data/Examples/Abusch1997.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Abusch1997.Examples`.
-/

@[expose] public section

namespace Abusch1997.Examples

def ex1 : Datum :=
  { id := "abusch1997_ex1"
    source := ⟨"abusch-1997", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The defendant was actually at home watching 'The Simpsons' at the time of the crime. But after hearing the testimony of the first eye-witness, the jurors clearly believed that he was in the laboratory building."
    glossedTokens := []
    context := "Past-shifted (backward-shifted) reading: the embedded `was` (in 'he was in the laboratory') is anaphoric to the time of the crime introduced in the first sentence. Time of the defendant being in the laboratory precedes the jurors' believing time. Abusch's diagnostic for the Independent Theory's anaphoric account of embedded past tense."
    judgment := .acceptable
    contrasts := []
    readings := [("past-shifted (defendant in lab before jurors' believing)", .acceptable)]
    paperFeatures := [] }

def ex2 : Datum :=
  { id := "abusch1997_ex2"
    source := ⟨"abusch-1997", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary believed it was raining."
    glossedTokens := []
    context := "Simultaneous reading. The embedded `was raining` is anaphoric to the matrix `believed`, yielding a reading where the raining is co-temporal with the believing. Abusch's contrast with (1): both readings derived by the Independent Theory via anaphora to different antecedents."
    judgment := .acceptable
    contrasts := []
    readings := [("simultaneous (raining at believing time)", .acceptable), ("past-shifted (raining before believing)", .acceptable)]
    paperFeatures := [] }

def ex3_ULC : Datum :=
  { id := "abusch1997_ex3_ULC"
    source := ⟨"abusch-1997", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John found an ostrich in his apartment yesterday. Just before he opened the door, he thought that a burglar attacked him."
    glossedTokens := []
    context := "Upper Limit Constraint (ULC) foil. The Independent Theory would predict a forward-shifted reading (the attack co-temporal with the later opening, hence after the thinking) via anaphora to the previous sentence's time of opening, paraphrasable as 'When I open the door, a burglar will attack me'. This reading is UNAVAILABLE: embedded past cannot denote a time later than the matrix event. Motivates the §7 ULC."
    judgment := .acceptable
    contrasts := []
    readings := [("past-shifted (attack before thinking)", .acceptable), ("forward-shifted (attack co-temporal with later opening, after thinking)", .ungrammatical)]
    paperFeatures := [] }

def ex8_doubleAccess : Datum :=
  { id := "abusch1997_ex8_doubleAccess"
    source := ⟨"abusch-1997", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed that Mary is pregnant."
    glossedTokens := []
    context := "Double-access (present-under-past). The pregnancy must include BOTH the utterance time and John's believing time. The embedded present cannot have a purely future-shifted reading (despite the future-orientation usually available to present tense). Analyzed in §12 by de re interpretation of the embedded present."
    judgment := .acceptable
    contrasts := []
    readings := [("double-access (pregnancy includes utterance + believing)", .acceptable), ("forward-shifted (pregnancy later than the believing)", .ungrammatical)]
    paperFeatures := [] }

def ex6 : Datum :=
  { id := "abusch1997_ex6"
    source := ⟨"abusch-1997", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John found an ostrich in his apartment yesterday. Just before he opened the door he thought that a burglar would attack him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("forward-shifted (attack after thinking, co-temporal with the opening)", .acceptable)]
    paperFeatures := [("configuration", "would under past"), ("reading", "forward-shifted")] }

def ex27 : Datum :=
  { id := "abusch1997_ex27"
    source := ⟨"abusch-1997", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Last Monday John believed that he was in Paris on Tuesday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("backward-shifted (a previous Tuesday)", .acceptable), ("forward-shifted (the Tuesday after last Monday)", .unacceptable)]
    paperFeatures := [("phenomenon", "upper limit"), ("anaphora", "internal to the attitude")] }

def ex29 : Datum :=
  { id := "abusch1997_ex29"
    source := ⟨"abusch-1997", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed he was in Paris at some time."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("backward-shifted, narrow scope (some time before the believing)", .acceptable), ("forward-shifted, narrow scope", .unacceptable)]
    paperFeatures := [("phenomenon", "upper limit"), ("anaphora", "internal to the attitude")] }

def ex30 : Datum :=
  { id := "abusch1997_ex30"
    source := ⟨"abusch-1997", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue believed that she would marry a man who loved her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("simultaneous (loving at the marrying, after the believing)", .acceptable)]
    paperFeatures := [("phenomenon", "sequence of tense"), ("morphology", "past without precedence")] }

def ex34 : Datum :=
  { id := "abusch1997_ex34"
    source := ⟨"abusch-1997", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John decided a week ago that in ten days at breakfast he would say to his mother that they were having their last meal together."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("simultaneous (meal at the saying, three days after the utterance)", .acceptable)]
    paperFeatures := [("phenomenon", "sequence of tense"), ("morphology", "past without precedence")] }

def ex46a : Datum :=
  { id := "abusch1997_ex46a"
    source := ⟨"abusch-1997", "(46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary believed that John was afraid during the last thunderstorm."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "upper limit"), ("reading", "backward-shifted")] }

def ex46b : Datum :=
  { id := "abusch1997_ex46b"
    source := ⟨"abusch-1997", "(46b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary believed that John was afraid during the next thunderstorm."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("forward-shifted (the thunderstorm after the believing)", .unacceptable)]
    paperFeatures := [("phenomenon", "upper limit"), ("reading", "forward-shifted")] }

def ex47 : Datum :=
  { id := "abusch1997_ex47"
    source := ⟨"abusch-1997", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo will go to Rome on the day of Lea's dissertation. Lia believes that she will go to Rome with him then."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "future-directed acquaintance"), ("source", "Bonomi")] }

def ex53 : Datum :=
  { id := "abusch1997_ex53"
    source := ⟨"abusch-1997", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Five days ago, John promised to talk during a seminar a week later about the topic that the participants were most interested in."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("narrow scope (interest at the seminar, after the utterance)", .acceptable), ("wide scope (a specific topic; interest before the utterance)", .acceptable)]
    paperFeatures := [("phenomenon", "sequence of tense"), ("sensitivity", "logical scope")] }

def ex60 : Datum :=
  { id := "abusch1997_ex60"
    source := ⟨"abusch-1997", "(60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue expects to marry a man she met recently."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("meeting before the marrying (locally licensed)", .acceptable)]
    paperFeatures := [("phenomenon", "local licensing"), ("matrix", "present")] }

def ex63 : Datum :=
  { id := "abusch1997_ex63"
    source := ⟨"abusch-1997", "(63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue expects to marry a man she loved."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("loving before the marrying", .acceptable), ("simultaneous (loving at the marrying)", .unacceptable)]
    paperFeatures := [("phenomenon", "local licensing"), ("matrix", "present")] }

def ex64 : Datum :=
  { id := "abusch1997_ex64"
    source := ⟨"abusch-1997", "(64)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue will marry a man she met recently."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("meeting before the marrying, possibly after the utterance", .acceptable)]
    paperFeatures := [("phenomenon", "local licensing"), ("operator", "will as evaluation-time shifter")] }

def ex69 : Datum :=
  { id := "abusch1997_ex69"
    source := ⟨"abusch-1997", "(69)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said two weeks ago that Mary is pregnant but actually she has just been overeating for the last three months."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "double access"), ("complement", "not true at either time")] }

def ex81 : Datum :=
  { id := "abusch1997_ex81"
    source := ⟨"abusch-1997", "(81)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed that Mary was pregnant."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [("phenomenon", "double access"), ("alternative", "simultaneous past")] }

def all : List Datum := [ex1, ex2, ex3_ULC, ex8_doubleAccess, ex6, ex27, ex29, ex30, ex34, ex46a, ex46b, ex47, ex53, ex60, ex63, ex64, ex69, ex81]

end Abusch1997.Examples
