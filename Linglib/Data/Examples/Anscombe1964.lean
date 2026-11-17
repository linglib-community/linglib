module

public import Linglib.Data.Examples.Schema

/-!
# `Anscombe1964` — typed example data

Auto-generated from `Linglib/Data/Examples/Anscombe1964.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Anscombe1964.Examples`.
-/

@[expose] public section

namespace Anscombe1964.Examples

def i : Datum :=
  { id := "anscombe1964_i"
    source := ⟨"anscombe-1964", "§I (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the Parthenon was there before the Dome of the Rock was there, and the Dome of the Rock was there before St. Peter's was there, then the Parthenon was there before St. Peter's was there."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before"), ("pattern", "transitivity")] }

def ii : Datum :=
  { id := "anscombe1964_ii"
    source := ⟨"anscombe-1964", "§I (ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If St. Peter's was there after the Dome of the Rock was there, and the Dome of the Rock was there after the Parthenon was there, then St. Peter's was there after the Parthenon was there."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "transitivity")] }

def mutual_before : Datum :=
  { id := "anscombe1964_mutual_before"
    source := ⟨"anscombe-1964", "§I"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "St. Peter's was there before the Parthenon was there."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before"), ("pattern", "mutual")] }

def mutual_after : Datum :=
  { id := "anscombe1964_mutual_after"
    source := ⟨"anscombe-1964", "§I"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Parthenon was there after St. Peter's was there."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "mutual")] }

def born : Datum :=
  { id := "anscombe1964_born"
    source := ⟨"anscombe-1964", "§II"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was born after the Parthenon was there; the Parthenon was there after I was born; ergo, I was born after I was born."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "transitivity_failure")] }

def scout : Datum :=
  { id := "anscombe1964_scout"
    source := ⟨"anscombe-1964", "§II"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was a Boy Scout after you were one."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "alternative_verifications")] }

def james1 : Datum :=
  { id := "anscombe1964_james1"
    source := ⟨"anscombe-1964", "§III (1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "James began being ill after John began to be ill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "verification"), ("verification", "begin_after_begin")] }

def james2 : Datum :=
  { id := "anscombe1964_james2"
    source := ⟨"anscombe-1964", "§III (2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "James began being ill after John stopped being ill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "verification"), ("verification", "begin_after_stop")] }

def james3 : Datum :=
  { id := "anscombe1964_james3"
    source := ⟨"anscombe-1964", "§III (3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "James was ill after John began to be ill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "verification"), ("verification", "overlap_after_begin")] }

def james4 : Datum :=
  { id := "anscombe1964_james4"
    source := ⟨"anscombe-1964", "§III (4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "James was ill after John stopped being ill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "verification"), ("verification", "after_stop")] }

def greece : Datum :=
  { id := "anscombe1964_greece"
    source := ⟨"anscombe-1964", "§IV"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A time at which I was in Greece was before every time at which you were in Italy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before"), ("pattern", "quantification")] }

def italy : Datum :=
  { id := "anscombe1964_italy"
    source := ⟨"anscombe-1964", "§IV"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A time at which you were in Italy was after a time at which I was in Greece."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "quantification")] }

def glass : Datum :=
  { id := "anscombe1964_glass"
    source := ⟨"anscombe-1964", "§V"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He studied his appearance in the glass before he used the telephone."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "before"), ("pattern", "before_ever")] }

def battle : Datum :=
  { id := "anscombe1964_battle"
    source := ⟨"anscombe-1964", "§VII"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The battle took place after it rained, and it rained after the battle started."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "mutual")] }

def quarrel : Datum :=
  { id := "anscombe1964_quarrel"
    source := ⟨"anscombe-1964", "§VII"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I left after they quarreled, and they quarreled after I left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "mutual")] }

def report : Datum :=
  { id := "anscombe1964_report"
    source := ⟨"anscombe-1964", "§VII"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I arrived after he was reading the report, and he was reading the report after I arrived."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "mutual")] }

def arrival : Datum :=
  { id := "anscombe1964_arrival"
    source := ⟨"anscombe-1964", "§VII"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her arrival was after their conversation."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "nominal"), ("instantaneous", "yes")] }

def john_tom : Datum :=
  { id := "anscombe1964_john_tom"
    source := ⟨"anscombe-1964", "§IX"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John arrived somewhere after Tom."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "instantaneous"), ("instantaneous", "yes")] }

def all : List Datum := [i, ii, mutual_before, mutual_after, born, scout, james1, james2, james3, james4, greece, italy, glass, battle, quarrel, report, arrival, john_tom]

end Anscombe1964.Examples
